//! Extract a function and its callee closure from a crate into a self-contained [`FnUnit`].

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use proc_macro2::Span;
use quote::ToTokens;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;

use crate::crate_index::{CrateIndex, Kind};
use crate::scalar;
use crate::unit::{macro_args, macro_policy, macro_skip, std_path_skip, FnUnit, MacroPolicy, Skip};

/// Names that resolve without an import.
const PRELUDE: &[&str] = &[
    "Some",
    "None",
    "Ok",
    "Err",
    "Option",
    "Result",
    "Box",
    "Vec",
    "String",
    "drop",
    "Default",
    "Clone",
    "Copy",
    "Into",
    "From",
    "TryFrom",
    "TryInto",
    "Iterator",
    "IntoIterator",
    "ToString",
    "ToOwned",
    "PartialEq",
    "Eq",
    "PartialOrd",
    "Ord",
    "Fn",
    "FnMut",
    "FnOnce",
    "Send",
    "Sync",
    "Sized",
    "Drop",
    "AsRef",
    "AsMut",
    "Extend",
    "FromIterator",
    "DoubleEndedIterator",
    "ExactSizeIterator",
    "char",
    "str",
];

#[derive(Clone, Copy, PartialEq, Eq)]
enum Ns {
    Value,
    Type,
}

enum Res {
    /// A local variable.
    Local,
    /// Outside the crate and allowed; replace the path with this one if given.
    External(Option<syn::Path>),
    /// An entry to include in the closure.
    Item(usize),
    Skip(Skip),
}

/// Extract the function at `entry` and everything it uses.
/// Resolve a function into a self-contained unit (its callee closure) without
/// checking whether it is in scope, so either path can apply its own checks.
pub fn extract_unvalidated(index: &CrateIndex, entry: usize) -> Result<FnUnit, Skip> {
    extract_in(index, entry, false)
}

/// Like [`extract_unvalidated`], but in heap mode: raw pointers are allowed and
/// the crate struct/union/enum types a function uses are pulled into the unit,
/// so the heap generator can build them. Still rejects IO, globals, and
/// unresolved or non-modelled foreign references during resolution; the heap
/// body scope check (`FnUnit::heap_body_in_scope`) applies the rest.
pub fn extract_heap(index: &CrateIndex, entry: usize) -> Result<FnUnit, Skip> {
    extract_in(index, entry, true)
}

fn extract_in(index: &CrateIndex, entry: usize, heap: bool) -> Result<FnUnit, Skip> {
    let resolver = Resolver { index, heap };
    let mut closure = BTreeSet::new();
    let mut queue = VecDeque::from([entry]);
    while let Some(e) = queue.pop_front() {
        if !closure.insert(e) {
            continue;
        }
        let item = index.entries[e]
            .item
            .as_ref()
            .expect("closure entries have items");
        let mut analyzer = Analyzer {
            resolver: &resolver,
            module: index.entries[e].module,
            locals: locals(item, &resolver, index.entries[e].module),
            found: vec![],
            skip: None,
        };
        analyzer.visit_item(item);
        if let Some(skip) = analyzer.skip {
            return Err(skip);
        }
        queue.extend(analyzer.found);
    }

    // Drop closure entries c2rust duplicated identically across files, keeping
    // one per name; a true collision (same name, different definition) is still
    // an error. The function being extracted is always kept.
    let mut names: HashMap<(bool, String), usize> = HashMap::new();
    let mut keep: Vec<usize> = Vec::new();
    for &e in &closure {
        let entry = &index.entries[e];
        let key = (entry.kind == Kind::TypeAlias, entry.name.clone());
        if let Some(&other) = names.get(&key) {
            if same_item(&index.entries[other].item, &entry.item) {
                continue;
            }
            return Err(Skip::new(
                "name collision",
                format!(
                    "`{}` and `{}` have the same name",
                    index.id(other),
                    index.id(e)
                ),
            ));
        }
        names.insert(key, e);
        keep.push(e);
    }

    let mut function = None;
    let mut callees = Vec::new();
    for &e in &keep {
        let mut item = index.entries[e]
            .item
            .clone()
            .expect("closure entries have items");
        let mut rewriter = Rewriter {
            resolver: &resolver,
            module: index.entries[e].module,
            locals: locals(&item, &resolver, index.entries[e].module),
        };
        rewriter.visit_item_mut(&mut item);
        match item {
            syn::Item::Fn(f) if e == entry => function = Some(f),
            item => callees.push(item),
        }
    }
    let unit = FnUnit {
        function: function.expect("the function is in its own closure"),
        callees,
    };
    Ok(unit)
}

/// Resolve a function into a self-contained unit and check it is in scope for
/// the scalar path. The heap path uses [`extract_unvalidated`] and its own
/// scope checks instead.
pub fn extract(index: &CrateIndex, entry: usize) -> Result<FnUnit, Skip> {
    let unit = extract_unvalidated(index, entry)?;
    unit.validate()?;
    Ok(unit)
}

struct Resolver<'a> {
    index: &'a CrateIndex,
    /// In heap mode the resolver pulls crate struct/union/enum types into the
    /// unit (so the generator can build them) instead of rejecting them, and
    /// the analyzer allows raw pointers. The scalar path leaves this off.
    heap: bool,
}

impl Resolver<'_> {
    /// Whether `name` resolves to a crate constant in `module`.
    fn is_const(&self, module: usize, name: &str) -> bool {
        let path = syn::Path::from(ident(name));
        matches!(
            self.resolve(module, &HashSet::new(), &path, Ns::Value),
            Res::Item(e) if self.index.entries[e].kind == Kind::Const
        )
    }

    fn resolve(&self, module: usize, locals: &HashSet<String>, path: &syn::Path, ns: Ns) -> Res {
        let segs = scalar::idents(path);
        let first = segs[0].as_str();
        if path.leading_colon.is_none() {
            if ns == Ns::Value && segs.len() == 1 && locals.contains(first) {
                return Res::Local;
            }
            if let Some(full) = self.index.modules[module].uses.get(first) {
                let mut new_path = full.clone();
                if let (Some(last), Some(seg)) =
                    (new_path.segments.last_mut(), path.segments.first())
                {
                    last.arguments = seg.arguments.clone();
                }
                for seg in path.segments.iter().skip(1) {
                    new_path.segments.push(seg.clone());
                }
                return match self.resolve_inner(module, &new_path, ns) {
                    Res::External(None) => Res::External(Some(new_path)),
                    res => res,
                };
            }
        }
        self.resolve_inner(module, path, ns)
    }

    fn resolve_inner(&self, module: usize, path: &syn::Path, ns: Ns) -> Res {
        let all = scalar::idents(path);
        let shown = all.join("::");
        let first = all[0].as_str();
        if matches!(first, "std" | "core" | "alloc") {
            return match std_path_skip(&all) {
                // The heap path handles `core::ptr::*` (null, offset, ...),
                // which Kani models; keep them rather than rejecting.
                Some(skip) if self.heap && skip.category == "raw pointer" => Res::External(None),
                Some(skip) => Res::Skip(skip),
                None => Res::External(None),
            };
        }
        if first == "libc" {
            return libc(&all, ns);
        }
        if path.leading_colon.is_none()
            && (scalar::primitive(first).is_some() || PRELUDE.contains(&first))
        {
            return Res::External(None);
        }

        let mut segs: &[String] = &all;
        let mut relative = false;
        while let Some(head) = segs.first() {
            if matches!(head.as_str(), "crate" | "self" | "super") {
                relative = true;
                segs = &segs[1..];
            } else {
                break;
            }
        }
        let Some((name, prefix)) = segs.split_last() else {
            return Res::Skip(Skip::new("unresolved", format!("path `{shown}`")));
        };
        let in_ns = |kind: Kind| match ns {
            Ns::Value => matches!(
                kind,
                Kind::Fn | Kind::Const | Kind::Static | Kind::ForeignFn | Kind::ForeignStatic
            ),
            Ns::Type => matches!(kind, Kind::TypeAlias | Kind::Type),
        };
        let index = self.index;
        let mut candidates: Vec<usize> = (0..index.entries.len())
            .filter(|&i| index.entries[i].name == *name && in_ns(index.entries[i].kind))
            .filter(|&i| {
                index.modules[index.entries[i].module]
                    .path
                    .ends_with(prefix)
            })
            .collect();
        if prefix.is_empty() {
            let local: Vec<usize> = candidates
                .iter()
                .copied()
                .filter(|&i| index.entries[i].module == module)
                .collect();
            if !local.is_empty() {
                candidates = local;
            } else if relative {
                candidates.clear();
            }
        }
        if candidates.len() > 1 {
            // A function and a foreign declaration of it in the same module.
            candidates.retain(|&i| index.entries[i].kind != Kind::ForeignFn);
        }
        if candidates.len() > 1 {
            // c2rust emits identical type/const definitions in many files; if
            // every candidate is the same definition, they're interchangeable.
            let first = &index.entries[candidates[0]].item;
            if candidates[1..]
                .iter()
                .all(|&i| same_item(&index.entries[i].item, first))
            {
                candidates.truncate(1);
            }
        }
        match candidates.as_slice() {
            [] => {
                if !prefix.is_empty() {
                    let ty = prefix.last().unwrap();
                    let type_entry = index
                        .entries
                        .iter()
                        .position(|e| e.name == *ty && matches!(e.kind, Kind::Type | Kind::TypeAlias));
                    if let Some(te) = type_entry {
                        // `EnumType::VARIANT` (an associated const): on the heap
                        // path, pull the type in and keep the `Type::const` path;
                        // the scalar path rejects it.
                        if self.heap {
                            return Res::Item(te);
                        }
                        return Res::Skip(Skip::new("crate type", format!("uses `{shown}`")));
                    }
                }
                Res::Skip(Skip::new("unresolved", format!("path `{shown}`")))
            }
            [e] => self.entry(*e, &shown),
            _ => Res::Skip(Skip::new("ambiguous", format!("path `{shown}`"))),
        }
    }

    fn entry(&self, e: usize, shown: &str) -> Res {
        let entry = &self.index.entries[e];
        match entry.kind {
            Kind::Fn | Kind::Const | Kind::TypeAlias => Res::Item(e),
            // libxml2's allocator-indirection globals are modelled on the heap
            // path (given a module-local definition by `allocmodel`); keep the
            // bare path so it resolves to that definition.
            Kind::ForeignStatic if self.heap && crate::allocmodel::is_alloc_global(&entry.name) => {
                Res::External(None)
            }
            // A crate-defined scalar `static mut` with its own initializer is
            // pulled into the unit: both versions get an identical copy with the
            // same starting value, and the harness compares the final values, so
            // a divergent global write is caught. A `static mut` is shared,
            // mutable state, but in isolation it starts from its initializer --
            // a real execution state -- which is sound (if incomplete).
            Kind::Static if self.heap && is_scalar_mut_static(&entry.item) => Res::Item(e),
            Kind::Static | Kind::ForeignStatic => {
                Res::Skip(Skip::new("global", format!("accesses `{shown}`")))
            }
            // On the heap path a crate struct/union/enum is pulled into the
            // unit so the generator can build it; the scalar path rejects it.
            Kind::Type if self.heap => Res::Item(e),
            Kind::Type => Res::Skip(Skip::new("crate type", format!("uses `{shown}`"))),
            Kind::ForeignFn => {
                let symbol = entry.symbol.as_deref().unwrap_or(&entry.name);
                match self.index.defs_by_symbol(symbol).as_slice() {
                    [def] => Res::Item(*def),
                    // On the heap path, a C memory or string function Kani can
                    // model (or `strmodel` defines), and any non-variadic scalar
                    // external modelled as an observable trace call, is pulled in
                    // as its own declaration rather than rejected.
                    [] if self.heap
                        && (crate::unit::is_modelled_c_fn(&entry.name)
                            || crate::strmodel::is_trace_modellable(&entry.item)) =>
                    {
                        Res::Item(e)
                    }
                    // A modelled variadic I/O call (`printf`, …) is kept as a
                    // bare call and rewritten into trace events later; its
                    // (variadic) declaration isn't pulled in.
                    [] if self.heap && crate::varmodel::is_variadic_modelled(&entry.name) => {
                        Res::External(None)
                    }
                    [] => Res::Skip(Skip::new(
                        "foreign call",
                        format!("calls foreign function `{shown}`"),
                    )),
                    _ => Res::Skip(Skip::new(
                        "ambiguous",
                        format!("several definitions of symbol `{symbol}`"),
                    )),
                }
            }
        }
    }
}

/// Whether an item is a scalar `static mut` (a global the heap path can model
/// by giving each version its own identically-initialised copy).
fn is_scalar_mut_static(item: &Option<syn::Item>) -> bool {
    matches!(item, Some(syn::Item::Static(s)) if crate::unit::is_scalar_mut_static(s))
}

/// Whether two stored items are the same definition, by token text. Used to
/// treat c2rust's identical per-file duplicate definitions as one.
fn same_item(a: &Option<syn::Item>, b: &Option<syn::Item>) -> bool {
    use quote::ToTokens;
    match (a, b) {
        (Some(x), Some(y)) => {
            x.to_token_stream().to_string() == y.to_token_stream().to_string()
        }
        (None, None) => true,
        _ => false,
    }
}

fn libc(segs: &[String], ns: Ns) -> Res {
    let shown = segs.join("::");
    let name = segs.last().unwrap();
    if ns == Ns::Type && segs.len() == 2 {
        if scalar::c_type(name).is_some() {
            return Res::External(Some(
                syn::parse_str(&format!("::core::ffi::{name}")).unwrap(),
            ));
        }
        if let Some(prim) = scalar::libc_typedef(name) {
            return Res::External(Some(syn::parse_str(prim).unwrap()));
        }
    }
    Res::Skip(Skip::new("foreign call", format!("uses `{shown}`")))
}

/// An identifier from its string form, which may be raw (`r#box`).
fn ident(name: &str) -> syn::Ident {
    match name.strip_prefix("r#") {
        Some(raw) => syn::Ident::new_raw(raw, Span::call_site()),
        None => syn::Ident::new(name, Span::call_site()),
    }
}

/// Names bound inside an item: arguments, `let`s, closure parameters, nested items.
///
/// A pattern identifier that names a constant in scope is a constant pattern,
/// not a binding, so it isn't a local.
fn locals(item: &syn::Item, resolver: &Resolver, module: usize) -> HashSet<String> {
    struct Locals(HashSet<String>);
    impl<'ast> Visit<'ast> for Locals {
        fn visit_pat_ident(&mut self, p: &'ast syn::PatIdent) {
            self.0.insert(p.ident.to_string());
            syn::visit::visit_pat_ident(self, p);
        }
        fn visit_item_fn(&mut self, f: &'ast syn::ItemFn) {
            self.0.insert(f.sig.ident.to_string());
            syn::visit::visit_item_fn(self, f);
        }
    }
    let mut l = Locals(HashSet::new());
    l.visit_item(item);
    // The item's own name refers to the item, not a local.
    if let syn::Item::Fn(f) = item {
        l.0.remove(&f.sig.ident.to_string());
    }
    l.0.retain(|name| !resolver.is_const(module, name));
    l.0
}

/// Resolves every path in an item and records what it needs.
struct Analyzer<'a> {
    resolver: &'a Resolver<'a>,
    module: usize,
    locals: HashSet<String>,
    found: Vec<usize>,
    skip: Option<Skip>,
}

impl Analyzer<'_> {
    fn path(&mut self, path: &syn::Path, ns: Ns) {
        match self.resolver.resolve(self.module, &self.locals, path, ns) {
            Res::Item(e) => self.found.push(e),
            Res::Skip(skip) => {
                self.skip.get_or_insert(skip);
            }
            Res::Local | Res::External(_) => {}
        }
        for seg in &path.segments {
            self.visit_path_arguments(&seg.arguments);
        }
    }
}

impl<'ast> Visit<'ast> for Analyzer<'_> {
    fn visit_expr_path(&mut self, e: &'ast syn::ExprPath) {
        match &e.qself {
            Some(q) => self.visit_type(&q.ty),
            None => self.path(&e.path, Ns::Value),
        }
    }

    fn visit_type_path(&mut self, t: &'ast syn::TypePath) {
        match &t.qself {
            Some(q) => self.visit_type(&q.ty),
            None => self.path(&t.path, Ns::Type),
        }
    }

    fn visit_expr_struct(&mut self, e: &'ast syn::ExprStruct) {
        self.path(&e.path, Ns::Type);
        for field in &e.fields {
            self.visit_expr(&field.expr);
        }
        if let Some(rest) = &e.rest {
            self.visit_expr(rest);
        }
    }

    fn visit_pat_tuple_struct(&mut self, p: &'ast syn::PatTupleStruct) {
        self.path(&p.path, Ns::Value);
        for elem in &p.elems {
            self.visit_pat(elem);
        }
    }

    fn visit_pat_ident(&mut self, p: &'ast syn::PatIdent) {
        if !self.locals.contains(&p.ident.to_string()) {
            self.path(&p.ident.clone().into(), Ns::Value);
        }
        syn::visit::visit_pat_ident(self, p);
    }

    fn visit_pat_struct(&mut self, p: &'ast syn::PatStruct) {
        self.path(&p.path, Ns::Type);
        for field in &p.fields {
            self.visit_pat(&field.pat);
        }
    }

    fn visit_type_ptr(&mut self, ptr: &'ast syn::TypePtr) {
        // The heap path handles raw pointers; recurse so the pointee type is
        // resolved and pulled into the unit. The scalar path rejects them.
        if self.resolver.heap {
            syn::visit::visit_type_ptr(self, ptr);
        } else {
            self.skip
                .get_or_insert(Skip::new("raw pointer", "uses raw pointers"));
        }
    }

    fn visit_item_static(&mut self, s: &'ast syn::ItemStatic) {
        // A scalar `static mut` is modelled on the heap path (included and
        // compared); visit its initializer for references but don't reject it.
        if self.resolver.heap
            && is_scalar_mut_static(&Some(syn::Item::Static(s.clone())))
        {
            syn::visit::visit_item_static(self, s);
            return;
        }
        self.skip.get_or_insert(Skip::new(
            "global",
            format!("declares static `{}`", s.ident),
        ));
    }

    fn visit_item_foreign_mod(&mut self, m: &'ast syn::ItemForeignMod) {
        // On the heap path, an `extern` block declaring only functions Kani
        // models (or that `strmodel` defines) and the modelled allocator
        // globals is kept; anything else is still out of scope.
        if self.resolver.heap
            && m.items.iter().all(|it| match it {
                syn::ForeignItem::Fn(f) => {
                    crate::unit::is_modelled_c_fn(&f.sig.ident.to_string())
                        || crate::strmodel::is_trace_modellable(&Some(syn::Item::ForeignMod(
                            syn::ItemForeignMod {
                                attrs: vec![],
                                unsafety: None,
                                abi: m.abi.clone(),
                                brace_token: m.brace_token,
                                items: vec![syn::ForeignItem::Fn(f.clone())],
                            },
                        )))
                }
                syn::ForeignItem::Static(s) => {
                    crate::allocmodel::is_alloc_global(&s.ident.to_string())
                }
                _ => false,
            })
        {
            return;
        }
        self.skip
            .get_or_insert(Skip::new("foreign call", "declares foreign items"));
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if let Some(skip) = macro_skip(mac) {
            self.skip.get_or_insert(skip);
        } else if let Ok(args) = macro_args(mac) {
            for arg in &args {
                self.visit_expr(arg);
            }
        }
    }

    // Attributes don't refer to items we need.
    fn visit_attribute(&mut self, _: &'ast syn::Attribute) {}
}

/// Rewrites paths so the item works inside a flat module of the closure's items.
struct Rewriter<'a> {
    resolver: &'a Resolver<'a>,
    module: usize,
    locals: HashSet<String>,
}

impl Rewriter<'_> {
    fn path(&mut self, path: &mut syn::Path, ns: Ns) {
        for seg in &mut path.segments {
            self.visit_path_arguments_mut(&mut seg.arguments);
        }
        match self.resolver.resolve(self.module, &self.locals, path, ns) {
            Res::Item(e) => {
                let entry = &self.resolver.index.entries[e];
                let name = &entry.name;
                // A path resolving to a type but ending in a different segment
                // is an associated const (`EnumType::VARIANT`): rewrite the type
                // prefix to its bare name and keep the final segment.
                let tail = path.segments.last().filter(|s| {
                    matches!(entry.kind, Kind::Type | Kind::TypeAlias) && s.ident != name.as_str()
                });
                let mut new_path = syn::Path::from(ident(name));
                if let Some(tail) = tail {
                    new_path.segments.push(tail.clone());
                } else if let (Some(last), Some(old)) =
                    (new_path.segments.last_mut(), path.segments.last())
                {
                    last.arguments = old.arguments.clone();
                }
                *path = new_path;
            }
            Res::External(Some(new_path)) => *path = new_path,
            Res::External(None) | Res::Local | Res::Skip(_) => {}
        }
    }
}

impl VisitMut for Rewriter<'_> {
    fn visit_expr_path_mut(&mut self, e: &mut syn::ExprPath) {
        match &mut e.qself {
            Some(q) => self.visit_type_mut(&mut q.ty),
            None => self.path(&mut e.path, Ns::Value),
        }
    }

    fn visit_type_path_mut(&mut self, t: &mut syn::TypePath) {
        match &mut t.qself {
            Some(q) => self.visit_type_mut(&mut q.ty),
            None => self.path(&mut t.path, Ns::Type),
        }
    }

    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        if let MacroPolicy::Exprs = macro_policy(mac) {
            if let Ok(mut args) = macro_args(mac) {
                for arg in &mut args {
                    self.visit_expr_mut(arg);
                }
                mac.tokens = args.to_token_stream();
            }
        }
    }
}
