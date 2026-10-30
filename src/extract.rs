//! Extract a function and its callee closure from a crate into a self-contained [`FnUnit`].

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

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
    extract_in(index, entry, false, &BTreeMap::new())
}

/// Like [`extract_unvalidated`], but in heap mode: raw pointers are allowed and
/// the crate struct/union/enum types a function uses are pulled into the unit,
/// so the heap generator can build them. Still rejects IO, globals, and
/// unresolved or non-modelled foreign references during resolution; the heap
/// body scope check (`FnUnit::heap_body_in_scope`) applies the rest.
pub fn extract_heap(index: &CrateIndex, entry: usize) -> Result<FnUnit, Skip> {
    extract_in(index, entry, true, &BTreeMap::new())
}

/// Like [`extract_heap`], but replacing each callee named in `summaries` with
/// its summary shim instead of inlining the callee's body (Subsystem A, phase
/// A3b). A summarised callee's call sites are kept as bare calls, and the
/// referenced shims are appended to the unit's callees. The catalog comes from
/// [`crate::compose::summary_catalog`], which only admits callees whose two
/// versions are equivalent and whose write set is fully havocable, so the
/// substitution is sound.
pub fn extract_heap_composed(
    index: &CrateIndex,
    entry: usize,
    summaries: &BTreeMap<String, syn::ItemFn>,
) -> Result<FnUnit, Skip> {
    extract_in(index, entry, true, summaries)
}

/// Research (not used by the tool): the full set of heap-path extraction
/// blockers a function hits across its whole reachable closure, as `(category,
/// detail)` pairs -- every skip, not just the first, exploring every reachable
/// item without short-circuiting. Drives blocker-set / wall-combination
/// analysis so levers can target the walls whose *joint* removal flips the most
/// functions, rather than one-at-a-time first-blocker guessing.
pub fn all_blockers(
    index: &CrateIndex,
    entry: usize,
    summaries: &BTreeMap<String, syn::ItemFn>,
) -> Vec<(String, String)> {
    let summary_names: BTreeSet<String> = summaries
        .keys()
        .filter(|name| **name != index.entries[entry].name)
        .cloned()
        .collect();
    let aliases = crate::heapgen::alias_table(index);
    let structs = crate::heapgen::data_struct_fields(index);
    let resolver = Resolver {
        index,
        heap: true,
        summaries: &summary_names,
        aliases: &aliases,
        structs: &structs,
    };
    let mut out = Vec::new();
    let mut closure = BTreeSet::new();
    let mut queue = VecDeque::from([entry]);
    while let Some(e) = queue.pop_front() {
        if !closure.insert(e) {
            continue;
        }
        let Some(item) = index.entries[e].item.as_ref() else {
            continue;
        };
        let mut type_env = crate::indirectmodel::TypeEnv::from_index(index);
        if let syn::Item::Fn(f) = item {
            type_env.with_fn(f);
        }
        let rewritten = crate::globalaccessmodel::rewritten(item);
        let analysed = rewritten.as_ref().unwrap_or(item);
        let mut analyzer = Analyzer {
            resolver: &resolver,
            module: index.entries[e].module,
            locals: locals(analysed, &resolver, index.entries[e].module),
            found: vec![],
            skip: None,
            all: vec![],
            type_env,
        };
        analyzer.visit_item(analysed);
        for s in analyzer.all {
            out.push((s.category, s.detail));
        }
        // Keep exploring regardless of blockers, so the whole closure is seen.
        queue.extend(analyzer.found);
    }
    out
}

fn extract_in(
    index: &CrateIndex,
    entry: usize,
    heap: bool,
    summaries: &BTreeMap<String, syn::ItemFn>,
) -> Result<FnUnit, Skip> {
    // Never summarise the function under test itself: it (and its recursive
    // calls) must be analysed in full. Only its callees may be replaced.
    let summary_names: BTreeSet<String> = summaries
        .keys()
        .filter(|name| **name != index.entries[entry].name)
        .cloned()
        .collect();
    // Crate type aliases, so a pointer hidden behind a typedef (c2rust emits
    // many, e.g. `xmlMutexPtr = *mut xmlMutex`) is recognised as a pointer by
    // the eligibility gates below and exposed in the assembled unit.
    let aliases = if heap {
        crate::heapgen::alias_table(index)
    } else {
        BTreeMap::new()
    };
    let structs = if heap {
        crate::heapgen::data_struct_fields(index)
    } else {
        BTreeMap::new()
    };
    let resolver = Resolver {
        index,
        heap,
        summaries: &summary_names,
        aliases: &aliases,
        structs: &structs,
    };
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
        // The variable/field type environment for recognising a modellable
        // indirect call in this item (fields from the whole index, variables
        // from this function's signature and annotated locals).
        let mut type_env = crate::indirectmodel::TypeEnv::from_index(index);
        if let syn::Item::Fn(f) = item {
            type_env.with_fn(f);
        }
        // A thread-local global accessor is analysed as its main-thread branch
        // (`&raw mut X`), not its out-of-scope per-thread indirection, so the
        // global `X` enters the closure and the accessor is in scope. The
        // kept item is rewritten to match when the unit is assembled below.
        let rewritten = if heap {
            crate::globalaccessmodel::rewritten(item)
        } else {
            None
        };
        let analysed = rewritten.as_ref().unwrap_or(item);
        let mut analyzer = Analyzer {
            resolver: &resolver,
            module: index.entries[e].module,
            locals: locals(analysed, &resolver, index.entries[e].module),
            found: vec![],
            skip: None,
            all: vec![],
            type_env,
        };
        analyzer.visit_item(analysed);
        if let Some(skip) = analyzer.skip {
            return Err(skip);
        }
        queue.extend(analyzer.found);
    }

    // Drop closure entries c2rust duplicated identically across files, keeping
    // one per name; a true collision (same name, different definition) is still
    // an error. The function being extracted is always kept.
    // c2rust emits a per-file `extern "C"` redeclaration of each function or
    // data global that is actually defined elsewhere in the crate. When the
    // closure pulls in both the real definition and such a foreign declaration,
    // they share a name but differ -- not a true collision (the declaration
    // merely forward-references the definition), so drop the redundant
    // declaration and keep the definition.
    let real_defs: HashSet<String> = closure
        .iter()
        .filter(|&&e| matches!(index.entries[e].kind, Kind::Fn | Kind::Static | Kind::Const))
        .map(|&e| index.entries[e].name.clone())
        .collect();
    // c2rust emits a per-file `const` for each C macro / enum value, so two
    // files can define the same-named const with *different* values (e.g.
    // `MAX_HASH_LEN` = 8 in dict.rs, 100 in hash.rs). When both land in one
    // closure they are a real clash; module-qualify each (definition and every
    // reference, like the anonymous types) rather than rejecting -- a sound
    // alpha-rename, since c2rust consts are file-local. Only names with 2+
    // distinct definitions in the closure need it.
    let qualify_consts: HashSet<String> = {
        let mut by_name: HashMap<String, HashSet<String>> = HashMap::new();
        for &e in &closure {
            let entry = &index.entries[e];
            if entry.kind == Kind::Const {
                if let Some(item) = &entry.item {
                    by_name
                        .entry(entry.name.clone())
                        .or_default()
                        .insert(item.to_token_stream().to_string());
                }
            }
        }
        by_name
            .into_iter()
            .filter(|(_, defs)| defs.len() > 1)
            .map(|(name, _)| name)
            .collect()
    };
    let mut names: HashMap<(bool, String), usize> = HashMap::new();
    let mut keep: Vec<usize> = Vec::new();
    for &e in &closure {
        let entry = &index.entries[e];
        if matches!(entry.kind, Kind::ForeignFn | Kind::ForeignStatic)
            && real_defs.contains(&entry.name)
        {
            continue;
        }
        // Qualify an anonymous c2rust type (or a clashing per-file const) by its
        // defining module in the dedup key, so two files' distinct definitions
        // are kept side by side (the rewrite renames each to its
        // module-qualified form) rather than reported as a collision.
        let name = if is_anon_c2rust(&entry.name)
            || (entry.kind == Kind::Const && qualify_consts.contains(&entry.name))
        {
            anon_qualified(&entry.name, index.entries[e].module)
        } else {
            entry.name.clone()
        };
        let key = (entry.kind == Kind::TypeAlias, name);
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
            qualify_consts: &qualify_consts,
        };
        rewriter.visit_item_mut(&mut item);
        match item {
            syn::Item::Fn(f) if e == entry => function = Some(f),
            item => callees.push(item),
        }
    }
    let mut function = function.expect("the function is in its own closure");

    // Pull in the inherent `impl` blocks of a kept crate type *only when* one of
    // its associated consts is actually referenced, so a newtype enum's variants
    // (c2rust's `Type::VARIANT` error codes / node-type tags, held in
    // `impl Type { pub const .. }`) resolve in the unit. A referenced variant is
    // a 2+-segment path `Type::VARIANT` in the already-rewritten unit, so collect
    // those base idents and pull impls for just those types -- pulling every kept
    // type's (often large) impl block bloats units and slows extraction badly.
    // Deduped by token text, since c2rust repeats each `impl` per file. Sound:
    // the consts are compile-time scalars, so this is pure scope resolution.
    if heap {
        let mut const_bases: HashSet<String> = HashSet::new();
        struct ConstBases<'a>(&'a mut HashSet<String>);
        impl<'ast> Visit<'ast> for ConstBases<'_> {
            fn visit_path(&mut self, p: &'ast syn::Path) {
                if p.segments.len() >= 2 {
                    self.0.insert(p.segments[0].ident.to_string());
                }
                syn::visit::visit_path(self, p);
            }
        }
        {
            let mut v = ConstBases(&mut const_bases);
            v.visit_item_fn(&function);
            for c in &callees {
                v.visit_item(c);
            }
        }
        let mut seen: HashSet<String> = HashSet::new();
        let kept_types: Vec<String> = keep
            .iter()
            .filter(|&&e| index.entries[e].kind == Kind::Type)
            .map(|&e| index.entries[e].name.clone())
            .filter(|n| const_bases.contains(n))
            .collect();
        for name in kept_types {
            if let Some(impls) = index.impls.get(&name) {
                for im in impls {
                    if seen.insert(im.to_token_stream().to_string()) {
                        callees.push(im.clone());
                    }
                }
            }
        }
    }

    // Expose pointers hidden behind crate typedefs as concrete `*mut`/`*const`
    // in the assembled unit, so the body scope check, the write-guard, and the
    // trace-shim generator all classify them correctly without alias lookup.
    if heap {
        let mut inliner = PtrAliasInliner { aliases: &aliases };
        inliner.visit_item_fn_mut(&mut function);
        for c in &mut callees {
            inliner.visit_item_mut(c);
        }
        // Rewrite thread-local accessors to their main-thread branch, matching
        // the clone analysed during closure building.
        if let Some(g) = crate::globalaccessmodel::accessor_global_fn(&function) {
            function.block = syn::parse_quote!({
                return &raw mut #g;
            });
        }
        crate::globalaccessmodel::rewrite(&mut callees);
        // Reading `xmlLastError` after a report is now in scope: the modelled
        // `__xmlRaiseError` populates its scalar fields with a fresh shared trace
        // value per report (see `crate::errormodel`), so a scalar-field read is
        // position-sensitive and agrees between versions exactly when it follows
        // the same reports. The pointer fields hold the formatted message, which
        // the model doesn't reconstruct (it sets them null), so a unit that
        // observably reads one stays out of scope.
        if crate::globalaccessmodel::reads_lasterror_pointer_field(&function, &callees) {
            return Err(Skip::new(
                "global",
                "reads a pointer field of `xmlLastError` (formatted message not modelled)"
                    .to_owned(),
            ));
        }
    }

    // Write-guard for read-only data globals: a data global is kept only if the
    // unit never writes it, so each version's identical copy is read
    // identically (no final comparison is emitted for it). If the unit does
    // write one, it isn't read-only -- reject rather than risk a silent miss.
    // A modelled struct `static mut` (e.g. `xmlLastError`) is excluded: it is
    // compared by final state, so writing it is in scope, not a violation.
    let data_statics: BTreeSet<String> = callees
        .iter()
        .filter_map(|c| match c {
            syn::Item::Static(s)
                if crate::unit::is_data_static(s, &structs, &aliases)
                    && crate::unit::modelled_struct_mut_static(s, &structs, &aliases)
                        .is_none()
                    // A mutex-pointer global is written only by the init path,
                    // which the mutex model treats as a no-op; exempt it.
                    && !crate::unit::is_mutex_ptr_static(s, &aliases) =>
            {
                Some(s.ident.to_string())
            }
            _ => None,
        })
        .collect();
    if !data_statics.is_empty() {
        let written = written_data_globals(&function, &callees, &data_statics);
        if let Some(g) = written.iter().next() {
            return Err(Skip::new(
                "global",
                format!("writes data global `{g}` (not read-only)"),
            ));
        }
    }

    // Write-guard for fn-ptr `static mut` globals: modelled as a shared symbolic
    // word injected read-only, with no final comparison, so a unit that writes
    // one (e.g. json-c's `json_global_set_string_hash` setting `char_hash_fn`)
    // would store a divergent concrete address undetected -- reject it instead.
    let fnptr_statics: BTreeSet<String> = callees
        .iter()
        .filter_map(|c| match c {
            syn::Item::Static(s) if crate::unit::is_fnptr_mut_static(s, &aliases) => {
                Some(s.ident.to_string())
            }
            _ => None,
        })
        .collect();
    if !fnptr_statics.is_empty() {
        let written = written_data_globals(&function, &callees, &fnptr_statics);
        if let Some(g) = written.iter().next() {
            return Err(Skip::new(
                "global",
                format!("writes fn-ptr global `{g}` (not read-only)"),
            ));
        }
    }

    // Append the summary shim for every summarised callee the unit actually
    // calls. A summarised callee was resolved to a bare `External` call (not
    // inlined, so not in the closure), so its definition must come from the
    // shim instead. Appending only referenced shims keeps the unit free of
    // unused definitions.
    if !summary_names.is_empty() {
        let mut used = BTreeSet::new();
        {
            struct IdentUse<'a>(&'a mut BTreeSet<String>);
            impl<'ast> Visit<'ast> for IdentUse<'_> {
                fn visit_ident(&mut self, i: &'ast syn::Ident) {
                    self.0.insert(i.to_string());
                }
            }
            let mut v = IdentUse(&mut used);
            v.visit_item_fn(&function);
            for c in &callees {
                v.visit_item(c);
            }
        }
        for (name, shim) in summaries {
            if summary_names.contains(name) && used.contains(name) {
                callees.push(syn::Item::Fn(shim.clone()));
            }
        }
    }

    // A union's discriminant may be proven by an accessor outside this unit's
    // closure, so mine the discriminant catalog from the full crate index --
    // but only when the unit actually carries a multi-field union (otherwise it
    // is never consulted), to avoid scanning the whole crate for every function.
    let union_tags = if heap && has_multi_field_union(&callees) {
        index.union_tag_catalog().clone()
    } else {
        Default::default()
    };
    let unit = FnUnit {
        function,
        callees,
        union_tags,
    };
    Ok(unit)
}

/// Whether any item is a union with more than one field -- the only case where
/// the discriminant catalog is needed.
fn has_multi_field_union(items: &[syn::Item]) -> bool {
    items.iter().any(|it| {
        matches!(it, syn::Item::Union(u) if u.fields.named.len() > 1)
    })
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
    /// Callees to replace by a summary shim rather than inline (phase A3b).
    /// A `Kind::Fn` whose name is here resolves to a bare `External` call; the
    /// shim definition is appended to the unit afterwards.
    summaries: &'a BTreeSet<String>,
    /// Crate type aliases, for seeing through a typedef to a pointer/scalar
    /// when classifying a foreign-call signature or a static's type.
    aliases: &'a BTreeMap<String, syn::Type>,
    /// Crate struct layouts (by name), for recognising a read-only data global
    /// of a struct-of-scalars type (`static G: xmlChRangeGroup`).
    structs: &'a BTreeMap<String, Vec<syn::Type>>,
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
                // A reference naming a crate type in value position, with no
                // top-level item of that name: either `EnumType::VARIANT` (an
                // associated const, `ty` = the prefix) or a bare tuple-struct /
                // newtype used as its constructor or a value, `xmlParserErrors(..)`
                // (`ty` = the name itself). On the heap path pull the type in and
                // keep the path; its inherent `impl` blocks (carrying the enum's
                // associated consts) come along in the unit assembly. The scalar
                // path rejects it.
                let ty = prefix.last().map(String::as_str).unwrap_or(name.as_str());
                let type_entry = index
                    .entries
                    .iter()
                    .position(|e| e.name == *ty && matches!(e.kind, Kind::Type | Kind::TypeAlias));
                if let Some(te) = type_entry {
                    if self.heap {
                        return Res::Item(te);
                    }
                    return Res::Skip(Skip::new("crate type", format!("uses `{shown}`")));
                }
                Res::Skip(Skip::new("unresolved", format!("path `{shown}`")))
            }
            [e] => self.entry(*e, &shown),
            _ => Res::Skip(Skip::new("ambiguous", format!("path `{shown}`"))),
        }
    }

    /// A crate `static` definition of `name` that the heap path can model (a
    /// scalar `static mut` or a data global), for resolving an `extern`
    /// reference to its in-crate definition. `None` if there is no such def.
    fn static_def(&self, name: &str) -> Option<usize> {
        (0..self.index.entries.len()).find(|&i| {
            let en = &self.index.entries[i];
            en.kind == Kind::Static
                && en.name == name
                && (is_scalar_mut_static(&en.item)
                    || self.is_data_static_item(&en.item)
                    || self.is_fnptr_mut_static_item(&en.item))
        })
    }

    /// Whether a static item is a modellable data global, seeing through crate
    /// type aliases (so `static X: SomePtrTypedef` is recognised as a pointer).
    fn is_modelled_struct_mut_static_item(&self, item: &Option<syn::Item>) -> bool {
        matches!(item, Some(syn::Item::Static(s))
            if crate::unit::modelled_struct_mut_static(s, self.structs, self.aliases).is_some())
    }

    fn is_data_static_item(&self, item: &Option<syn::Item>) -> bool {
        let Some(syn::Item::Static(s)) = item else {
            return false;
        };
        if crate::unit::is_scalar_mut_static(s) {
            return false;
        }
        crate::unit::is_data_type(
            &inline_ptr_aliases(&s.ty, self.aliases),
            self.structs,
            self.aliases,
        )
    }

    fn is_fnptr_mut_static_item(&self, item: &Option<syn::Item>) -> bool {
        matches!(item, Some(syn::Item::Static(s))
            if crate::unit::is_fnptr_mut_static(s, self.aliases))
    }

    /// Whether a foreign function can be modelled as an observable trace call,
    /// seeing through crate type aliases on its argument and return types.
    fn is_trace_modellable_item(&self, item: &Option<syn::Item>) -> bool {
        let Some(syn::Item::ForeignMod(m)) = item else {
            return false;
        };
        let mut m = m.clone();
        PtrAliasInliner { aliases: self.aliases }.visit_item_foreign_mod_mut(&mut m);
        crate::strmodel::is_trace_modellable(&Some(syn::Item::ForeignMod(m)))
    }

    fn entry(&self, e: usize, shown: &str) -> Res {
        let entry = &self.index.entries[e];
        match entry.kind {
            // A summarised callee: keep the bare call and don't inline its
            // body; its shim is appended to the unit afterwards.
            Kind::Fn if self.summaries.contains(&entry.name) => Res::External(None),
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
            // A read-only data global (lookup table / string constant) is
            // pulled in too; the final write-guard in `extract_in` rejects the
            // unit if any function actually writes it (then it isn't read-only).
            Kind::Static if self.heap && self.is_data_static_item(&entry.item) => Res::Item(e),
            // A modelled struct `static mut` (e.g. `xmlLastError`): pulled in and
            // compared by final state field-by-field, so writing it is in scope.
            Kind::Static if self.heap && self.is_modelled_struct_mut_static_item(&entry.item) => {
                Res::Item(e)
            }
            // A `static mut` holding a nullable function pointer: pulled in and
            // modelled as a shared symbolic word injected into both versions
            // (see `unit::is_fnptr_mut_static`). The write-guard rejects the
            // unit if any function writes it.
            Kind::Static if self.heap && self.is_fnptr_mut_static_item(&entry.item) => Res::Item(e),
            // A reference through an `extern` declaration (c2rust emits one per
            // file) resolves to the crate definition of the same name when that
            // definition is a modellable global, so the data-global and
            // scalar-`static mut` cases above apply to cross-file accesses too.
            Kind::ForeignStatic if self.heap => {
                match self.static_def(&entry.name) {
                    Some(def) => self.entry(def, shown),
                    None => Res::Skip(Skip::new("global", format!("accesses `{shown}`"))),
                }
            }
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
                            || self.is_trace_modellable_item(&entry.item)) =>
                    {
                        Res::Item(e)
                    }
                    // A modelled variadic I/O call (`printf`, …) or the error
                    // primitive `__xmlRaiseError` is kept as a bare call and
                    // rewritten into trace events later; its (variadic)
                    // declaration isn't pulled in.
                    [] if self.heap
                        && (crate::varmodel::is_variadic_modelled(&entry.name)
                            || crate::errormodel::is_error_fn(&entry.name)) =>
                    {
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

/// Resolve `ty` through crate type aliases and, if it stands for a pointer,
/// return that pointer type; otherwise return `ty` unchanged. Only pointer
/// aliases are inlined -- scalar typedefs are already classified elsewhere --
/// so the common `*Typedef` hidden behind a name becomes a visible `*mut T`.
fn inline_ptr_aliases(ty: &syn::Type, aliases: &BTreeMap<String, syn::Type>) -> syn::Type {
    let resolved = crate::heapgen::resolve_alias(ty, aliases);
    if matches!(resolved, syn::Type::Ptr(_)) {
        resolved
    } else {
        ty.clone()
    }
}

/// Rewrites every type that stands (through aliases) for a pointer into that
/// pointer type, so downstream consumers (trace shims, body scope check,
/// write-guard) see a concrete `*mut`/`*const` rather than an opaque typedef.
struct PtrAliasInliner<'a> {
    aliases: &'a BTreeMap<String, syn::Type>,
}

impl VisitMut for PtrAliasInliner<'_> {
    fn visit_type_mut(&mut self, ty: &mut syn::Type) {
        let inlined = inline_ptr_aliases(ty, self.aliases);
        if &inlined != ty {
            *ty = inlined;
        }
        syn::visit_mut::visit_type_mut(self, ty);
    }
}

/// Names of data globals that `items` write (assign, take a `&mut`/`*mut` of,
/// or `addr_of_mut!`). A data global absent here is read-only across the unit,
/// so each version's identical copy is read identically -- sound without a
/// final comparison. Any path to mutating a global must first name it on an
/// assignment's left side or take its mutable address, so this is a sound
/// over-approximation of "written".
fn written_data_globals(
    function: &syn::ItemFn,
    callees: &[syn::Item],
    names: &BTreeSet<String>,
) -> BTreeSet<String> {
    struct Finder<'a> {
        names: &'a BTreeSet<String>,
        hit: BTreeSet<String>,
    }
    impl Finder<'_> {
        fn mark(&mut self, e: &syn::Expr) {
            if let Some(n) = base_name(e) {
                if self.names.contains(&n) {
                    self.hit.insert(n);
                }
            }
        }
    }
    impl<'ast> Visit<'ast> for Finder<'_> {
        fn visit_expr_assign(&mut self, a: &'ast syn::ExprAssign) {
            self.mark(&a.left);
            syn::visit::visit_expr_assign(self, a);
        }
        fn visit_expr_reference(&mut self, r: &'ast syn::ExprReference) {
            if r.mutability.is_some() {
                self.mark(&r.expr);
            }
            syn::visit::visit_expr_reference(self, r);
        }
        fn visit_expr_cast(&mut self, c: &'ast syn::ExprCast) {
            if matches!(&*c.ty, syn::Type::Ptr(p) if p.mutability.is_some()) {
                self.mark(&c.expr);
            }
            syn::visit::visit_expr_cast(self, c);
        }
        fn visit_macro(&mut self, m: &'ast syn::Macro) {
            // `addr_of_mut!(X)` (bare or `core::ptr::addr_of_mut!`) takes a
            // writable address of its argument -- treat it as a write.
            if m.path.segments.last().is_some_and(|s| s.ident == "addr_of_mut") {
                if let Ok(e) = m.parse_body::<syn::Expr>() {
                    self.mark(&e);
                }
            }
            syn::visit::visit_macro(self, m);
        }
    }
    let mut f = Finder {
        names,
        hit: BTreeSet::new(),
    };
    f.visit_item_fn(function);
    for c in callees {
        f.visit_item(c);
    }
    f.hit
}

/// The root global name a place expression refers to, following field, index,
/// deref, reference, cast and paren wrappers down to a leading path identifier.
fn base_name(e: &syn::Expr) -> Option<String> {
    match e {
        syn::Expr::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
        syn::Expr::Field(f) => base_name(&f.base),
        syn::Expr::Index(i) => base_name(&i.expr),
        syn::Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => base_name(&u.expr),
        syn::Expr::Paren(p) => base_name(&p.expr),
        syn::Expr::Reference(r) => base_name(&r.expr),
        syn::Expr::Cast(c) => base_name(&c.expr),
        _ => None,
    }
}

/// Whether two stored items are the same definition, by token text. Used to
/// treat c2rust's identical per-file duplicate definitions as one.
/// c2rust names every anonymous C aggregate `C2Rust_Unnamed` (with a per-file
/// `_N` suffix), so two different files' anonymous types share a name. Each is
/// only ever referenced within its own file, so qualifying it by its defining
/// module -- the definition's ident and every reference alike -- is a sound
/// alpha-rename that lets one closure hold several of them without collision.
fn is_anon_c2rust(name: &str) -> bool {
    name.starts_with("C2Rust_Unnamed") || name.starts_with("C2RustUnnamed")
}

fn anon_qualified(name: &str, module: usize) -> String {
    format!("{name}_m{module}")
}

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
        fn visit_item_static(&mut self, s: &'ast syn::ItemStatic) {
            // A function-local `static` (c2rust's lowering of a C function-static
            // variable, e.g. genann's lazily-built sigmoid `lookup` table) is a
            // real, in-scope item in the body; its name is not an out-of-scope
            // path. It is emitted verbatim in the scratch, so a reference to it
            // resolves locally. Sound for differential equivalence: both versions
            // hold their own copy from the same initializer and the harness calls
            // each once, so a lazily-initialised static is built identically.
            self.0.insert(s.ident.to_string());
            syn::visit::visit_item_static(self, s);
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
    /// Every skip seen (not just the first), for research-mode blocker-set
    /// analysis; the real extraction only reads `skip`.
    all: Vec<Skip>,
    /// Struct-field and current-function variable types, so a modellable
    /// indirect (function-pointer) call can be recognised and admitted.
    type_env: crate::indirectmodel::TypeEnv,
}

impl Analyzer<'_> {
    /// Record a skip: keep the first in `skip` (the real extraction's verdict)
    /// and append every one to `all` (research-mode blocker-set analysis).
    fn note(&mut self, s: Skip) {
        self.all.push(s.clone());
        self.skip.get_or_insert(s);
    }

    fn path(&mut self, path: &syn::Path, ns: Ns) {
        match self.resolver.resolve(self.module, &self.locals, path, ns) {
            Res::Item(e) => self.found.push(e),
            Res::Skip(skip) => {
                self.note(skip);
            }
            Res::Local | Res::External(_) => {}
        }
        for seg in &path.segments {
            self.visit_path_arguments(&seg.arguments);
        }
    }
}

impl<'ast> Visit<'ast> for Analyzer<'_> {
    fn visit_expr_call(&mut self, c: &'ast syn::ExprCall) {
        // A lock/unlock wrapper call is a sequential no-op (dropped at harness
        // generation); admit it without resolving the wrapper's body or its
        // global mutex argument (which would otherwise trip the foreign-call and
        // global walls). See `crate::mutexmodel`.
        if self.resolver.heap && crate::mutexmodel::is_mutex_call(c) {
            return;
        }
        // A thread-local handler accessor `__xmlGenericError()` etc. is erased by
        // the scratch rewrite (the dispatch through it becomes an observable
        // trace call keyed by the handler name; see `crate::errormodel`), so
        // skip-descend it: the accessor and its out-of-scope fn-pointer global
        // never enter the unit. Catches the accessor wherever it appears -- the
        // dispatch receiver and the `.is_some()`/`.is_none()` guards alike.
        if self.resolver.heap && crate::errormodel::is_handler_accessor_call(c) {
            return;
        }
        // An indirect call -- through a function pointer held in a local (c2rust
        // emits `if let Some(cb) = (*x).field { cb(..) }`) or any non-path callee
        // -- targets a symbolic address on the heap path and can't be modelled
        // soundly, so it is out of scope. This guards the opaque fn-ptr-field
        // model: such a pointer may be carried, never invoked. A direct call
        // names a crate/external function by path.
        if self.resolver.heap {
            let indirect = match &*c.func {
                syn::Expr::Path(p) if p.qself.is_none() => matches!(
                    self.resolver
                        .resolve(self.module, &self.locals, &p.path, Ns::Value),
                    Res::Local
                ),
                _ => true,
            };
            // A function-pointer call c2rust emits as `field.expect("..")(args)`
            // is modelled as an observable/uninterpreted trace call keyed by the
            // callback value (see `crate::indirectmodel`), so it is admitted
            // when its shape fits. Any other indirect call is still out of scope.
            if indirect
                && !self.type_env.indirect_is_modellable(c)
                && !crate::allocmodel::is_alloc_hook_call(c)
                && !crate::errormodel::is_handler_dispatch(c)
            {
                self.note(Skip::new(
                    "indirect call",
                    format!(
                        "calls through a function pointer: {}",
                        quote::ToTokens::to_token_stream(&*c.func).to_string()
                    ),
                ));
            }
        }
        syn::visit::visit_expr_call(self, c);
    }

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
        // A scalar `static mut` (modelled and compared) or a read-only data
        // global is kept on the heap path; visit its initializer for references
        // but don't reject it. A written data global is caught by the
        // write-guard in `extract_in`, not here.
        if self.resolver.heap
            && (is_scalar_mut_static(&Some(syn::Item::Static(s.clone())))
                || self
                    .resolver
                    .is_data_static_item(&Some(syn::Item::Static(s.clone())))
                || self
                    .resolver
                    .is_fnptr_mut_static_item(&Some(syn::Item::Static(s.clone()))))
        {
            syn::visit::visit_item_static(self, s);
            return;
        }
        self.note(Skip::new(
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
                        || self.resolver.is_trace_modellable_item(&Some(syn::Item::ForeignMod(
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
            self.note(skip);
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
    /// Per-file consts that clash across the closure (same name, different
    /// value); each is renamed to its module-qualified form, definition and
    /// references alike.
    qualify_consts: &'a HashSet<String>,
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
                // An anonymous c2rust type -- or a clashing per-file const -- is
                // renamed to its module-qualified form, matching the rename of
                // its definition's ident below.
                let qualified;
                let name: &str = if is_anon_c2rust(name)
                    || (entry.kind == Kind::Const && self.qualify_consts.contains(name))
                {
                    qualified = anon_qualified(name, entry.module);
                    &qualified
                } else {
                    name
                };
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

    // Rename an anonymous c2rust type's *definition* ident to its
    // module-qualified form, so it matches the references rewritten in `path`
    // (its fields' types are rewritten by the descent).
    fn visit_item_struct_mut(&mut self, s: &mut syn::ItemStruct) {
        if is_anon_c2rust(&s.ident.to_string()) {
            s.ident = ident(&anon_qualified(&s.ident.to_string(), self.module));
        }
        syn::visit_mut::visit_item_struct_mut(self, s);
    }

    fn visit_item_union_mut(&mut self, u: &mut syn::ItemUnion) {
        if is_anon_c2rust(&u.ident.to_string()) {
            u.ident = ident(&anon_qualified(&u.ident.to_string(), self.module));
        }
        syn::visit_mut::visit_item_union_mut(self, u);
    }

    fn visit_item_enum_mut(&mut self, en: &mut syn::ItemEnum) {
        if is_anon_c2rust(&en.ident.to_string()) {
            en.ident = ident(&anon_qualified(&en.ident.to_string(), self.module));
        }
        syn::visit_mut::visit_item_enum_mut(self, en);
    }

    // Rename a clashing per-file const's *definition* ident to its
    // module-qualified form, matching the references rewritten in `path`.
    fn visit_item_const_mut(&mut self, c: &mut syn::ItemConst) {
        if self.qualify_consts.contains(&c.ident.to_string()) {
            c.ident = ident(&anon_qualified(&c.ident.to_string(), self.module));
        }
        syn::visit_mut::visit_item_const_mut(self, c);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compose::summary_catalog;
    use crate::crate_index::CrateIndex;

    fn index(src: &str) -> CrateIndex {
        let mut i = CrateIndex::default();
        i.add_source("lib.rs", src).unwrap();
        i
    }

    fn callees_src(unit: &FnUnit) -> String {
        unit.callees
            .iter()
            .map(|c| c.to_token_stream().to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }

    // A3b: a summarisable, unchanged callee is replaced by its summary shim --
    // which records on the shared TRACE and havocs the out-pointer -- instead
    // of having its body (`*p = v`) inlined into the caller's closure.
    #[test]
    fn summarised_callee_is_replaced_by_its_shim() {
        let src = "pub unsafe fn helper(p: *mut i32, v: i32) { *p = v; }\n\
                   pub unsafe fn caller(p: *mut i32) { helper(p, 3i32); }";
        let idx = index(src);
        let cat = summary_catalog(&idx, &idx);
        assert!(cat.contains_key("helper"));
        let e = idx.find_functions("caller")[0];
        let unit = extract_heap_composed(&idx, e, &cat).unwrap();
        let callees = callees_src(&unit);
        assert!(callees.contains("TRACE"), "shim appended: {callees}");
        // The original deterministic body must NOT be inlined.
        assert!(
            !callees.contains("* p = v"),
            "callee body not inlined: {callees}"
        );
    }

    // Without a catalog, the same callee is inlined as before (its body is a
    // kept callee, no TRACE shim) -- the summarisation is opt-in.
    #[test]
    fn without_catalog_callee_is_inlined() {
        let src = "pub unsafe fn helper(p: *mut i32, v: i32) { *p = v; }\n\
                   pub unsafe fn caller(p: *mut i32) { helper(p, 3i32); }";
        let idx = index(src);
        let e = idx.find_functions("caller")[0];
        let unit = extract_heap(&idx, e).unwrap();
        let callees = callees_src(&unit);
        assert!(callees.contains("* p = v"), "body inlined: {callees}");
    }

    // The function under test is never summarised, even if it is itself in the
    // catalog: a self/recursive call keeps the real body.
    #[test]
    fn entry_function_is_never_summarised() {
        let src = "pub unsafe fn helper(p: *mut i32, v: i32) { *p = v; }";
        let idx = index(src);
        let cat = summary_catalog(&idx, &idx);
        assert!(cat.contains_key("helper"));
        let e = idx.find_functions("helper")[0];
        let unit = extract_heap_composed(&idx, e, &cat).unwrap();
        // `helper` is the entry; its body stays, and no shim is appended.
        assert!(unit.function.to_token_stream().to_string().contains("* p = v"));
        assert!(!callees_src(&unit).contains("TRACE"));
    }

    // Data globals: a read-only lookup table is pulled into the unit, so each
    // version gets an identical copy and reads it identically (sound).
    #[test]
    fn read_only_data_global_is_pulled_in() {
        let src = "static mut TBL: [i32; 3] = [1i32, 2i32, 3i32];\n\
                   pub unsafe fn f(p: *mut i32) { *p = TBL[1]; }";
        let idx = index(src);
        let e = idx.find_functions("f")[0];
        let unit = extract_heap(&idx, e).unwrap();
        assert!(callees_src(&unit).contains("static mut TBL"), "table pulled in");
    }

    // A data global the unit *writes* is not read-only: no final comparison is
    // emitted for it, so keeping it would risk a silent divergence -- reject.
    #[test]
    fn written_data_global_is_rejected() {
        let src = "static mut TBL: [i32; 3] = [1i32, 2i32, 3i32];\n\
                   pub unsafe fn f(p: *mut i32) { TBL[0] = *p; }";
        let idx = index(src);
        let e = idx.find_functions("f")[0];
        let skip = extract_heap(&idx, e).unwrap_err();
        assert_eq!(skip.category, "global", "{skip:?}");
    }

    // Taking a mutable reference to a data global also counts as a write (the
    // alias could be written through), so it is rejected too.
    #[test]
    fn mut_ref_to_data_global_is_rejected() {
        let src = "static mut TBL: [i32; 3] = [0i32; 3];\n\
                   pub unsafe fn f(p: *mut i32) { let r = &mut TBL; r[0] = *p; }";
        let idx = index(src);
        let e = idx.find_functions("f")[0];
        assert_eq!(extract_heap(&idx, e).unwrap_err().category, "global");
    }

    // An indirect call through a function pointer read into a local (the shape
    // c2rust emits for a nullable callback) is rejected during extraction,
    // where the local is known -- so the opaque fn-ptr-field model stays sound.
    #[test]
    fn indirect_call_through_local_fn_ptr_is_rejected() {
        let src = "pub struct S { pub cb: Option<unsafe extern \"C\" fn(*mut S)> }\n\
                   pub unsafe fn f(s: *mut S) { if let Some(cb) = (*s).cb { cb(s); } }";
        let idx = index(src);
        let e = idx.find_functions("f")[0];
        let skip = extract_heap(&idx, e).unwrap_err();
        assert_eq!(skip.category, "indirect call", "{skip:?}");
    }

    // A pointer hidden behind a crate typedef (c2rust emits these everywhere)
    // is recognised as a data global and exposed as a concrete `*mut` in the
    // unit, not rejected as an opaque global.
    #[test]
    fn pointer_typedef_global_is_recognized() {
        let src = "pub type Handle = *mut i32;\n\
                   static mut TBL: Handle = core::ptr::null_mut();\n\
                   pub unsafe fn f(p: *mut i32) { *p = if TBL.is_null() { 0i32 } else { 1i32 }; }";
        let idx = index(src);
        let e = idx.find_functions("f")[0];
        let unit = extract_heap(&idx, e).unwrap();
        let callees = callees_src(&unit);
        assert!(callees.contains("static mut TBL"), "typedef'd ptr global kept: {callees}");
        // The alias is inlined to a concrete pointer in the unit.
        assert!(callees.contains("* mut i32"), "alias inlined to pointer: {callees}");
    }

    // c2rust duplicates the same `type` alias in every file; identical copies
    // must not be treated as ambiguous (which would defeat alias resolution).
    #[test]
    fn duplicate_identical_typedef_still_resolves() {
        let mut idx = CrateIndex::default();
        idx.add_source("a.rs", "pub type Handle = *mut i32;\n\
                                static mut TBL: Handle = core::ptr::null_mut();")
            .unwrap();
        idx.add_source("b.rs", "pub type Handle = *mut i32;\n\
                                pub unsafe fn g(p: *mut i32) { *p = (!TBL.is_null()) as i32; }")
            .unwrap();
        let e = idx.find_functions("g")[0];
        let unit = extract_heap(&idx, e).unwrap();
        assert!(callees_src(&unit).contains("static mut TBL"));
    }

    // A cross-file access goes through an `extern` declaration (c2rust emits
    // one per file); it must resolve to the crate definition so the data-global
    // model applies, not be rejected as an opaque foreign static.
    #[test]
    fn extern_ref_to_data_global_resolves_to_definition() {
        let mut idx = CrateIndex::default();
        idx.add_source("a.rs", "static mut TBL: [i32; 3] = [1i32, 2i32, 3i32];")
            .unwrap();
        idx.add_source(
            "b.rs",
            "extern \"C\" { static mut TBL: [i32; 3]; }\n\
             pub unsafe fn g(p: *mut i32) { *p = TBL[2]; }",
        )
        .unwrap();
        let e = idx.find_functions("g")[0];
        let unit = extract_heap(&idx, e).unwrap();
        assert!(
            callees_src(&unit).contains("static mut TBL"),
            "definition pulled in across files"
        );
    }
}
