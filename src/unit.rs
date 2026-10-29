//! A function together with the items it needs, independent of any crate.

use std::collections::BTreeMap;
use std::fmt;

use quote::ToTokens;
use serde::{Deserialize, Serialize};
use syn::visit::Visit;

use crate::scalar::{self, ScalarKind};

/// Arguments beyond this many aren't supported.
pub const MAX_ARGS: usize = 8;

/// A function and its callee closure: every function, constant and type alias it uses,
/// directly or through other callees.
///
/// The items must be self-contained: paths to other items in the unit are bare
/// identifiers, and everything else is a path into `core`, `std` or `alloc`.
#[derive(Clone, Debug)]
pub struct FnUnit {
    pub function: syn::ItemFn,
    pub callees: Vec<syn::Item>,
    /// Crate-wide union discriminant maps (keyed by union-field name), mined
    /// from the full crate index at extraction time. A self-contained unit's
    /// own index may lack the accessor that proves a discriminant, so the heap
    /// generator consults this catalog; empty when built outside extraction.
    pub union_tags: std::collections::BTreeMap<String, crate::taggedunion::TagMap>,
}

/// Why a function wasn't checked.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Skip {
    /// A short, fixed label for grouping, e.g. `global`.
    pub category: String,
    pub detail: String,
}

impl Skip {
    pub fn new(category: &str, detail: impl Into<String>) -> Self {
        Self {
            category: category.to_owned(),
            detail: detail.into(),
        }
    }
}

impl fmt::Display for Skip {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.category, self.detail)
    }
}

/// The scalar kinds of a function's arguments and return value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub args: Vec<ScalarKind>,
    pub ret: ScalarKind,
}

impl Signature {
    pub fn uses_floats(&self) -> bool {
        self.args
            .iter()
            .chain([&self.ret])
            .any(|&k| k == ScalarKind::Float)
    }
}

impl FnUnit {
    /// Parse a unit from source text.
    pub fn parse(function: &str, callees: &[&str]) -> syn::Result<Self> {
        Ok(Self {
            function: syn::parse_str(function)?,
            callees: callees
                .iter()
                .map(|s| syn::parse_str(s))
                .collect::<syn::Result<_>>()?,
            union_tags: Default::default(),
        })
    }

    pub fn name(&self) -> String {
        self.function.sig.ident.to_string()
    }

    /// The callees followed by the function.
    pub fn items(&self) -> Vec<syn::Item> {
        let mut items = self.callees.clone();
        items.push(syn::Item::Fn(self.function.clone()));
        items
    }

    /// Formatted source of [`Self::items`].
    pub fn source(&self) -> String {
        prettyplease::unparse(&syn::File {
            shebang: None,
            attrs: vec![],
            items: self.items(),
        })
    }

    /// Check that the unit is in scope for this version, and return its signature.
    pub fn validate(&self) -> Result<Signature, Skip> {
        let sig = self.signature()?;
        self.body_in_scope(false)?;
        Ok(sig)
    }

    /// Check the body for the heap path: raw pointers are allowed (the heap
    /// path builds and compares them), but IO, globals, foreign calls and
    /// unsupported macros still put the function out of scope.
    pub fn heap_body_in_scope(&self) -> Result<(), Skip> {
        self.body_in_scope(true)
    }

    fn body_in_scope(&self, allow_pointers: bool) -> Result<(), Skip> {
        let items = self.items();
        let mut checker = BodyChecker {
            skip: None,
            allow_pointers,
            // Field types come from every struct in the unit; variable types are
            // filled in per function as the checker descends (see visit_item_fn).
            type_env: crate::indirectmodel::TypeEnv::from_items(&items),
            // Struct layouts and type aliases, so a read-only data global of a
            // struct-of-scalars type (`static G: xmlChRangeGroup`) is recognised
            // as in scope -- the same gate the extractor used to pull it in.
            structs: crate::heapgen::data_struct_fields_from_items(&items),
            aliases: crate::heapgen::alias_table_from_items(&items),
        };
        for item in &items {
            // A generated summary shim is trusted code that only runs in the
            // scratch template (it uses the trace support there); its body is
            // not source under test, so it is exempt from the scope check.
            if crate::summary::is_summary_shim(item) {
                continue;
            }
            checker.visit_item(item);
        }
        match checker.skip {
            Some(skip) => Err(skip),
            None => Ok(()),
        }
    }

    /// The function's signature, if every argument and the return value are scalars.
    pub fn signature(&self) -> Result<Signature, Skip> {
        let sig = &self.function.sig;
        if !sig.generics.params.is_empty() {
            return Err(Skip::new("signature", "generic function"));
        }
        if sig.asyncness.is_some() {
            return Err(Skip::new("signature", "async function"));
        }
        if sig.variadic.is_some() {
            return Err(Skip::new("signature", "variadic function"));
        }
        if sig.inputs.len() > MAX_ARGS {
            return Err(Skip::new(
                "signature",
                format!("more than {MAX_ARGS} arguments"),
            ));
        }
        let mut args = Vec::new();
        for input in &sig.inputs {
            let syn::FnArg::Typed(pat_ty) = input else {
                return Err(Skip::new("signature", "method with a receiver"));
            };
            if !matches!(&*pat_ty.pat, syn::Pat::Ident(_) | syn::Pat::Wild(_)) {
                return Err(Skip::new(
                    "signature",
                    "argument with a destructuring pattern",
                ));
            }
            match self.kind_of(&pat_ty.ty, 0) {
                Some(ScalarKind::Unit) | None => {
                    return Err(Skip::new(
                        "signature",
                        format!(
                            "argument `{}` has non-scalar type `{}`",
                            pat_ty.pat.to_token_stream(),
                            pat_ty.ty.to_token_stream()
                        ),
                    ))
                }
                Some(kind) => args.push(kind),
            }
        }
        let ret = match &sig.output {
            syn::ReturnType::Default => ScalarKind::Unit,
            syn::ReturnType::Type(_, ty) => self.kind_of(ty, 0).ok_or_else(|| {
                Skip::new(
                    "signature",
                    format!("non-scalar return type `{}`", ty.to_token_stream()),
                )
            })?,
        };
        Ok(Signature { args, ret })
    }

    /// Whether the function might do floating-point arithmetic.
    pub fn uses_floats(&self) -> bool {
        let mut finder = FloatFinder { found: false };
        for item in self.items() {
            finder.visit_item(&item);
        }
        finder.found
    }

    /// The scalar kind of `ty`, following type aliases among the callees.
    fn kind_of(&self, ty: &syn::Type, depth: usize) -> Option<ScalarKind> {
        if depth > 16 {
            return None;
        }
        match ty {
            syn::Type::Paren(p) => self.kind_of(&p.elem, depth),
            syn::Type::Group(g) => self.kind_of(&g.elem, depth),
            syn::Type::Tuple(t) if t.elems.is_empty() => Some(ScalarKind::Unit),
            syn::Type::Path(p) if p.qself.is_none() => {
                let segs = scalar::idents(&p.path);
                let (last, prefix) = segs.split_last()?;
                if prefix.is_empty() {
                    if let Some(kind) = scalar::primitive(last) {
                        return Some(kind);
                    }
                    if let Some(alias) = self.alias(last) {
                        return self.kind_of(&alias.ty, depth + 1);
                    }
                    return scalar::c_type(last);
                }
                if scalar::is_ffi_module(prefix) {
                    return scalar::c_type(last);
                }
                None
            }
            _ => None,
        }
    }

    fn alias(&self, name: &str) -> Option<&syn::ItemType> {
        self.callees.iter().find_map(|item| match item {
            syn::Item::Type(t) if t.ident == name && t.generics.params.is_empty() => Some(t),
            _ => None,
        })
    }
}

/// What a macro invocation is allowed to be.
pub(crate) enum MacroPolicy {
    /// Its arguments are comma-separated expressions that we can analyze.
    Exprs,
    /// It performs I/O.
    Io,
    /// Anything else.
    Unknown,
}

pub(crate) fn macro_policy(mac: &syn::Macro) -> MacroPolicy {
    let name = mac
        .path
        .segments
        .last()
        .map(|s| s.ident.to_string())
        .unwrap_or_default();
    match name.as_str() {
        "assert" | "assert_eq" | "assert_ne" | "debug_assert" | "debug_assert_eq"
        | "debug_assert_ne" | "panic" | "unreachable" | "unimplemented" | "todo" | "format" => {
            MacroPolicy::Exprs
        }
        "print" | "println" | "eprint" | "eprintln" | "dbg" | "write" | "writeln" => {
            MacroPolicy::Io
        }
        _ => MacroPolicy::Unknown,
    }
}

pub(crate) fn macro_args(
    mac: &syn::Macro,
) -> syn::Result<syn::punctuated::Punctuated<syn::Expr, syn::Token![,]>> {
    use syn::parse::Parser;
    syn::punctuated::Punctuated::parse_terminated.parse2(mac.tokens.clone())
}

pub(crate) fn macro_skip(mac: &syn::Macro) -> Option<Skip> {
    let name = mac.path.to_token_stream().to_string().replace(' ', "");
    match macro_policy(mac) {
        MacroPolicy::Exprs => match macro_args(mac) {
            Ok(_) => None,
            Err(_) => Some(Skip::new(
                "macro",
                format!("could not analyze the arguments of `{name}!`"),
            )),
        },
        MacroPolicy::Io => Some(Skip::new("io", format!("uses `{name}!`"))),
        MacroPolicy::Unknown => Some(Skip::new("macro", format!("uses macro `{name}!`"))),
    }
}

/// Why a path into the standard library is out of scope, if it is.
pub(crate) fn std_path_skip(segs: &[String]) -> Option<Skip> {
    let [root, module, rest @ ..] = segs else {
        return None;
    };
    if !matches!(root.as_str(), "std" | "core" | "alloc") {
        return None;
    }
    let shown = segs.join("::");
    match module.as_str() {
        "ptr" => Some(Skip::new("raw pointer", format!("uses `{shown}`"))),
        "intrinsics" => Some(Skip::new("unstable feature", format!("uses `{shown}`"))),
        "os" if rest.first().map(String::as_str) == Some("raw") => None,
        // Fences and atomics on locals; globals are excluded separately.
        "sync" if rest.first().map(String::as_str) == Some("atomic") => None,
        "io" | "fs" | "net" | "process" | "env" | "thread" | "time" | "sync" | "os" | "alloc"
        | "arch" => Some(Skip::new("io", format!("uses `{shown}`"))),
        _ => None,
    }
}

/// The C allocation and memory functions Kani models directly, so the heap
/// path may call them. Others (e.g. `strlen`, `printf`) need FFI models or
/// stubs and stay out of scope for now.
/// Whether a static is a scalar `static mut`, which the heap path models by
/// giving each version its own identically-initialised copy.
pub(crate) fn is_scalar_mut_static(s: &syn::ItemStatic) -> bool {
    if !matches!(s.mutability, syn::StaticMutability::Mut(_)) {
        return false;
    }
    if let syn::Type::Path(p) = &*s.ty {
        if let Some(seg) = p.path.segments.last() {
            let n = seg.ident.to_string();
            return crate::scalar::primitive(&n).is_some()
                || crate::scalar::c_type(&n).is_some()
                || crate::scalar::libc_typedef(&n).is_some();
        }
    }
    false
}

/// Whether a static is a read-only "data" global the heap path can pull into a
/// unit as an identical per-version copy: an array of scalars, a raw-pointer
/// table, or an immutable scalar (a lookup table or string constant). Unlike a
/// scalar `static mut` -- modelled with a final-value comparison -- these carry
/// no comparison, so they are sound only when the unit never writes them, which
/// the extractor checks before keeping them.
pub(crate) fn is_data_static(
    s: &syn::ItemStatic,
    structs: &BTreeMap<String, Vec<syn::Type>>,
    aliases: &BTreeMap<String, syn::Type>,
) -> bool {
    !is_scalar_mut_static(s) && is_data_type(&s.ty, structs, aliases)
}

/// Whether `ty` is a read-only "data" type the heap path can carry as an
/// identical per-version copy: a scalar, a raw pointer (carried by its bits, not
/// dereferenced here), an array of such, or a struct every one of whose fields
/// is itself a data type (e.g. libxml2's `xmlChRangeGroup` Unicode-range tables:
/// `{ nbShortRange: c_int, shortRange: *const xmlChSRange, .. }`). Type aliases
/// are followed. A struct field that is a pointer short-circuits to `true`
/// without recursing into the pointee, so the recursion (bounded anyway)
/// terminates; unions are excluded (absent from `structs`), since their bytes
/// are ambiguous. Carrying such a global is sound only because the extractor's
/// write-guard rejects the unit if any function writes it -- both versions then
/// read the identical const bytes, so any observable difference is real.
pub(crate) fn is_data_type(
    ty: &syn::Type,
    structs: &BTreeMap<String, Vec<syn::Type>>,
    aliases: &BTreeMap<String, syn::Type>,
) -> bool {
    is_data_type_rec(ty, structs, aliases, 0)
}

fn is_data_type_rec(
    ty: &syn::Type,
    structs: &BTreeMap<String, Vec<syn::Type>>,
    aliases: &BTreeMap<String, syn::Type>,
    depth: usize,
) -> bool {
    if depth > 16 {
        return false;
    }
    let resolved = crate::heapgen::resolve_alias(ty, aliases);
    match &resolved {
        syn::Type::Array(a) => is_data_type_rec(&a.elem, structs, aliases, depth + 1),
        syn::Type::Ptr(_) => true,
        syn::Type::Path(p) => p.path.segments.last().is_some_and(|seg| {
            let n = seg.ident.to_string();
            if crate::scalar::primitive(&n).is_some()
                || crate::scalar::c_type(&n).is_some()
                || crate::scalar::libc_typedef(&n).is_some()
            {
                return true;
            }
            // A struct of data fields: check every field recursively.
            structs.get(&n).is_some_and(|fields| {
                fields
                    .iter()
                    .all(|f| is_data_type_rec(f, structs, aliases, depth + 1))
            })
        }),
        _ => false,
    }
}

pub(crate) fn is_modelled_c_fn(name: &str) -> bool {
    matches!(
        name,
        // Allocation and memory functions, modelled by Kani/CBMC natively.
        "malloc" | "calloc" | "realloc" | "free" | "memcpy" | "memmove" | "memset" | "memcmp"
        // Read-only C string functions, defined for the scratch crate by
        // `strmodel` (sound Rust reimplementations over NUL-terminated
        // buffers, which `gen_cstr` guarantees). Writing functions (`strcpy`,
        // `strcat`) are left out: their destination bounds aren't modelled.
        | "strlen" | "strcmp" | "strncmp" | "strchr" | "strrchr"
        // The assertion handler (a failed assert cuts the path, like a panic)
        // and errno accessor (a per-run cell), also defined by `strmodel`.
        | "__assert_rtn" | "__assert_fail" | "__error" | "__errno_location"
    )
    // Pure math / ctype functions, modelled as argument-keyed oracles.
    || crate::strmodel::is_pure_oracle(name)
}

/// Finds constructs that are out of scope in a self-contained unit.
struct BodyChecker {
    skip: Option<Skip>,
    /// The heap path handles raw pointers, so it allows them while still
    /// rejecting the rest (IO, globals, foreign calls, unsupported macros).
    allow_pointers: bool,
    /// Struct-field and current-function variable types, so a modellable
    /// indirect call (`field.expect("..")(args)`) can be recognised.
    type_env: crate::indirectmodel::TypeEnv,
    /// Struct layouts (by name) and type aliases, for classifying a read-only
    /// data global of a struct-of-scalars type (see [`is_data_type`]).
    structs: BTreeMap<String, Vec<syn::Type>>,
    aliases: BTreeMap<String, syn::Type>,
}

impl BodyChecker {
    fn set(&mut self, skip: Skip) {
        self.skip.get_or_insert(skip);
    }
}

impl<'ast> Visit<'ast> for BodyChecker {
    fn visit_type_ptr(&mut self, p: &'ast syn::TypePtr) {
        if !self.allow_pointers {
            self.set(Skip::new("raw pointer", "uses raw pointers"));
        }
        syn::visit::visit_type_ptr(self, p);
    }

    fn visit_expr_call(&mut self, c: &'ast syn::ExprCall) {
        // A direct call names a function by path (`foo(...)`). Any other callee
        // expression is an indirect call through a function pointer (e.g. a
        // struct field `((*x).cb)(...)`), whose target is a symbolic address we
        // can't model soundly -- so it's out of scope. This guards the opaque
        // function-pointer field model: such a pointer may be carried, never
        // invoked. Checked on the heap path (where fn-ptr fields are built).
        if self.allow_pointers
            && crate::indirectmodel::is_indirect(c)
            && !self.type_env.indirect_is_modellable(c)
            && !crate::allocmodel::is_alloc_hook_call(c)
        {
            self.set(Skip::new(
                "indirect call",
                "calls through a function pointer",
            ));
        }
        syn::visit::visit_expr_call(self, c);
    }

    fn visit_item_fn(&mut self, f: &'ast syn::ItemFn) {
        // Record this function's parameter and local types so an indirect call
        // in its body can be typed, then check the body.
        self.type_env.with_fn(f);
        syn::visit::visit_item_fn(self, f);
    }

    fn visit_item_static(&mut self, s: &'ast syn::ItemStatic) {
        // On the heap path a scalar `static mut` is modelled (each version gets
        // its own copy, final values compared), so it is kept in scope.
        // A read-only data global (lookup table / string constant) is also
        // kept: the extractor only pulls one in after checking the unit never
        // writes it, so each version's identical copy is read identically.
        if self.allow_pointers
            && (is_scalar_mut_static(s) || is_data_static(s, &self.structs, &self.aliases))
        {
            return;
        }
        self.set(Skip::new(
            "global",
            format!("declares static `{}`", s.ident),
        ));
    }

    fn visit_item_foreign_mod(&mut self, m: &'ast syn::ItemForeignMod) {
        // On the heap path, foreign declarations of the C allocation and memory
        // functions Kani models are allowed; any other foreign item is not.
        for item in &m.items {
            let ok = self.allow_pointers
                && (matches!(item, syn::ForeignItem::Fn(f)
                    if is_modelled_c_fn(&f.sig.ident.to_string())
                        || crate::varmodel::is_variadic_modelled(&f.sig.ident.to_string())
                        || crate::strmodel::is_trace_modellable(&Some(syn::Item::ForeignMod(
                            syn::ItemForeignMod {
                                attrs: vec![],
                                unsafety: m.unsafety,
                                abi: m.abi.clone(),
                                brace_token: m.brace_token,
                                items: vec![syn::ForeignItem::Fn(f.clone())],
                            },
                        ))))
                    // An allocator-hook global (`static mut xmlMalloc: ..`) is
                    // given a module-local modelled definition by allocmodel.
                    || matches!(item, syn::ForeignItem::Static(s)
                        if crate::allocmodel::is_alloc_global(&s.ident.to_string())));
            if !ok {
                let what = match item {
                    syn::ForeignItem::Fn(f) => format!("foreign function `{}`", f.sig.ident),
                    _ => "a foreign item".to_owned(),
                };
                self.set(Skip::new("foreign call", format!("declares {what}")));
            }
        }
    }

    fn visit_path(&mut self, path: &'ast syn::Path) {
        let segs = scalar::idents(path);
        if segs.first().map(String::as_str) == Some("libc") {
            // On the heap path, `libc::malloc` and friends that Kani models are
            // allowed, like the equivalent extern declarations.
            let modelled = self.allow_pointers && segs.len() == 2 && is_modelled_c_fn(&segs[1]);
            if !modelled {
                self.set(Skip::new(
                    "foreign call",
                    format!("uses `{}`", segs.join("::")),
                ));
            }
        } else if let Some(skip) = std_path_skip(&segs) {
            // The heap path allows `core::ptr::*` (null, offset, copy, ...),
            // which Kani models; IO and the rest still put it out of scope.
            if !(self.allow_pointers && skip.category == "raw pointer") {
                self.set(skip);
            }
        }
        syn::visit::visit_path(self, path);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if let Some(skip) = macro_skip(mac) {
            self.set(skip);
        } else if let Ok(args) = macro_args(mac) {
            for arg in &args {
                self.visit_expr(arg);
            }
        }
    }
}

struct FloatFinder {
    found: bool,
}

impl<'ast> Visit<'ast> for FloatFinder {
    fn visit_lit_float(&mut self, _: &'ast syn::LitFloat) {
        self.found = true;
    }

    fn visit_ident(&mut self, ident: &'ast proc_macro2::Ident) {
        if matches!(
            ident.to_string().as_str(),
            "f32" | "f64" | "c_float" | "c_double"
        ) {
            self.found = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unit(function: &str, callees: &[&str]) -> FnUnit {
        FnUnit::parse(function, callees).unwrap()
    }

    #[test]
    fn heap_body_allows_modelled_allocators() {
        let u = unit(
            "pub unsafe fn f(p: *mut u8) -> *mut u8 { realloc(p, 8) }",
            &["extern \"C\" { fn realloc(p: *mut u8, n: usize) -> *mut u8; }"],
        );
        assert!(u.heap_body_in_scope().is_ok());
    }

    #[test]
    fn heap_body_rejects_other_foreign_calls() {
        // An external with more arguments than the trace records isn't modelled.
        let u = unit(
            "pub unsafe fn f() { big(1, 2, 3, 4); }",
            &["extern \"C\" { fn big(_: i32, _: i32, _: i32, _: i32); }"],
        );
        let skip = u.heap_body_in_scope().unwrap_err();
        assert_eq!(skip.category, "foreign call");
        assert!(skip.detail.contains("big"));
    }

    #[test]
    fn heap_body_rejects_an_indirect_call() {
        // A call through a function pointer (here a struct field) can't be
        // modelled soundly, so it is out of scope -- this is what keeps the
        // opaque fn-ptr-field model honest (the pointer is carried, not called).
        let u = unit(
            "pub unsafe fn f(s: *mut S) { ((*s).cb.unwrap())(s); }",
            &["pub struct S { pub cb: Option<unsafe extern \"C\" fn(*mut S)> }"],
        );
        let skip = u.heap_body_in_scope().unwrap_err();
        assert_eq!(skip.category, "indirect call");
    }

    #[test]
    fn heap_body_allows_a_carried_fn_ptr_field() {
        // Merely reading/storing a fn-ptr field (not calling it) is fine.
        let u = unit(
            "pub unsafe fn f(s: *mut S) -> bool { (*s).cb.is_some() }",
            &["pub struct S { pub cb: Option<unsafe extern \"C\" fn(*mut S)> }"],
        );
        assert!(u.heap_body_in_scope().is_ok());
    }

    #[test]
    fn heap_body_allows_pointers_but_scalar_validate_does_not() {
        let u = unit("pub unsafe fn f(p: *mut i32) -> i32 { *p }", &[]);
        // The heap path accepts the pointer; the scalar path rejects it (its
        // signature check runs first and sees a non-scalar argument).
        assert!(u.heap_body_in_scope().is_ok());
        assert!(u.validate().is_err());
    }

    #[test]
    fn body_checker_rejects_a_raw_pointer_on_the_scalar_path() {
        // A pointer buried in a callee's body (not the signature) is caught by
        // the body checker as a raw-pointer use on the scalar path.
        let u = unit(
            "pub fn f() -> i32 { g() }",
            &["pub fn g() -> i32 { let p: *const i32 = core::ptr::null(); unsafe { if p.is_null() { 0 } else { *p } } }"],
        );
        let skip = u.validate().unwrap_err();
        assert_eq!(skip.category, "raw pointer");
        assert!(u.heap_body_in_scope().is_ok());
    }
}
