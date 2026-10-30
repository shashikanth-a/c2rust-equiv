//! Modelling c2rust's thread-local global accessors on the heap path.
//!
//! For every global that libxml2 can keep per-thread, c2rust emits an accessor
//! `__X() -> *mut T` of the shape
//!
//! ```ignore
//! fn __X() -> *mut T {
//!     if xmlIsMainThread() != 0 { return &raw mut X; }
//!     else { return &raw mut (*xmlGetGlobalState()).X; }
//! }
//! ```
//!
//! and every access to the global `X` goes through it. The else branch calls
//! through a cast function pointer (`xmlGetGlobalState`), which puts every
//! accessor -- and so every function that touches a global error/config state
//! -- out of heap scope.
//!
//! Model each accessor as its main-thread branch: rewrite its body to
//! `{ return &raw mut X; }`. This is the single-threaded execution assumption
//! already taken for the mutex model (`crate::mutexmodel`): the whole unit runs
//! on one thread, so `xmlIsMainThread()` is true and the per-thread indirection
//! is dead. Both versions are rewritten identically, and the global `X` is then
//! an ordinary modelled global (scalar/data/struct) the harness compares.

use syn::visit::Visit;

/// If `item` is a thread-local accessor, the global it returns on the main
/// thread. Detection: a zero-argument function named `__…` returning a pointer,
/// whose body takes `&raw mut <bare global>` -- the main-thread branch. The
/// per-thread branch takes `&raw mut (*…).field`, whose inner expression is a
/// field access, not a bare path, so the first bare `&raw mut <ident>` found is
/// unambiguously the main-thread global.
pub fn accessor_global(item: &syn::Item) -> Option<syn::Ident> {
    match item {
        syn::Item::Fn(f) => accessor_global_fn(f),
        _ => None,
    }
}

/// [`accessor_global`] for a function item directly (no `Item` wrapper/clone).
pub fn accessor_global_fn(f: &syn::ItemFn) -> Option<syn::Ident> {
    // Fast rejects before visiting the body: zero-argument `__…` returning a
    // pointer. Only the ~dozen real accessors reach the body scan.
    if !f.sig.inputs.is_empty() || !f.sig.ident.to_string().starts_with("__") {
        return None;
    }
    if !matches!(&f.sig.output, syn::ReturnType::Type(_, t) if matches!(**t, syn::Type::Ptr(_))) {
        return None;
    }
    let mut finder = BareGlobal(None);
    finder.visit_block(&f.block);
    finder.0
}

/// Finds the first `&raw mut <bare identifier>` in a block.
struct BareGlobal(Option<syn::Ident>);

impl<'ast> Visit<'ast> for BareGlobal {
    fn visit_expr_raw_addr(&mut self, e: &'ast syn::ExprRawAddr) {
        if self.0.is_none() {
            if let syn::Expr::Path(p) = &*e.expr {
                if let Some(id) = p.path.get_ident() {
                    self.0 = Some(id.clone());
                }
            }
        }
        syn::visit::visit_expr_raw_addr(self, e);
    }
}

/// Rewrite every accessor in `items` to its main-thread branch, dropping the
/// per-thread indirection.
pub fn rewrite(items: &mut [syn::Item]) {
    for item in items {
        if let Some(g) = accessor_global(item) {
            if let syn::Item::Fn(f) = item {
                f.block = syn::parse_quote!({
                    return &raw mut #g;
                });
            }
        }
    }
}

/// A rewritten clone of `item` for analysis, if it is an accessor (so the
/// extractor sees the main-thread body rather than the out-of-scope per-thread
/// branch); `None` leaves the item analysed as-is.
pub fn rewritten(item: &syn::Item) -> Option<syn::Item> {
    accessor_global(item)?;
    let mut it = item.clone();
    rewrite(std::slice::from_mut(&mut it));
    Some(it)
}

/// The pointer fields of `xmlError` (`xmlLastError`). The error model populates
/// these with null rather than the real formatted message (which it doesn't
/// model), so a unit that observably reads one would see null where real code
/// sees a string -- unsound if that value reaches the compared output. Such a
/// unit is kept out of heap scope; a unit that reads only the scalar fields
/// (code/domain/level/line/int1/int2), which the model populates faithfully per
/// report, is in scope.
const LASTERROR_PTR_FIELDS: &[&str] =
    &["message", "file", "str1", "str2", "str3", "ctxt", "node"];

/// Whether these items access a pointer field *of `xmlLastError`* -- a field
/// access `<e>.<ptr-field>` whose base `<e>` is the global `xmlLastError` or a
/// dereference of the `__xmlLastError()` accessor (`(*__xmlLastError()).file`).
/// Precise: a `.node`/`.file`/... on some other struct does not count (those
/// field names are ubiquitous in libxml2), only on the error global itself.
pub fn reads_lasterror_pointer_field(function: &syn::ItemFn, callees: &[syn::Item]) -> bool {
    struct PtrField(bool);
    impl PtrField {
        /// Whether `e` denotes `xmlLastError` or `*__xmlLastError()` (through
        /// parens/groups and a single deref).
        fn is_lasterror_base(e: &syn::Expr) -> bool {
            match e {
                syn::Expr::Paren(p) => Self::is_lasterror_base(&p.expr),
                syn::Expr::Group(g) => Self::is_lasterror_base(&g.expr),
                syn::Expr::Path(p) => p.path.is_ident("xmlLastError"),
                syn::Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => {
                    // `*__xmlLastError()` or `*<call producing the accessor>`.
                    matches!(&*u.expr, syn::Expr::Call(c)
                        if matches!(&*c.func, syn::Expr::Path(p)
                            if p.path.segments.last().is_some_and(|s| s.ident == "__xmlLastError")))
                }
                _ => false,
            }
        }
    }
    impl<'ast> Visit<'ast> for PtrField {
        fn visit_expr_field(&mut self, f: &'ast syn::ExprField) {
            if let syn::Member::Named(id) = &f.member {
                if LASTERROR_PTR_FIELDS.contains(&id.to_string().as_str())
                    && Self::is_lasterror_base(&f.base)
                {
                    self.0 = true;
                }
            }
            syn::visit::visit_expr_field(self, f);
        }
    }
    let mut v = PtrField(false);
    v.visit_item_fn(function);
    for c in callees {
        v.visit_item(c);
    }
    v.0
}

