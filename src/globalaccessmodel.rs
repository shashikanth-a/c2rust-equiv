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

/// Whether these items both call a modelled error reporter and reference the
/// `xmlLastError` global. The error model (`crate::errormodel`) treats the
/// reporter as stateless -- it does not model the reporter's write to
/// `xmlLastError` -- so a read of that error state afterwards would observe the
/// stale initial value, which could hide a real divergence. A unit that does
/// both is therefore left out of heap scope (sound over-approximation).
pub fn reporter_and_lasterror(function: &syn::ItemFn, callees: &[syn::Item]) -> bool {
    // Cheap gate: `xmlLastError` can only be read when its accessor or the
    // global itself is in scope as a callee. Most units have neither, so skip
    // the full scan for them (sound: no accessor/global in scope => no read).
    let touches = callees.iter().any(|c| {
        matches!(c, syn::Item::Static(s) if s.ident == "xmlLastError")
            || matches!(c, syn::Item::Fn(f) if f.sig.ident == "__xmlLastError")
    });
    if !touches {
        return false;
    }
    let mut v = ReporterAndLastErr {
        reporter: false,
        lasterror: false,
    };
    v.visit_item_fn(function);
    for c in callees {
        v.visit_item(c);
    }
    v.reporter && v.lasterror
}

struct ReporterAndLastErr {
    reporter: bool,
    lasterror: bool,
}

impl<'ast> Visit<'ast> for ReporterAndLastErr {
    fn visit_expr_call(&mut self, c: &'ast syn::ExprCall) {
        if let syn::Expr::Path(p) = &*c.func {
            if let Some(name) = p.path.segments.last().map(|s| s.ident.to_string()) {
                if crate::errormodel::is_error_fn(&name) {
                    self.reporter = true;
                }
            }
        }
        syn::visit::visit_expr_call(self, c);
    }
    fn visit_ident(&mut self, id: &'ast syn::Ident) {
        if id == "xmlLastError" {
            self.lasterror = true;
        }
    }
}
