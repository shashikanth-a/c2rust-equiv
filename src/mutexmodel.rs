//! Modelling libxml2's lock/unlock calls as no-ops on the heap path.
//!
//! libxml2 guards shared state with `xmlMutexLock(m)` / `xmlMutexUnlock(m)` and
//! their recursive variants `xmlRMutexLock` / `xmlRMutexUnlock`, where `m` is a
//! global mutex pointer (`xmlDictMutex`, `xmlThreadsMutex`, ...). Those wrappers
//! dereference the mutex, call the foreign `pthread_mutex_lock`, and read the
//! `libxml_is_threaded` global -- so inlining them drags in a foreign call and
//! two globals, putting almost every function that touches shared state out of
//! scope.
//!
//! For **sequential** equivalence -- the only kind we check -- a lock/unlock
//! pair has no observable effect: an uncontended `pthread_mutex_lock` returns 0
//! and mutates only the lock's own bytes, which no modelled function reads. The
//! literature's objection to no-op mutexes is that they hide data races and
//! deadlocks, which are concurrency properties outside our scope. So [`rewrite`]
//! drops each such call (replacing it with `()`), and the eligibility gates
//! admit it without resolving the wrapper or its global argument. Both versions
//! get the identical no-op treatment, so the differential proof is unaffected.
//!
//! Only the four crate wrappers are modelled. A direct `pthread_mutex_lock`
//! lives inside the mutex infrastructure itself (`xmlMutexLock`, `xmlNewMutex`),
//! which we never need to make eligible, so it is left out.

use syn::visit_mut::VisitMut;

/// The lock/unlock/free wrappers modelled as no-ops (dropped to `()`). Freeing
/// a mutex is a no-op for the same reason as unlocking: the mutex object's bytes
/// are never read by any modelled function (every access goes through these
/// wrappers), so destroying it has no observable sequential effect.
const WRAPPERS: &[&str] = &[
    "xmlMutexLock",
    "xmlMutexUnlock",
    "xmlRMutexLock",
    "xmlRMutexUnlock",
    "xmlFreeMutex",
    "xmlFreeRMutex",
];

/// The mutex constructors, modelled as returning a non-null sentinel pointer.
/// libxml2 allocates a mutex once, stores the handle in a global, null-checks
/// it, then only ever locks/unlocks/frees it -- all no-ops here -- so the handle
/// is never dereferenced. A fixed non-null sentinel (identical in both versions)
/// passes the null-check and drives both down the same path, without resolving
/// the constructor's body (which allocates and calls `pthread_mutex_init`).
const CTORS: &[&str] = &["xmlNewMutex", "xmlNewRMutex"];

/// Whether `call` is a call to a modelled lock/unlock wrapper whose arguments
/// are side-effect-free, so dropping the whole call (arguments included) is
/// sound. A direct call `xmlMutexLock(<global-or-field>)`; an argument that
/// itself calls a function or assigns is *not* treated as a no-op, so a real
/// side effect is never silently dropped.
pub fn is_mutex_call(call: &syn::ExprCall) -> bool {
    is_mutex_noop_call(call) || is_mutex_ctor_call(call)
}

/// A lock/unlock/free wrapper call with side-effect-free arguments, so dropping
/// the whole call (arguments included) to `()` is sound.
fn is_mutex_noop_call(call: &syn::ExprCall) -> bool {
    let Some(name) = call_name(call) else {
        return false;
    };
    WRAPPERS.contains(&name.as_str()) && call.args.iter().all(is_pure)
}

/// A mutex constructor call (`xmlNewMutex()` / `xmlNewRMutex()`), rewritten to a
/// non-null sentinel pointer.
fn is_mutex_ctor_call(call: &syn::ExprCall) -> bool {
    call_name(call).is_some_and(|n| CTORS.contains(&n.as_str()))
}

fn call_name(call: &syn::ExprCall) -> Option<String> {
    let syn::Expr::Path(p) = &*call.func else {
        return None;
    };
    p.path.segments.last().map(|seg| seg.ident.to_string())
}

/// A conservatively side-effect-free expression: a path, a field/index access,
/// a reference or dereference, a cast, or a parenthesised/grouped such -- but
/// never a call, method call, assignment, or macro. libxml2's lock arguments
/// are always a global pointer or a struct field, which are all pure.
fn is_pure(e: &syn::Expr) -> bool {
    match e {
        syn::Expr::Path(_) | syn::Expr::Lit(_) => true,
        syn::Expr::Field(f) => is_pure(&f.base),
        syn::Expr::Index(i) => is_pure(&i.expr) && is_pure(&i.index),
        syn::Expr::Reference(r) => is_pure(&r.expr),
        syn::Expr::Unary(u) => is_pure(&u.expr),
        syn::Expr::Cast(c) => is_pure(&c.expr),
        syn::Expr::Paren(p) => is_pure(&p.expr),
        syn::Expr::Group(g) => is_pure(&g.expr),
        // A `&raw const/mut place` expression (c2rust's addr-of) parses as a
        // verbatim token stream in some syn versions; treat a bare one as pure.
        syn::Expr::Verbatim(_) => true,
        _ => false,
    }
}

/// Replace every modelled lock/unlock call in `items` with `()`.
pub fn rewrite(items: &mut [syn::Item]) {
    let mut v = Rewriter;
    for item in items {
        v.visit_item_mut(item);
    }
}

struct Rewriter;

impl VisitMut for Rewriter {
    fn visit_expr_mut(&mut self, e: &mut syn::Expr) {
        // Recurse first, so a lock call nested in a larger expression is handled.
        syn::visit_mut::visit_expr_mut(self, e);
        if let syn::Expr::Call(c) = e {
            if is_mutex_ctor_call(c) {
                // A non-null sentinel pointer, cast to the assignment's pointer
                // type by inference. Never dereferenced (every mutex access is a
                // no-op wrapper), so a bogus address is sound.
                *e = syn::parse_quote!((1usize as *mut u8).cast());
            } else if is_mutex_noop_call(c) {
                *e = syn::parse_quote!(());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;

    fn expr_call(src: &str) -> syn::ExprCall {
        match syn::parse_str::<syn::Expr>(src).unwrap() {
            syn::Expr::Call(c) => c,
            other => panic!("not a call: {}", other.to_token_stream()),
        }
    }

    #[test]
    fn recognises_wrapper_calls_with_pure_args() {
        assert!(is_mutex_call(&expr_call("xmlMutexLock(xmlDictMutex)")));
        assert!(is_mutex_call(&expr_call("xmlRMutexUnlock((*ctxt).mutex)")));
        assert!(is_mutex_call(&expr_call("xmlMutexUnlock(m)")));
    }

    #[test]
    fn rejects_non_wrappers_and_impure_args() {
        assert!(!is_mutex_call(&expr_call("xmlFree(p)")));
        // An argument with its own side effect must not be dropped.
        assert!(!is_mutex_call(&expr_call("xmlMutexLock(get_mutex())")));
    }

    #[test]
    fn rewrite_drops_the_call() {
        let mut items = syn::parse_file(
            "pub unsafe fn f() { xmlMutexLock(xmlDictMutex); do_work(); xmlMutexUnlock(xmlDictMutex); }",
        )
        .unwrap()
        .items;
        rewrite(&mut items);
        let src = items
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(!src.contains("xmlMutexLock"));
        assert!(!src.contains("xmlMutexUnlock"));
        // The real work in between is untouched.
        assert!(src.contains("do_work"));
    }
}
