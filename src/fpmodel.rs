//! Modelling floating-point division as an uninterpreted operation on the heap
//! path.
//!
//! CBMC bit-blasts IEEE-754 division -- its single most expensive float op,
//! with the full special-case tree (NaN, subnormals, infinities, signed zero).
//! A single division over an unconstrained symbolic `f64` can make an otherwise
//! trivial equivalence proof time out: empirically, proving even `x == x` for
//! `1.0 / (1.0 + exp(-a))` does not finish in 120s, while the identical function
//! with the divide removed proves in ~2s. So a straight-line float function with
//! a `/` (e.g. a sigmoid activation) is unprovable by Kani as written, despite
//! having no loops and no real difficulty.
//!
//! For **equivalence** we never need to know *what* a division computes, only
//! that both versions compute the same thing. A floating-point division is a
//! deterministic function of its two operands' bit patterns (fixed rounding
//! mode), so modelling it as an oracle keyed on those bits -- the same device
//! already used for external calls like `exp` -- is sound:
//!
//! * identical operands yield the same oracle result in both versions, so an
//!   equivalent rewrite still proves equal; the oracle can never invent a false
//!   *equality*, because equal `(op, operand-bits)` means an equal real result;
//! * a rewrite that changes an operand, swaps operand order, or drops a
//!   negation produces a different key, so the results may differ and the
//!   divergence is caught (verified by the catch-direction test).
//!
//! The cost is **completeness**, never soundness: an equivalence that holds
//! only by a floating-point algebraic identity (reassociation, `x/x == 1.0`,
//! etc.) is no longer provable here -- it is reported as "not proved", never as
//! "different". c2rust-transpiled code preserves C's exact operation order, so
//! a faithful rewrite is unaffected; only a rewrite that deliberately
//! re-derives a float expression loses the proof (and differential testing
//! still covers it).
//!
//! Integer `/` is left as real division: it is cheap for CBMC, and its
//! divide-by-zero and `MIN / -1` panics are observable and must be preserved.
//! The rewrite therefore does not try to tell float from integer divisions
//! syntactically (the unit has no per-expression type information); it rewrites
//! every `/` to a call to [`FpDiv::__fpdiv`] and lets the trait dispatch by
//! type at monomorphisation -- floats route through the oracle, integers do a
//! real divide. A numeric type with no `FpDiv` impl is a compile error, which
//! leaves the function unmodelled (skipped) rather than modelled unsoundly,
//! matching how every other model fails closed. The `FpDiv` trait and its impls
//! live in the shared `support` module (see `heap_support.rs`).
//!
//! Compound assignment (`a /= b`, `BinOp::DivAssign`) is deliberately left
//! alone: rewriting it would require evaluating a possibly-side-effecting place
//! twice. It stays a real division (sound, just not abstracted), so a function
//! whose only float divide is a `/=` is not helped -- none of the current
//! targets use one.

use syn::visit_mut::VisitMut;

/// Rewrite every binary `/` in the items to `crate::support::FpDiv::__fpdiv`.
pub fn rewrite(items: &mut [syn::Item]) {
    let mut v = Rewriter;
    for item in items {
        v.visit_item_mut(item);
    }
}

struct Rewriter;

impl VisitMut for Rewriter {
    fn visit_expr_mut(&mut self, e: &mut syn::Expr) {
        // Recurse first so nested divisions (`a / b / c`) are rewritten
        // inner-first, leaving no `/` behind.
        syn::visit_mut::visit_expr_mut(self, e);
        if let syn::Expr::Binary(b) = e {
            if matches!(b.op, syn::BinOp::Div(_)) {
                let left = &b.left;
                let right = &b.right;
                *e = syn::parse_quote!(crate::support::FpDiv::__fpdiv(#left, #right));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;

    fn rewrite_fn(src: &str) -> String {
        let mut items = vec![syn::Item::Fn(syn::parse_str(src).unwrap())];
        rewrite(&mut items);
        items[0].to_token_stream().to_string()
    }

    #[test]
    fn rewrites_a_plain_division() {
        let out = rewrite_fn("fn f(a: f64, b: f64) -> f64 { a / b }");
        assert!(out.contains("FpDiv :: __fpdiv (a , b)"), "{out}");
        assert!(!out.contains("a / b"), "{out}");
    }

    #[test]
    fn rewrites_nested_divisions_inner_first() {
        let out = rewrite_fn("fn f(a: f64, b: f64, c: f64) -> f64 { a / b / c }");
        // `(a / b) / c` -> __fpdiv(__fpdiv(a, b), c)
        assert!(
            out.contains("__fpdiv (crate :: support :: FpDiv :: __fpdiv (a , b) , c)"),
            "{out}"
        );
    }

    #[test]
    fn leaves_other_operators_untouched() {
        let out = rewrite_fn("fn f(a: f64, b: f64) -> f64 { a + b * (a - b) }");
        assert!(!out.contains("__fpdiv"), "{out}");
    }

    #[test]
    fn leaves_compound_div_assign_alone() {
        // `a /= b` must not become a call (it would evaluate the place twice).
        let out = rewrite_fn("fn f(mut a: f64, b: f64) -> f64 { a /= b; a }");
        assert!(!out.contains("__fpdiv"), "{out}");
    }
}
