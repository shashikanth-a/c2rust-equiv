//! Subsystem B -- equality saturation over Program Expression Graphs (Tate et
//! al.'s PEG / Peggy), a second backend independent of Kani and of any
//! environment model. Two functions are equivalent when their translated
//! expressions land in the same e-class after saturating a set of
//! **semantics-preserving** rewrite rules: congruence (automatic in the
//! e-graph) then equates syntactically-different-but-equal computations.
//!
//! Soundness: [`equivalent`] returns `Some(true)` only when both expressions
//! provably reduce to one e-class under rules that each preserve meaning for
//! all inputs. `Some(false)` means *not proved equal here* (it is a sound but
//! incomplete backend -- never read it as "proved different"), and `None` means
//! a construct outside the supported fragment, so the function can't be decided
//! by this backend and some other must.
//!
//! The tool's semantics counts arithmetic **overflow as a panic** (as in a
//! build with overflow checks -- Kani always checks), so two functions are
//! equivalent only if they also panic on exactly the same inputs. That rules
//! out, for the *checked* operators, any rewrite that moves where an overflow
//! can occur: associativity, distributivity, `a-b = a+(-b)` and `-(-a) = a` are
//! therefore **excluded** for them (e.g. `(a+b)+c` can overflow where
//! `a+(b+c)` does not). The checked rules kept are only those that preserve
//! both value and overflow behaviour on every input: commutativity of `+`/`*`,
//! `x+0 = x`, `x*1 = x`, `x*0 = 0`, `x-x = 0`, and `x*2 = x+x` (which overflows
//! exactly when `x+x` does). General constant folding is omitted too (folding
//! an overflowing constant is width-dependent).
//!
//! **Wrapping operators** are different. c2rust-transpiled C emits
//! `a.wrapping_add(b)`, `wrapping_sub`, `wrapping_mul` and `wrapping_neg` for C
//! integer arithmetic, which never panics: it is two's-complement arithmetic
//! modulo `2^n`. That is a commutative ring, so the **full ring axioms hold
//! soundly** for these operators -- commutativity *and* associativity of `+`
//! and `*`, distributivity of `*` over `+`, `a-b = a+(-b)` and `-(-a) = a` --
//! because none of them can change an (impossible) panic. They are modelled as
//! their own node kind (`w+`, `w-`, `w*`, `wneg`) so these stronger rules match
//! only wrapping subtrees and never a checked operator, keeping the checked
//! fragment sound. A checked `+` and a wrapping `w+` are distinct nodes and are
//! never equated, which is correct: they differ precisely on the inputs where
//! one panics.
//!
//! Current fragment: straight-line integer functions -- `let` bindings and a
//! final (or `return`) expression over checked `+`, `-`, `*`, unary `-`, the
//! wrapping method calls above, integer literals and parameters. Loops,
//! pointers, calls and control flow are future work (they need PEG
//! theta/eval/pass nodes); anything unsupported makes [`equivalent`] return
//! `None` rather than guess.

use std::collections::HashMap;

use egg::{define_language, rewrite as rw, EGraph, Id, Rewrite, Runner, Symbol};

define_language! {
    /// A program expression graph node. Leaves are integer literals and opaque
    /// symbols (parameters, by position); the rest are integer operators.
    pub enum Peg {
        // Checked (overflow-as-panic) operators.
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "neg" = Neg([Id; 1]),
        // Wrapping (two's-complement modular) operators -- a commutative ring,
        // so the full ring axioms apply soundly (see module docs). Kept as
        // distinct node kinds so their rules never touch a checked operator.
        "w+" = WAdd([Id; 2]),
        "w-" = WSub([Id; 2]),
        "w*" = WMul([Id; 2]),
        "wneg" = WNeg([Id; 1]),
        Num(i64),
        Sym(Symbol),
    }
}

/// The rewrite rules. Each preserves BOTH the computed value AND the set of
/// inputs on which the expression overflows (panics), so a proof of
/// equivalence under them is sound under overflow-as-panic semantics. Rules
/// that would move an overflow point (associativity, distributivity,
/// sub-as-add-neg, neg-neg) are deliberately NOT included -- see module docs.
fn rules() -> Vec<Rewrite<Peg, ()>> {
    vec![
        // `a + b` and `b + a` compute the same sum and overflow together.
        rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("comm-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        // Identities that neither change the value nor introduce an overflow.
        rw!("add-0"; "(+ ?a 0)" => "?a"),
        rw!("mul-1"; "(* ?a 1)" => "?a"),
        rw!("mul-0"; "(* ?a 0)" => "0"),
        rw!("sub-self"; "(- ?a ?a)" => "0"),
        // `a * 2` and `a + a` are the same value and overflow on the same inputs.
        rw!("double";  "(* ?a 2)" => "(+ ?a ?a)"),
        rw!("double2"; "(+ ?a ?a)" => "(* ?a 2)"),
        // --- Wrapping operators: a commutative ring mod 2^n, so the FULL ring
        // axioms are sound (no operation can panic). These patterns only match
        // the wrapping node kinds, so they never rewrite a checked operator.
        rw!("w-comm-add"; "(w+ ?a ?b)" => "(w+ ?b ?a)"),
        rw!("w-comm-mul"; "(w* ?a ?b)" => "(w* ?b ?a)"),
        rw!("w-assoc-add"; "(w+ (w+ ?a ?b) ?c)" => "(w+ ?a (w+ ?b ?c))"),
        rw!("w-assoc-add2"; "(w+ ?a (w+ ?b ?c))" => "(w+ (w+ ?a ?b) ?c)"),
        rw!("w-assoc-mul"; "(w* (w* ?a ?b) ?c)" => "(w* ?a (w* ?b ?c))"),
        rw!("w-assoc-mul2"; "(w* ?a (w* ?b ?c))" => "(w* (w* ?a ?b) ?c)"),
        rw!("w-distrib"; "(w* ?a (w+ ?b ?c))" => "(w+ (w* ?a ?b) (w* ?a ?c))"),
        rw!("w-distrib2"; "(w+ (w* ?a ?b) (w* ?a ?c))" => "(w* ?a (w+ ?b ?c))"),
        rw!("w-add-0"; "(w+ ?a 0)" => "?a"),
        rw!("w-mul-1"; "(w* ?a 1)" => "?a"),
        rw!("w-mul-0"; "(w* ?a 0)" => "0"),
        rw!("w-sub-self"; "(w- ?a ?a)" => "0"),
        // In a ring, subtraction is addition of the negation, and negation is
        // an involution -- both sound because wrapping never panics.
        rw!("w-sub-neg"; "(w- ?a ?b)" => "(w+ ?a (wneg ?b))"),
        rw!("w-sub-neg2"; "(w+ ?a (wneg ?b))" => "(w- ?a ?b)"),
        rw!("w-neg-neg"; "(wneg (wneg ?a))" => "?a"),
        rw!("w-double";  "(w* ?a 2)" => "(w+ ?a ?a)"),
        rw!("w-double2"; "(w+ ?a ?a)" => "(w* ?a 2)"),
    ]
}

/// Decide equivalence of two functions by equality saturation.
///
/// `Some(true)`: proved equivalent (sound). `Some(false)`: not proved equal by
/// this backend (inconclusive, never "proved different"). `None`: outside the
/// supported straight-line integer fragment -- can't be decided here.
pub fn equivalent(old: &syn::ItemFn, new: &syn::ItemFn) -> Option<bool> {
    // The two functions must agree on arity for their parameters to correspond.
    if old.sig.inputs.len() != new.sig.inputs.len() {
        return None;
    }
    let mut egraph = EGraph::<Peg, ()>::default();
    // Both functions share one e-graph, and parameters are the same symbol by
    // position, so corresponding parameters are the same node.
    let a = translate_fn(&mut egraph, old)?;
    let b = translate_fn(&mut egraph, new)?;
    let runner = Runner::default().with_egraph(egraph).run(&rules());
    Some(runner.egraph.find(a) == runner.egraph.find(b))
}

/// Translate a function into a root expression id, binding each parameter (by
/// position) to a shared opaque symbol. `None` on anything unsupported.
fn translate_fn(g: &mut EGraph<Peg, ()>, f: &syn::ItemFn) -> Option<Id> {
    let mut env: HashMap<String, Id> = HashMap::new();
    for (i, input) in f.sig.inputs.iter().enumerate() {
        let syn::FnArg::Typed(pt) = input else {
            return None;
        };
        let syn::Pat::Ident(id) = &*pt.pat else {
            return None;
        };
        let sym = g.add(Peg::Sym(format!("a{i}").into()));
        env.insert(id.ident.to_string(), sym);
    }
    translate_block(g, &f.block, &mut env)
}

fn translate_block(
    g: &mut EGraph<Peg, ()>,
    block: &syn::Block,
    env: &mut HashMap<String, Id>,
) -> Option<Id> {
    let last = block.stmts.len().saturating_sub(1);
    for (i, stmt) in block.stmts.iter().enumerate() {
        match stmt {
            syn::Stmt::Local(local) => {
                let syn::Pat::Ident(id) = &local.pat else {
                    return None;
                };
                let init = local.init.as_ref()?;
                if init.diverge.is_some() {
                    return None;
                }
                let value = translate_expr(g, &init.expr, env)?;
                env.insert(id.ident.to_string(), value);
            }
            // A `return e;` anywhere, or the final tail expression, is the root.
            syn::Stmt::Expr(syn::Expr::Return(r), _) => {
                return translate_expr(g, r.expr.as_ref()?, env);
            }
            syn::Stmt::Expr(e, semi) if i == last && semi.is_none() => {
                return translate_expr(g, e, env);
            }
            // Any other statement (a side-effecting expression, an item, a
            // macro) is outside the straight-line fragment.
            _ => return None,
        }
    }
    None
}

fn translate_expr(
    g: &mut EGraph<Peg, ()>,
    e: &syn::Expr,
    env: &HashMap<String, Id>,
) -> Option<Id> {
    match e {
        syn::Expr::Lit(l) => match &l.lit {
            syn::Lit::Int(n) => Some(g.add(Peg::Num(n.base10_parse().ok()?))),
            _ => None,
        },
        syn::Expr::Path(p) => {
            let name = p.path.get_ident()?.to_string();
            env.get(&name).copied()
        }
        syn::Expr::Paren(p) => translate_expr(g, &p.expr, env),
        syn::Expr::Group(group) => translate_expr(g, &group.expr, env),
        syn::Expr::Unary(u) => match u.op {
            syn::UnOp::Neg(_) => {
                let a = translate_expr(g, &u.expr, env)?;
                Some(g.add(Peg::Neg([a])))
            }
            _ => None,
        },
        syn::Expr::Binary(b) => {
            let l = translate_expr(g, &b.left, env)?;
            let r = translate_expr(g, &b.right, env)?;
            match b.op {
                syn::BinOp::Add(_) => Some(g.add(Peg::Add([l, r]))),
                syn::BinOp::Sub(_) => Some(g.add(Peg::Sub([l, r]))),
                syn::BinOp::Mul(_) => Some(g.add(Peg::Mul([l, r]))),
                _ => None,
            }
        }
        // c2rust emits C integer arithmetic as wrapping method calls. These are
        // modular (never panic), so they become the wrapping node kinds.
        syn::Expr::MethodCall(mc) if mc.turbofish.is_none() => {
            let recv = translate_expr(g, &mc.receiver, env)?;
            let method = mc.method.to_string();
            let mut args = mc.args.iter();
            match (method.as_str(), mc.args.len()) {
                ("wrapping_neg", 0) => Some(g.add(Peg::WNeg([recv]))),
                ("wrapping_add", 1) => {
                    let b = translate_expr(g, args.next()?, env)?;
                    Some(g.add(Peg::WAdd([recv, b])))
                }
                ("wrapping_sub", 1) => {
                    let b = translate_expr(g, args.next()?, env)?;
                    Some(g.add(Peg::WSub([recv, b])))
                }
                ("wrapping_mul", 1) => {
                    let b = translate_expr(g, args.next()?, env)?;
                    Some(g.add(Peg::WMul([recv, b])))
                }
                _ => None,
            }
        }
        syn::Expr::Return(r) => translate_expr(g, r.expr.as_ref()?, env),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(src: &str) -> syn::ItemFn {
        syn::parse_str(src).unwrap()
    }

    #[test]
    fn commutativity_is_proved() {
        let a = f("fn g(x: i64, y: i64) -> i64 { x + y }");
        let b = f("fn g(x: i64, y: i64) -> i64 { y + x }");
        assert_eq!(equivalent(&a, &b), Some(true));
    }

    #[test]
    fn strength_reduction_is_proved() {
        let a = f("fn g(x: i64) -> i64 { x * 2 }");
        let b = f("fn g(x: i64) -> i64 { x + x }");
        assert_eq!(equivalent(&a, &b), Some(true));
    }

    #[test]
    fn let_bindings_are_inlined() {
        // `let` bindings are threaded through; commutativity still proves these.
        let a = f("fn g(x: i64, y: i64) -> i64 { let s = x + y; s }");
        let b = f("fn g(x: i64, y: i64) -> i64 { y + x }");
        assert_eq!(equivalent(&a, &b), Some(true));
    }

    #[test]
    fn distribution_is_withheld_under_overflow_semantics() {
        // x*(y+z) and x*y + x*z are equal only under wrapping arithmetic; with
        // overflow-as-panic they panic on different inputs, so the backend must
        // NOT prove them equivalent (it would be unsound).
        let a = f("fn g(x: i64, y: i64, z: i64) -> i64 { x * (y + z) }");
        let b = f("fn g(x: i64, y: i64, z: i64) -> i64 { let p = x * y; let q = x * z; p + q }");
        assert_eq!(equivalent(&a, &b), Some(false));
    }

    #[test]
    fn associativity_is_withheld_under_overflow_semantics() {
        // (a+b)+c can overflow where a+(b+c) does not -- not provably equivalent.
        let a = f("fn g(a: i64, b: i64, c: i64) -> i64 { (a + b) + c }");
        let b = f("fn g(a: i64, b: i64, c: i64) -> i64 { a + (b + c) }");
        assert_eq!(equivalent(&a, &b), Some(false));
    }

    #[test]
    fn genuinely_different_functions_are_not_proved() {
        // a + b and a - b are not equal; the backend must not prove them equal.
        let a = f("fn g(x: i64, y: i64) -> i64 { x + y }");
        let b = f("fn g(x: i64, y: i64) -> i64 { x - y }");
        assert_eq!(equivalent(&a, &b), Some(false));
    }

    #[test]
    fn wrapping_associativity_is_proved() {
        // Wrapping add is associative mod 2^n (never panics), so the two
        // groupings ARE provably equivalent -- unlike checked `+`.
        let a = f("fn g(a: i64, b: i64, c: i64) -> i64 \
                   { a.wrapping_add(b).wrapping_add(c) }");
        let b = f("fn g(a: i64, b: i64, c: i64) -> i64 \
                   { a.wrapping_add(b.wrapping_add(c)) }");
        assert_eq!(equivalent(&a, &b), Some(true));
    }

    #[test]
    fn wrapping_distributivity_is_proved() {
        // x*(y+z) == x*y + x*z in the ring Z/2^n -- all wrapping ops.
        let a = f("fn g(x: i64, y: i64, z: i64) -> i64 \
                   { x.wrapping_mul(y.wrapping_add(z)) }");
        let b = f("fn g(x: i64, y: i64, z: i64) -> i64 \
                   { let p = x.wrapping_mul(y); let q = x.wrapping_mul(z); p.wrapping_add(q) }");
        assert_eq!(equivalent(&a, &b), Some(true));
    }

    #[test]
    fn wrapping_sub_is_add_of_negation() {
        // a - b == a + (-b) in the ring; both are wrapping.
        let a = f("fn g(a: i64, b: i64) -> i64 { a.wrapping_sub(b) }");
        let b = f("fn g(a: i64, b: i64) -> i64 { a.wrapping_add(b.wrapping_neg()) }");
        assert_eq!(equivalent(&a, &b), Some(true));
    }

    #[test]
    fn checked_and_wrapping_are_not_cross_equated() {
        // SOUNDNESS: checked `a + b` panics on overflow where wrapping
        // `a.wrapping_add(b)` does not, so they differ on exactly those inputs.
        // The backend must NOT prove them equivalent.
        let a = f("fn g(a: i64, b: i64) -> i64 { a + b }");
        let b = f("fn g(a: i64, b: i64) -> i64 { a.wrapping_add(b) }");
        assert_eq!(equivalent(&a, &b), Some(false));
    }

    #[test]
    fn checked_associativity_still_withheld_with_wrapping_rules_present() {
        // Adding the wrapping ring rules must not leak into the checked
        // operators: checked associativity stays unproven (would be unsound).
        let a = f("fn g(a: i64, b: i64, c: i64) -> i64 { (a + b) + c }");
        let b = f("fn g(a: i64, b: i64, c: i64) -> i64 { a + (b + c) }");
        assert_eq!(equivalent(&a, &b), Some(false));
    }

    #[test]
    fn unsupported_fragment_is_none() {
        // A loop is outside the straight-line fragment: undecided, not guessed.
        let a = f("fn g(x: i64) -> i64 { let mut s = 0; for _ in 0..x { s += 1; } s }");
        let b = f("fn g(x: i64) -> i64 { x }");
        assert_eq!(equivalent(&a, &b), None);
    }
}
