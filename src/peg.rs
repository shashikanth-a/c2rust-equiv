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
//! The rewrite rules are restricted to identities that hold at **every integer
//! width** under two's-complement wrapping (commutativity, associativity,
//! `x+0`, `x*1`, `x*0`, `x*2 = x+x`, `x-x = 0`, `a - b = a + (-b)`,
//! distributivity). So proving equivalence here is sound even though the
//! fragment ignores the specific scalar width. General constant folding is
//! deliberately omitted: folding an overflowing constant is width-dependent and
//! would not be sound across widths.
//!
//! Current fragment: straight-line integer functions -- `let` bindings and a
//! final (or `return`) expression over `+`, `-`, `*`, unary `-`, integer
//! literals and parameters. Loops, pointers, calls and control flow are future
//! work (they need PEG theta/eval/pass nodes); anything unsupported makes
//! [`equivalent`] return `None` rather than guess.

use std::collections::HashMap;

use egg::{define_language, rewrite as rw, EGraph, Id, Rewrite, Runner, Symbol};

define_language! {
    /// A program expression graph node. Leaves are integer literals and opaque
    /// symbols (parameters, by position); the rest are integer operators.
    pub enum Peg {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "neg" = Neg([Id; 1]),
        Num(i64),
        Sym(Symbol),
    }
}

/// The rewrite rules -- each a semantic identity valid at every integer width
/// under wrapping arithmetic, so a proof of equivalence under them is sound.
fn rules() -> Vec<Rewrite<Peg, ()>> {
    vec![
        rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
        rw!("assoc-add"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("assoc-add2";"(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("assoc-mul"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        rw!("assoc-mul2";"(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("add-0";     "(+ ?a 0)"         => "?a"),
        rw!("mul-1";     "(* ?a 1)"         => "?a"),
        rw!("mul-0";     "(* ?a 0)"         => "0"),
        rw!("sub-add-neg"; "(- ?a ?b)"      => "(+ ?a (neg ?b))"),
        rw!("add-neg-sub"; "(+ ?a (neg ?b))"=> "(- ?a ?b)"),
        rw!("neg-neg";   "(neg (neg ?a))"   => "?a"),
        rw!("double";    "(* ?a 2)"         => "(+ ?a ?a)"),
        rw!("double2";   "(+ ?a ?a)"        => "(* ?a 2)"),
        rw!("sub-self";  "(- ?a ?a)"        => "0"),
        rw!("distribute";"(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("factor";    "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
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
    fn let_bindings_and_distribution() {
        let a = f("fn g(x: i64, y: i64, z: i64) -> i64 { x * (y + z) }");
        let b = f("fn g(x: i64, y: i64, z: i64) -> i64 { let p = x * y; let q = x * z; p + q }");
        assert_eq!(equivalent(&a, &b), Some(true));
    }

    #[test]
    fn genuinely_different_functions_are_not_proved() {
        // a + b and a - b are not equal; the backend must not prove them equal.
        let a = f("fn g(x: i64, y: i64) -> i64 { x + y }");
        let b = f("fn g(x: i64, y: i64) -> i64 { x - y }");
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
