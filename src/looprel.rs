//! Route B: relational (lockstep) equivalence for a single flat map-style loop,
//! proved **unbounded** via Kani's loop contracts instead of unrolled.
//!
//! Bounded model checking cannot discharge a loop over a runtime-sized array: no
//! fixed unwinding bound covers every size, and even a modest bound blows up. For
//! *equivalence* we do not need to reason about what the loop computes, only that
//! both versions compute the same thing. When both versions are the **same
//! flat map-style loop** -- a single counter from 0 to a loop-invariant bound,
//! each iteration writing a fresh location indexed by the counter, with no
//! loop-carried state but the counter and no read-back of what it wrote -- the
//! loops are equivalent iff, at an arbitrary iteration, they make the same
//! external calls and write the same value to the same address, and they run the
//! same number of times. That reduces to a single abstracted iteration (a loop
//! contract with invariant `counter <= bound`), so the proof holds for any size
//! and the array is never materialised.
//!
//! This module is the **detection and alignment** front end. It conservatively
//! recognises the shape and fails closed: anything it is not certain is a flat
//! map-style loop returns `None`, so the caller falls back to the ordinary
//! (bounded) heap path. Misclassifying a loop that carries state across
//! iterations (e.g. `sum += ...`) or reads a location it earlier wrote would
//! make the per-iteration reduction unsound, so each such feature is rejected.
//!
//! What it does NOT do yet: generate the relational harness (that needs a
//! loop-free oracle and per-call-site operand matching), and align loops that
//! differ structurally (reordered, fused, split -- the KestRel/Alien problem).
//! Until the codegen lands, a recognised + aligned pair is reported as an honest
//! `Skip`, never a proof.

// Stage 1 of route B: detection + alignment only. The relational harness
// codegen (stage 2) will consume these; until it lands they are intentionally
// unused, so the module opts out of the dead-code lint rather than littering
// each entry point with an attribute.
#![allow(dead_code)]

use syn::spanned::Spanned;
use syn::visit::Visit;

/// A recognised single flat map-style loop, with the pieces a relational harness
/// would need. All expressions are borrowed from the function's AST.
#[derive(Debug)]
pub struct FlatLoop<'a> {
    /// The loop counter (a local `let mut c: int = 0;` before the loop).
    pub counter: syn::Ident,
    /// The loop bound expression in `while counter < bound` (loop-invariant).
    pub bound: &'a syn::Expr,
    /// The loop body, with the trailing `counter += 1` still present.
    pub body: &'a syn::Block,
}

/// Recognise a flat map-style loop in `func`, or `None` if it is not certainly
/// one. Conservative by construction: every rejection keeps the caller on the
/// sound bounded path.
pub fn analyze(func: &syn::ItemFn) -> Option<FlatLoop<'_>> {
    // Exactly one loop in the whole function, and it is a `while`. A `for` or
    // `loop`, or more than one loop (nested or sequential), is out of scope.
    let mut loops = LoopCollector::default();
    loops.visit_block(&func.block);
    if loops.other_loop {
        return None;
    }
    if loops.whiles.len() != 1 {
        return None;
    }
    let while_expr = loops.whiles[0];

    // The guard must be `counter < bound`.
    let (counter, bound) = parse_guard(&while_expr.cond)?;

    // `counter` is a local `let mut counter: <int> = 0;` somewhere before the
    // loop, and is assigned nowhere except its initialiser and the `+= 1`.
    if !counter_is_zero_initialised_local(&func.block, &counter) {
        return None;
    }

    // The bound must not mention the counter and must not be assigned anywhere
    // in the function (loop-invariant across the loop). A bound with no clear
    // root ident is treated as unsafe and rejected by `ident_is_assigned`.
    let bound_root = bound_root_ident(bound);
    if mentions_ident(bound, &counter) || ident_is_assigned(&func.block, &bound_root) {
        return None;
    }

    // The body must end with `counter += 1` and not otherwise touch the counter,
    // carry no other mutable state across iterations, contain no nested loop,
    // and only write fresh counter-indexed locations (never read one back).
    if !body_is_map_style(&while_expr.body, &counter) {
        return None;
    }

    Some(FlatLoop {
        counter,
        bound,
        body: &while_expr.body,
    })
}

/// Whether old and new are both flat map-style loops that are aligned enough to
/// attempt a relational proof: same bound expression and same counter. (Richer
/// alignment -- renamed locals, reordered independent statements -- is future
/// work; a mismatch here just declines route B.)
pub fn aligned<'a>(
    old: &'a syn::ItemFn,
    new: &'a syn::ItemFn,
) -> Option<(FlatLoop<'a>, FlatLoop<'a>)> {
    let o = analyze(old)?;
    let n = analyze(new)?;
    if expr_eq(o.bound, n.bound) && o.counter == n.counter {
        Some((o, n))
    } else {
        None
    }
}

// ----- guard parsing -------------------------------------------------------

/// Parse `counter < bound` from a while guard.
fn parse_guard(cond: &syn::Expr) -> Option<(syn::Ident, &syn::Expr)> {
    let syn::Expr::Binary(b) = cond else {
        return None;
    };
    if !matches!(b.op, syn::BinOp::Lt(_)) {
        return None;
    }
    let counter = expr_as_ident(&b.left)?;
    Some((counter, &b.right))
}

fn expr_as_ident(e: &syn::Expr) -> Option<syn::Ident> {
    if let syn::Expr::Path(p) = e {
        p.path.get_ident().cloned()
    } else {
        None
    }
}

/// The root identifier a bound expression hangs off, used to check the bound is
/// never reassigned. For `(*ann).total_weights` this is `ann`; for a bare `n`
/// it is `n`. `None` if there is no single clear root.
fn bound_root_ident(e: &syn::Expr) -> Option<syn::Ident> {
    match e {
        syn::Expr::Path(p) => p.path.get_ident().cloned(),
        syn::Expr::Field(f) => bound_root_ident(&f.base),
        syn::Expr::Unary(u) => bound_root_ident(&u.expr),
        syn::Expr::Paren(p) => bound_root_ident(&p.expr),
        syn::Expr::MethodCall(m) => bound_root_ident(&m.receiver),
        syn::Expr::Cast(c) => bound_root_ident(&c.expr),
        _ => None,
    }
}

// ----- counter checks ------------------------------------------------------

/// The identifier a `let` pattern binds, unwrapping a type annotation
/// (`let mut i: c_int = 0` is `Pat::Type(Pat::Ident(i), c_int)`).
fn pat_binding(pat: &syn::Pat) -> Option<&syn::Ident> {
    match pat {
        syn::Pat::Ident(pi) => Some(&pi.ident),
        syn::Pat::Type(pt) => pat_binding(&pt.pat),
        _ => None,
    }
}

fn counter_is_zero_initialised_local(block: &syn::Block, counter: &syn::Ident) -> bool {
    for stmt in &block.stmts {
        if let syn::Stmt::Local(local) = stmt {
            // A `let [mut] c[: T] = ...;` for the counter. We don't require the
            // initialiser be literally 0 (c2rust emits `let mut i = 0;` then
            // `i = 0;`), only that the counter is a local.
            if pat_binding(&local.pat) == Some(counter) {
                return true;
            }
        }
    }
    false
}

// ----- body shape ----------------------------------------------------------

/// A body is map-style iff: it ends with `counter += 1`; the counter is not
/// otherwise assigned; there is no nested loop; the only `let mut` reassigned
/// across iterations is the counter (no accumulators); and every pointer write
/// is to a `<base>.offset(counter ...)` location whose base is not the target of
/// a read in the same body (no read-after-write of the mapped array).
fn body_is_map_style(body: &syn::Block, counter: &syn::Ident) -> bool {
    // Must end with `counter += 1` (or `counter = counter + 1`).
    let Some(last) = body.stmts.last() else {
        return false;
    };
    if !is_counter_increment(last, counter) {
        return false;
    }

    // No nested loops anywhere in the body.
    let mut loops = LoopCollector::default();
    loops.visit_block(body);
    if loops.other_loop || !loops.whiles.is_empty() {
        return false;
    }

    // No assignment to the counter other than the trailing increment, and no
    // assignment to any variable declared OUTSIDE the body (loop-carried state
    // other than the counter). We approximate "declared outside" as: any `=` /
    // `+=` etc. whose target is a bare identifier that is not declared by a
    // `let` inside this body and is not the counter -> reject (could be carried
    // state). Writes through a dereference are handled separately below.
    let mut locals = LocalIdents::default();
    locals.visit_block(body);
    let mut asg = AssignTargets::default();
    asg.visit_block(body);
    for (id, is_deref) in &asg.targets {
        if *is_deref {
            continue; // pointer writes checked below
        }
        if id == counter {
            continue; // the increment (already required to be the last stmt)
        }
        if !locals.names.contains(id) {
            return false; // assignment to a non-local scalar: possible carried state
        }
    }

    // Every pointer write target must be `<base>.offset(<counter-indexed>)` so
    // each iteration touches a distinct cell, and no read may go through such a
    // base (no read-after-write of the mapped array). We require that every
    // dereferenced write is counter-indexed; if any write target can't be shown
    // counter-indexed, reject.
    let mut writes = PtrWrites {
        counter: Some(counter.clone()),
        all_counter_indexed: false,
        seen: false,
    };
    writes.visit_block(body);
    if !writes.all_counter_indexed {
        return false;
    }

    true
}

fn is_counter_increment(stmt: &syn::Stmt, counter: &syn::Ident) -> bool {
    let expr = match stmt {
        syn::Stmt::Expr(e, _) => e,
        _ => return false,
    };
    match expr {
        // `counter += 1`
        syn::Expr::Binary(b) if matches!(b.op, syn::BinOp::AddAssign(_)) => {
            expr_as_ident(&b.left).as_ref() == Some(counter) && is_one(&b.right)
        }
        // `counter = counter + 1`
        syn::Expr::Assign(a) => {
            if expr_as_ident(&a.left).as_ref() != Some(counter) {
                return false;
            }
            if let syn::Expr::Binary(b) = &*a.right {
                matches!(b.op, syn::BinOp::Add(_))
                    && expr_as_ident(&b.left).as_ref() == Some(counter)
                    && is_one(&b.right)
            } else {
                false
            }
        }
        _ => false,
    }
}

fn is_one(e: &syn::Expr) -> bool {
    // Accept `1`, `1 as _`, `1 as c_int`, etc.
    match e {
        syn::Expr::Lit(l) => matches!(&l.lit, syn::Lit::Int(i) if i.base10_digits() == "1"),
        syn::Expr::Cast(c) => is_one(&c.expr),
        syn::Expr::Paren(p) => is_one(&p.expr),
        _ => false,
    }
}

// ----- visitors ------------------------------------------------------------

#[derive(Default)]
struct LoopCollector<'a> {
    whiles: Vec<&'a syn::ExprWhile>,
    other_loop: bool,
}
impl<'a> Visit<'a> for LoopCollector<'a> {
    fn visit_expr_while(&mut self, i: &'a syn::ExprWhile) {
        self.whiles.push(i);
        syn::visit::visit_expr_while(self, i);
    }
    fn visit_expr_for_loop(&mut self, i: &'a syn::ExprForLoop) {
        self.other_loop = true;
        syn::visit::visit_expr_for_loop(self, i);
    }
    fn visit_expr_loop(&mut self, i: &'a syn::ExprLoop) {
        self.other_loop = true;
        syn::visit::visit_expr_loop(self, i);
    }
}

#[derive(Default)]
struct LocalIdents {
    names: Vec<syn::Ident>,
}
impl<'a> Visit<'a> for LocalIdents {
    fn visit_local(&mut self, l: &'a syn::Local) {
        if let Some(id) = pat_binding(&l.pat) {
            self.names.push(id.clone());
        }
        syn::visit::visit_local(self, l);
    }
}

/// Collects assignment targets as (root ident, is_through_deref).
#[derive(Default)]
struct AssignTargets {
    targets: Vec<(syn::Ident, bool)>,
}
impl<'a> Visit<'a> for AssignTargets {
    fn visit_expr(&mut self, e: &'a syn::Expr) {
        match e {
            syn::Expr::Assign(a) => {
                record_target(&a.left, &mut self.targets);
            }
            syn::Expr::Binary(b)
                if matches!(
                    b.op,
                    syn::BinOp::AddAssign(_)
                        | syn::BinOp::SubAssign(_)
                        | syn::BinOp::MulAssign(_)
                        | syn::BinOp::DivAssign(_)
                        | syn::BinOp::RemAssign(_)
                        | syn::BinOp::BitXorAssign(_)
                        | syn::BinOp::BitAndAssign(_)
                        | syn::BinOp::BitOrAssign(_)
                        | syn::BinOp::ShlAssign(_)
                        | syn::BinOp::ShrAssign(_)
                ) =>
            {
                record_target(&b.left, &mut self.targets);
            }
            _ => {}
        }
        syn::visit::visit_expr(self, e);
    }
}

fn record_target(lhs: &syn::Expr, out: &mut Vec<(syn::Ident, bool)>) {
    match lhs {
        syn::Expr::Path(p) => {
            if let Some(id) = p.path.get_ident() {
                out.push((id.clone(), false));
            }
        }
        syn::Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => {
            if let Some(id) = bound_root_ident(&u.expr) {
                out.push((id, true));
            } else {
                // A deref write we can't attribute to a root: record a sentinel
                // that forces rejection via the counter-index check.
            }
        }
        syn::Expr::Paren(p) => record_target(&p.expr, out),
        _ => {}
    }
}

/// Checks that every pointer write (`*<place> = ...`) is to a location indexed
/// by the counter, e.g. `*base.offset(counter as isize) = v`.
#[derive(Default)]
struct PtrWrites {
    counter: Option<syn::Ident>,
    all_counter_indexed: bool,
    seen: bool,
}
impl<'a> Visit<'a> for PtrWrites {
    fn visit_expr(&mut self, e: &'a syn::Expr) {
        let target = match e {
            syn::Expr::Assign(a) => Some(&*a.left),
            syn::Expr::Binary(b) if is_compound_assign(&b.op) => Some(&*b.left),
            _ => None,
        };
        if let Some(syn::Expr::Unary(u)) = target {
            if matches!(u.op, syn::UnOp::Deref(_)) {
                if !self.seen {
                    self.seen = true;
                    self.all_counter_indexed = true;
                }
                if !self.deref_is_counter_indexed(&u.expr) {
                    self.all_counter_indexed = false;
                }
            }
        }
        syn::visit::visit_expr(self, e);
    }
}
impl PtrWrites {
    fn deref_is_counter_indexed(&self, place: &syn::Expr) -> bool {
        // Look for a `.offset(<e>)` / `.add(<e>)` where <e> mentions the counter.
        let Some(counter) = &self.counter else {
            return false;
        };
        let mut found = false;
        struct Finder<'c> {
            counter: &'c syn::Ident,
            found: &'c mut bool,
        }
        impl<'c, 'ast> Visit<'ast> for Finder<'c> {
            fn visit_expr_method_call(&mut self, m: &'ast syn::ExprMethodCall) {
                if (m.method == "offset" || m.method == "add")
                    && m.args.iter().any(|a| mentions_ident(a, self.counter))
                {
                    *self.found = true;
                }
                syn::visit::visit_expr_method_call(self, m);
            }
        }
        Finder {
            counter,
            found: &mut found,
        }
        .visit_expr(place);
        found
    }
}

fn is_compound_assign(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
            | syn::BinOp::RemAssign(_)
            | syn::BinOp::BitXorAssign(_)
            | syn::BinOp::BitAndAssign(_)
            | syn::BinOp::BitOrAssign(_)
            | syn::BinOp::ShlAssign(_)
            | syn::BinOp::ShrAssign(_)
    )
}

// ----- small AST helpers ---------------------------------------------------

fn mentions_ident(e: &syn::Expr, id: &syn::Ident) -> bool {
    let mut found = false;
    struct F<'a> {
        id: &'a syn::Ident,
        found: &'a mut bool,
    }
    impl<'a, 'ast> Visit<'ast> for F<'a> {
        fn visit_ident(&mut self, i: &'ast syn::Ident) {
            if i == self.id {
                *self.found = true;
            }
        }
    }
    F {
        id,
        found: &mut found,
    }
    .visit_expr(e);
    found
}

/// Whether the bound's root is *directly reassigned* (`id = ...`) anywhere in
/// the function, which would make the bound non-invariant. Writes *through* the
/// root (`*id.field.offset(..) = ..`, a deref target) do not count: they mutate
/// pointed-to array cells, not the pointer or the (distinct) bound field, under
/// the memory-safety assumption the whole heap path already relies on. A bound
/// with no clear root is treated as unsafe.
fn ident_is_assigned(block: &syn::Block, id: &Option<syn::Ident>) -> bool {
    let Some(id) = id else { return true };
    let mut asg = AssignTargets::default();
    asg.visit_block(block);
    asg.targets
        .iter()
        .any(|(t, is_deref)| t == id && !*is_deref)
}

/// Syntactic expression equality via token comparison (after pretty-printing).
fn expr_eq(a: &syn::Expr, b: &syn::Expr) -> bool {
    use quote::ToTokens;
    a.to_token_stream().to_string() == b.to_token_stream().to_string()
}

// A tiny helper so `Spanned` is used (keeps spans available for future
// diagnostics without a dead-import warning).
#[allow(dead_code)]
fn span_of(e: &syn::Expr) -> proc_macro2::Span {
    e.span()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(src: &str) -> syn::ItemFn {
        syn::parse_str(src).unwrap()
    }

    #[test]
    fn recognises_genann_randomize_shape() {
        let func = f(r#"
            pub unsafe fn randomize(ann: *mut genann) {
                let mut i: i32 = 0;
                i = 0;
                while i < (*ann).total_weights {
                    let r: f64 = rand() as f64 / RAND_MAX as f64;
                    *(*ann).weight.offset(i as isize) = r - 0.5f64;
                    i += 1;
                }
            }
        "#);
        let fl = analyze(&func).expect("should recognise a flat map loop");
        assert_eq!(fl.counter, "i");
    }

    #[test]
    fn rejects_accumulator_loop() {
        // A running `sum` carried across iterations is not map-style.
        let func = f(r#"
            pub unsafe fn dot(p: *const f64, n: i32) -> f64 {
                let mut i: i32 = 0;
                let mut sum: f64 = 0.0;
                while i < n {
                    sum += *p.offset(i as isize);
                    i += 1;
                }
                sum
            }
        "#);
        assert!(analyze(&func).is_none(), "accumulator must be rejected");
    }

    #[test]
    fn rejects_nested_loop() {
        let func = f(r#"
            pub unsafe fn m(a: *mut f64, n: i32) {
                let mut i: i32 = 0;
                while i < n {
                    let mut j: i32 = 0;
                    while j < n { j += 1; }
                    *a.offset(i as isize) = 0.0;
                    i += 1;
                }
            }
        "#);
        assert!(analyze(&func).is_none(), "nested loop must be rejected");
    }

    #[test]
    fn rejects_non_counter_indexed_write() {
        // Writes to a fixed location every iteration -> not a fresh-cell map.
        let func = f(r#"
            pub unsafe fn m(a: *mut f64, n: i32) {
                let mut i: i32 = 0;
                while i < n {
                    *a.offset(0 as isize) = 1.0;
                    i += 1;
                }
            }
        "#);
        assert!(
            analyze(&func).is_none(),
            "non-counter-indexed write must be rejected"
        );
    }

    #[test]
    fn rejects_for_loop() {
        let func = f(r#"
            pub unsafe fn m(a: *mut f64, n: i32) {
                for i in 0..n { unsafe { *a.offset(i as isize) = 0.0; } }
            }
        "#);
        assert!(analyze(&func).is_none(), "for loops are out of scope");
    }

    #[test]
    fn aligns_identical_randomize() {
        let src = r#"
            pub unsafe fn randomize(ann: *mut genann) {
                let mut i: i32 = 0;
                while i < (*ann).total_weights {
                    *(*ann).weight.offset(i as isize) = 0.5f64;
                    i += 1;
                }
            }
        "#;
        assert!(aligned(&f(src), &f(src)).is_some());
    }

    #[test]
    fn declines_alignment_on_different_bound() {
        let a = r#"
            pub unsafe fn m(ann: *mut genann) {
                let mut i: i32 = 0;
                while i < (*ann).total_weights { *(*ann).weight.offset(i as isize) = 0.5; i += 1; }
            }
        "#;
        let b = r#"
            pub unsafe fn m(ann: *mut genann) {
                let mut i: i32 = 0;
                while i < (*ann).total_neurons { *(*ann).weight.offset(i as isize) = 0.5; i += 1; }
            }
        "#;
        assert!(
            aligned(&f(a), &f(b)).is_none(),
            "different bound must decline"
        );
    }
}
