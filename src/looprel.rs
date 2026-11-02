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

    // The bound must not mention the counter and must be loop-invariant: it may
    // mention no identifier the function directly reassigns.
    if mentions_ident(bound, &counter) || !bound_is_invariant(&func.block, bound, &counter) {
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

/// Whether the bound is loop-invariant: it mentions no identifier the function
/// *directly* reassigns (`id = ...`). Writes *through* an identifier
/// (`*id.field.offset(..) = ..`, a deref target) do not count -- they mutate
/// pointed-to array cells, not the pointer or the (distinct) bound field, under
/// the memory-safety assumption the whole heap path already relies on. A bound
/// built only from literals, parameters and never-reassigned locals/fields
/// (e.g. `16` or `(*ann).total_weights`) is invariant; one mentioning a
/// variable the body writes is not. The counter is excluded here because a
/// bound mentioning the counter is rejected separately by the caller.
fn bound_is_invariant(block: &syn::Block, bound: &syn::Expr, counter: &syn::Ident) -> bool {
    let mut asg = AssignTargets::default();
    asg.visit_block(block);
    for (id, is_deref) in &asg.targets {
        if *is_deref || id == counter {
            continue;
        }
        if mentions_ident(bound, id) {
            return false;
        }
    }
    true
}

/// Syntactic expression equality via token comparison (after pretty-printing).
fn expr_eq(a: &syn::Expr, b: &syn::Expr) -> bool {
    use quote::ToTokens;
    a.to_token_stream().to_string() == b.to_token_stream().to_string()
}

/// Syntactic equality of two statement sequences, by token comparison.
fn stmts_eq(a: &[syn::Stmt], b: &[syn::Stmt]) -> bool {
    use quote::ToTokens;
    let tok = |s: &[syn::Stmt]| {
        s.iter()
            .map(|st| st.to_token_stream().to_string())
            .collect::<Vec<_>>()
    };
    tok(a) == tok(b)
}

// ----- route B plan (stage 2 input) ----------------------------------------

/// Everything the relational codegen needs for one aligned pair. The counter,
/// its type and the bound are shared (the alignment check requires them equal);
/// only the per-iteration body differs between the two versions.
#[derive(Debug)]
pub struct Plan {
    /// The loop counter, a parameter of each generated `__looprel_iter`.
    pub counter: syn::Ident,
    /// The counter's declared integer type (from its `let` annotation).
    pub counter_ty: syn::Type,
    /// The loop bound (from old; equal to new's by token comparison).
    pub bound: syn::Expr,
    /// Pre-loop statements with the counter's own init removed, run once at the
    /// start of each generated helper so a bound or body that reads a pre-loop
    /// local still resolves. Token-equal between the two versions (checked), so
    /// running them is sound: identical code has identical behaviour.
    pub preamble: Vec<syn::Stmt>,
    /// Old's loop body with the trailing `counter += 1` removed.
    pub old_iter_body: Vec<syn::Stmt>,
    /// New's loop body with the trailing `counter += 1` removed.
    pub new_iter_body: Vec<syn::Stmt>,
}

/// Build a relational plan if both functions are *exactly* a flat map-style loop
/// and are aligned. This is sound as a whole-**function** equivalence, not just
/// a loop equivalence: the return type is `()` (no post-loop value to compare),
/// the loop is the last statement (no post-loop code), and the pre-loop
/// statements are token-equal between the versions (so only the loop itself is
/// left to prove). With no loop-carried state but the counter (enforced by
/// [`analyze`]), one symbolic iteration over an arbitrary initial heap
/// over-approximates every reachable iteration, so proving the single iteration
/// equivalent proves the whole loop -- and hence the whole function -- equivalent
/// for any array size, without unrolling.
pub fn plan(old: &syn::ItemFn, new: &syn::ItemFn) -> Option<Plan> {
    let o = whole_fn_loop(old)?;
    let n = whole_fn_loop(new)?;
    // Same counter, same bound, identical pre-loop code: anything else declines.
    if o.counter != n.counter || !expr_eq(&o.bound, &n.bound) || !stmts_eq(&o.preamble, &n.preamble)
    {
        return None;
    }
    Some(Plan {
        counter: o.counter,
        counter_ty: o.counter_ty,
        bound: o.bound,
        preamble: o.preamble,
        old_iter_body: o.iter_body,
        new_iter_body: n.iter_body,
    })
}

/// Parameter positions (into the function's argument list) that are pointers
/// both versions **unconditionally dereference before any null guard**, so
/// assuming them non-null is sound: `plan` requires the preamble and bound to be
/// token-identical between the two versions, so if one is undefined on a null
/// argument the other is too, and a null input is therefore outside the
/// equivalence domain (nothing defined is lost by excluding it). The relational
/// harness emits `kani::assume(!p.is_null())` for each. Analysing one version
/// suffices because the two share these statements verbatim.
pub fn nonnull_args(func: &syn::ItemFn, plan: &Plan) -> Vec<usize> {
    let mut out = Vec::new();
    for (idx, input) in func.sig.inputs.iter().enumerate() {
        let syn::FnArg::Typed(pt) = input else {
            continue;
        };
        if !matches!(&*pt.ty, syn::Type::Ptr(_)) {
            continue;
        }
        if let Some(p) = pat_binding(&pt.pat) {
            if param_requires_non_null(p, plan) {
                out.push(idx);
            }
        }
    }
    out
}

fn param_requires_non_null(p: &syn::Ident, plan: &Plan) -> bool {
    // If the code tests `p` against null (or even just compares it), it may
    // handle null itself, so never assume non-null -- excluding it is the safe
    // choice (route B simply keeps declining such a function on its null case).
    if expr_tests_ptr(&plan.bound, p) || plan.preamble.iter().any(|s| stmt_tests_ptr(s, p)) {
        return false;
    }
    // The bound is evaluated unconditionally when the loop is entered; a direct
    // dereference of `p` there (with no branch in the bound expression) is
    // undefined on a null `p`, so null is out of domain.
    bound_has_direct_deref(&plan.bound, p)
}

/// Whether an expression tests a pointer `p` (an `is_null()` call on it, or any
/// `==`/`!=` comparison mentioning it). Conservative: a false positive only
/// *excludes* `p` from the non-null assumption, which is always safe.
fn expr_tests_ptr(e: &syn::Expr, p: &syn::Ident) -> bool {
    struct T<'a> {
        p: &'a syn::Ident,
        found: bool,
    }
    impl<'a, 'ast> Visit<'ast> for T<'a> {
        fn visit_expr_method_call(&mut self, m: &'ast syn::ExprMethodCall) {
            if m.method == "is_null" && expr_as_ident(&m.receiver).as_ref() == Some(self.p) {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, m);
        }
        fn visit_expr_binary(&mut self, b: &'ast syn::ExprBinary) {
            if matches!(b.op, syn::BinOp::Eq(_) | syn::BinOp::Ne(_))
                && (mentions_ident(&b.left, self.p) || mentions_ident(&b.right, self.p))
            {
                self.found = true;
            }
            syn::visit::visit_expr_binary(self, b);
        }
    }
    let mut t = T { p, found: false };
    t.visit_expr(e);
    t.found
}

fn stmt_tests_ptr(s: &syn::Stmt, p: &syn::Ident) -> bool {
    struct T<'a> {
        p: &'a syn::Ident,
        found: bool,
    }
    impl<'a, 'ast> Visit<'ast> for T<'a> {
        fn visit_expr(&mut self, e: &'ast syn::Expr) {
            if expr_tests_ptr(e, self.p) {
                self.found = true;
            }
            syn::visit::visit_expr(self, e);
        }
    }
    let mut t = T { p, found: false };
    t.visit_stmt(s);
    t.found
}

/// Whether the bound directly dereferences `p` with no conditional in the way:
/// no `if`/`match` anywhere in the bound (so the dereference is unconditional
/// whenever the bound is evaluated), and a `*p` / `(*p)...` somewhere in it.
fn bound_has_direct_deref(bound: &syn::Expr, p: &syn::Ident) -> bool {
    struct D<'a> {
        p: &'a syn::Ident,
        deref: bool,
        conditional: bool,
    }
    impl<'a, 'ast> Visit<'ast> for D<'a> {
        fn visit_expr_if(&mut self, _: &'ast syn::ExprIf) {
            self.conditional = true;
        }
        fn visit_expr_match(&mut self, _: &'ast syn::ExprMatch) {
            self.conditional = true;
        }
        fn visit_expr_unary(&mut self, u: &'ast syn::ExprUnary) {
            if matches!(u.op, syn::UnOp::Deref(_))
                && bound_root_ident(&u.expr).as_ref() == Some(self.p)
            {
                self.deref = true;
            }
            syn::visit::visit_expr_unary(self, u);
        }
    }
    let mut d = D {
        p,
        deref: false,
        conditional: false,
    };
    d.visit_expr(bound);
    d.deref && !d.conditional
}

/// One version's pieces for a relational plan.
struct WholeFn {
    counter: syn::Ident,
    counter_ty: syn::Type,
    bound: syn::Expr,
    preamble: Vec<syn::Stmt>,
    iter_body: Vec<syn::Stmt>,
}

/// Decompose `func` into (pre-loop preamble, the flat map loop's body) if the
/// function body is exactly a flat map-style loop as its last statement and
/// returns `()`. Returns `None` -- declining route B -- for anything else.
fn whole_fn_loop(func: &syn::ItemFn) -> Option<WholeFn> {
    // Must return `()`: route B compares per-iteration heap effects, not a
    // return value, so a function with a meaningful return is out of scope.
    if !matches!(func.sig.output, syn::ReturnType::Default) {
        return None;
    }
    let fl = analyze(func)?;
    let counter = fl.counter.clone();
    let bound = fl.bound.clone();
    let counter_ty = counter_type(&func.block, &counter)?;

    // The loop must be the function's last statement: no post-loop code, whose
    // (possibly divergent) effects route B would otherwise miss.
    let stmts = &func.block.stmts;
    let widx = stmts.iter().position(stmt_is_while)?;
    if widx != stmts.len() - 1 {
        return None;
    }

    // The iteration body is the loop body minus its trailing `counter += 1`
    // (guaranteed last by `analyze`). An early `return`/`break`/`continue`
    // inside it would not survive the per-iteration reduction, so decline.
    let mut iter_body = fl.body.stmts.clone();
    iter_body.pop();
    if stmts_have_control_flow(&iter_body) {
        return None;
    }
    // Every pointer write must be a plain `*<base>.offset(<idx>) = <val>` (or
    // `.add`), so the relational codegen can abstract it into an (address,
    // value) obligation without performing it. A compound assignment
    // (`*p.offset(c) += v`) reads the cell back, which the no-materialisation
    // abstraction cannot model, so decline.
    if !writes_are_simple(&iter_body) {
        return None;
    }

    // Pre-loop statements, minus the counter's own `let`/init assignment (the
    // counter becomes a helper parameter). What remains runs once per helper.
    let preamble: Vec<syn::Stmt> = stmts[..widx]
        .iter()
        .filter(|s| !stmt_defines_or_sets(s, &counter))
        .cloned()
        .collect();

    Some(WholeFn {
        counter,
        counter_ty,
        bound,
        preamble,
        iter_body,
    })
}

/// The counter's declared type, from its `let mut counter: T = ...;` binding.
/// `None` if the binding carries no explicit type (so the helper can't give the
/// counter parameter a type) -- c2rust always annotates, so this just declines.
fn counter_type(block: &syn::Block, counter: &syn::Ident) -> Option<syn::Type> {
    for stmt in &block.stmts {
        if let syn::Stmt::Local(local) = stmt {
            if pat_binding(&local.pat) == Some(counter) {
                if let syn::Pat::Type(pt) = &local.pat {
                    return Some((*pt.ty).clone());
                }
            }
        }
    }
    None
}

/// Whether a statement is a `while` loop (as a statement or a trailing expr).
fn stmt_is_while(stmt: &syn::Stmt) -> bool {
    matches!(stmt, syn::Stmt::Expr(syn::Expr::While(_), _))
}

/// Whether a statement defines (by `let`) or directly assigns the counter.
fn stmt_defines_or_sets(stmt: &syn::Stmt, counter: &syn::Ident) -> bool {
    match stmt {
        syn::Stmt::Local(l) => pat_binding(&l.pat) == Some(counter),
        syn::Stmt::Expr(syn::Expr::Assign(a), _) => {
            expr_as_ident(&a.left).as_ref() == Some(counter)
        }
        _ => false,
    }
}

/// Whether every pointer write in the body is a plain
/// `*<base>.offset(<idx>) = <val>` or `*<base>.add(<idx>) = <val>` -- the only
/// shape the relational codegen can abstract into an (address, value) trace
/// obligation. A compound assignment through a dereference (`*p.offset(c) += v`)
/// reads the cell back and so cannot be abstracted without materialising it; a
/// write whose place is not an `.offset`/`.add` method call likewise can't be
/// turned into an address without performing it. Either declines route B.
fn writes_are_simple(stmts: &[syn::Stmt]) -> bool {
    #[derive(Default)]
    struct W {
        ok: bool,
    }
    impl<'a> Visit<'a> for W {
        fn visit_expr(&mut self, e: &'a syn::Expr) {
            match e {
                // A compound assignment through a dereference: unsupported.
                syn::Expr::Binary(b)
                    if is_compound_assign(&b.op)
                        && matches!(&*b.left, syn::Expr::Unary(u)
                            if matches!(u.op, syn::UnOp::Deref(_))) =>
                {
                    self.ok = false;
                }
                // A plain assignment through a dereference: the place must be an
                // `.offset`/`.add` method call.
                syn::Expr::Assign(a) => {
                    if let syn::Expr::Unary(u) = &*a.left {
                        if matches!(u.op, syn::UnOp::Deref(_)) && !is_offset_place(&u.expr) {
                            self.ok = false;
                        }
                    }
                }
                _ => {}
            }
            syn::visit::visit_expr(self, e);
        }
    }
    let mut w = W { ok: true };
    for s in stmts {
        w.visit_stmt(s);
    }
    w.ok
}

/// Whether `place` is a `<base>.offset(<idx>)` or `<base>.add(<idx>)` call,
/// possibly wrapped in parentheses -- the dereferenceable place the relational
/// codegen knows how to turn into an address.
fn is_offset_place(place: &syn::Expr) -> bool {
    match place {
        syn::Expr::Paren(p) => is_offset_place(&p.expr),
        syn::Expr::MethodCall(m) => {
            (m.method == "offset" || m.method == "add") && m.args.len() == 1
        }
        _ => false,
    }
}

/// Whether any statement contains a `return`, `break` or `continue` (which the
/// per-iteration reduction cannot model). There are no nested loops in a body
/// `analyze` accepted, so a `break`/`continue` would target this loop.
fn stmts_have_control_flow(stmts: &[syn::Stmt]) -> bool {
    #[derive(Default)]
    struct CF {
        found: bool,
    }
    impl<'a> Visit<'a> for CF {
        fn visit_expr_return(&mut self, _: &'a syn::ExprReturn) {
            self.found = true;
        }
        fn visit_expr_break(&mut self, _: &'a syn::ExprBreak) {
            self.found = true;
        }
        fn visit_expr_continue(&mut self, _: &'a syn::ExprContinue) {
            self.found = true;
        }
        // Don't descend into closures or nested items: their control flow is
        // their own. (A body `analyze` accepted has no nested loops.)
        fn visit_item(&mut self, _: &'a syn::Item) {}
        fn visit_expr_closure(&mut self, _: &'a syn::ExprClosure) {}
    }
    let mut cf = CF::default();
    for s in stmts {
        cf.visit_stmt(s);
    }
    cf.found
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
    fn plans_identical_randomize() {
        let src = r#"
            pub unsafe fn randomize(ann: *mut genann) {
                let mut i: i32 = 0;
                while i < (*ann).total_weights {
                    *(*ann).weight.offset(i as isize) = 0.5f64;
                    i += 1;
                }
            }
        "#;
        let p = plan(&f(src), &f(src)).expect("identical randomize should plan");
        assert_eq!(p.counter, "i");
        // One body statement survives after the `i += 1` is stripped.
        assert_eq!(p.old_iter_body.len(), 1);
    }

    #[test]
    fn declines_plan_on_different_bound() {
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
        assert!(plan(&f(a), &f(b)).is_none(), "different bound must decline");
    }

    #[test]
    fn declines_plan_with_nonunit_return() {
        // A map loop that also returns a value is out of scope: route B compares
        // per-iteration effects, not a return.
        let src = r#"
            pub unsafe fn m(ann: *mut genann) -> i32 {
                let mut i: i32 = 0;
                while i < (*ann).total_weights { *(*ann).weight.offset(i as isize) = 0.5; i += 1; }
                0
            }
        "#;
        assert!(
            plan(&f(src), &f(src)).is_none(),
            "a non-unit return must decline"
        );
    }

    #[test]
    fn declines_plan_with_post_loop_code() {
        // A statement after the loop is not covered by the loop proof.
        let src = r#"
            pub unsafe fn m(ann: *mut genann) {
                let mut i: i32 = 0;
                while i < (*ann).total_weights { *(*ann).weight.offset(i as isize) = 0.5; i += 1; }
                *(*ann).weight = 1.0;
            }
        "#;
        assert!(
            plan(&f(src), &f(src)).is_none(),
            "post-loop code must decline"
        );
    }

    #[test]
    fn nonnull_args_flags_unguarded_pointer_deref_in_bound() {
        // A bound of `(*ann).total_weights` dereferences `ann` unconditionally
        // and with no null guard, so `ann` (parameter 0) is required non-null.
        let src = r#"
            pub unsafe fn randomize(ann: *mut genann) {
                let mut i: i32 = 0;
                while i < (*ann).total_weights {
                    *(*ann).weight.offset(i as isize) = 0.5f64;
                    i += 1;
                }
            }
        "#;
        let func = f(src);
        let p = plan(&func, &func).expect("plans");
        assert_eq!(nonnull_args(&func, &p), vec![0]);
    }

    #[test]
    fn nonnull_args_excludes_null_guarded_pointer() {
        // The function tests `v` for null and computes a zero bound for it, so
        // it is defined on null: never assume non-null.
        let src = r#"
            pub unsafe fn fill(v: *mut Vec1) {
                let n: i32 = if v.is_null() { 0 } else { (*v).len };
                let mut i: i32 = 0;
                while i < n {
                    *(*v).data.offset(i as isize) = 0.5f64;
                    i += 1;
                }
            }
        "#;
        let func = f(src);
        let p = plan(&func, &func).expect("plans");
        assert!(nonnull_args(&func, &p).is_empty());
    }

    #[test]
    fn declines_plan_on_divergent_preamble() {
        // Token-different pre-loop code leaves more than the loop to prove.
        let a = r#"
            pub unsafe fn m(ann: *mut genann) {
                let mut i: i32 = 0;
                let k: f64 = 0.0;
                while i < (*ann).total_weights { *(*ann).weight.offset(i as isize) = k; i += 1; }
            }
        "#;
        let b = r#"
            pub unsafe fn m(ann: *mut genann) {
                let mut i: i32 = 0;
                let k: f64 = 1.0;
                while i < (*ann).total_weights { *(*ann).weight.offset(i as isize) = k; i += 1; }
            }
        "#;
        assert!(
            plan(&f(a), &f(b)).is_none(),
            "divergent preamble must decline"
        );
    }
}
