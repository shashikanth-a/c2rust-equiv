//! Mod/ref (frame) analysis: a conservative set of locations a function may
//! write that are visible to its caller -- its `assigns` set. This is the
//! soundness crux of compositional summaries and the memory
//! model of the algebraic backend: a callee can only be replaced by
//! a havoc of this set if the set covers *every* caller-visible write it makes
//! (CBMC/Kani function-contract `assigns` semantics). So the analysis
//! over-approximates: anything it can't classify makes the whole set `Top`
//! (may write anything), which forces the caller to inline rather than
//! summarise -- less complete, never unsound.
//!
//! "Caller-visible" means writes through a pointer parameter (reaching the
//! caller's heap) or to a global. Writes through a pointer the function itself
//! allocated are local and don't escape, so they're ignored.

use std::collections::{BTreeMap, BTreeSet};

/// What a function may write that its caller can observe.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WriteSet {
    /// May write anything (an unclassifiable write): cannot be summarised.
    Top,
    /// Writes only through these pointer-parameter indices' pointees and these
    /// named globals. An empty set means the function is caller-side pure.
    Known {
        params: BTreeSet<usize>,
        globals: BTreeSet<String>,
    },
}

impl WriteSet {
    fn empty() -> Self {
        WriteSet::Known {
            params: BTreeSet::new(),
            globals: BTreeSet::new(),
        }
    }
    fn add_param(&mut self, i: usize) {
        if let WriteSet::Known { params, .. } = self {
            params.insert(i);
        }
    }
    fn add_global(&mut self, name: String) {
        if let WriteSet::Known { globals, .. } = self {
            globals.insert(name);
        }
    }
    fn top(&mut self) {
        *self = WriteSet::Top;
    }
}

/// Where a pointer value came from, for deciding whether a write through it is
/// caller-visible.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Prov {
    /// Derived from pointer parameter `i` (write escapes to the caller).
    Param(usize),
    /// A pointer the function made locally (write doesn't escape).
    Local,
    /// Unknown origin: a write through it is treated as `Top` (could be
    /// caller state).
    Unknown,
}

/// The caller-visible write set of a function body. `globals` names the crate
/// statics (so a write to one is attributed); `locals_alloc` names functions
/// whose result is a fresh local allocation (so a write through their result
/// doesn't escape) -- the modelled allocators.
pub fn write_set(f: &syn::ItemFn) -> WriteSet {
    // Pointer parameters, by index and bound name.
    let mut param_of: BTreeMap<String, usize> = BTreeMap::new();
    for (i, input) in f.sig.inputs.iter().enumerate() {
        if let syn::FnArg::Typed(pt) = input {
            if matches!(&*pt.ty, syn::Type::Ptr(_)) {
                if let syn::Pat::Ident(id) = &*pt.pat {
                    param_of.insert(id.ident.to_string(), i);
                }
            }
        }
    }
    let mut a = Analysis {
        param_of,
        prov: BTreeMap::new(),
        ws: WriteSet::empty(),
    };
    a.block(&f.block);
    a.ws
}

struct Analysis {
    param_of: BTreeMap<String, usize>,
    prov: BTreeMap<String, Prov>,
    ws: WriteSet,
}

impl Analysis {
    fn block(&mut self, b: &syn::Block) {
        for s in &b.stmts {
            self.stmt(s);
        }
    }

    fn stmt(&mut self, s: &syn::Stmt) {
        match s {
            syn::Stmt::Local(l) => {
                if let syn::Pat::Ident(id) = &l.pat {
                    let p = l
                        .init
                        .as_ref()
                        .map(|i| self.prov_of(&i.expr))
                        .unwrap_or(Prov::Unknown);
                    self.prov.insert(id.ident.to_string(), p);
                    if let Some(init) = &l.init {
                        self.expr(&init.expr);
                        if let Some(d) = &init.diverge {
                            self.expr(&d.1);
                        }
                    }
                }
            }
            syn::Stmt::Expr(e, _) => self.expr(e),
            syn::Stmt::Item(_) | syn::Stmt::Macro(_) => self.ws.top(),
        }
    }

    /// The provenance of a pointer-valued expression.
    fn prov_of(&self, e: &syn::Expr) -> Prov {
        match e {
            syn::Expr::Path(p) if p.path.segments.len() == 1 => {
                let name = p.path.segments[0].ident.to_string();
                if let Some(&i) = self.param_of.get(&name) {
                    Prov::Param(i)
                } else {
                    self.prov.get(&name).copied().unwrap_or(Prov::Unknown)
                }
            }
            // Pointer arithmetic and casts preserve provenance.
            syn::Expr::MethodCall(m)
                if matches!(
                    m.method.to_string().as_str(),
                    "offset" | "add" | "sub" | "wrapping_add" | "wrapping_sub" | "cast"
                ) =>
            {
                self.prov_of(&m.receiver)
            }
            syn::Expr::Cast(c) => self.prov_of(&c.expr),
            syn::Expr::Paren(p) => self.prov_of(&p.expr),
            syn::Expr::Reference(r) => self.prov_of(&r.expr),
            // A pointer a modelled allocator returned is the function's own
            // memory: writes through it don't escape to the caller.
            syn::Expr::Call(call) => match &*call.func {
                syn::Expr::Path(p)
                    if p.path.segments.last().is_some_and(|s| {
                        matches!(
                            s.ident.to_string().as_str(),
                            "malloc" | "calloc" | "realloc"
                        )
                    }) =>
                {
                    Prov::Local
                }
                _ => Prov::Unknown,
            },
            // A field of a dereferenced pointer: provenance of the base pointer.
            syn::Expr::Field(fld) => {
                if let syn::Expr::Unary(u) = &*fld.base {
                    if matches!(u.op, syn::UnOp::Deref(_)) {
                        return self.prov_of(&u.expr);
                    }
                }
                Prov::Unknown
            }
            _ => Prov::Unknown,
        }
    }

    /// The pointer whose pointee a place expression writes to, if any:
    /// `*p = _`, `(*p).f = _`, `p[i] = _`, `(*p).f[i].g = _`, ... all write
    /// through `p`.
    fn written_pointer<'a>(&self, place: &'a syn::Expr) -> Option<&'a syn::Expr> {
        match place {
            syn::Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => Some(&u.expr),
            syn::Expr::Field(f) => self.written_pointer(&f.base),
            syn::Expr::Index(i) => self.written_pointer(&i.expr),
            syn::Expr::Paren(p) => self.written_pointer(&p.expr),
            _ => None,
        }
    }

    /// Record a write to a place expression.
    fn record_write(&mut self, place: &syn::Expr) {
        // A write to a bare path: a local (ignored) or a global/static.
        if let syn::Expr::Path(p) = place {
            if p.path.segments.len() == 1 {
                let name = p.path.segments[0].ident.to_string();
                if !self.param_of.contains_key(&name) && !self.prov.contains_key(&name) {
                    // Not a known local or parameter: treat as a global write.
                    // (A fresh local would have appeared in a `let`.)
                    self.ws.add_global(name);
                }
                return;
            }
            // `module::STATIC = _`: a global.
            if let Some(seg) = p.path.segments.last() {
                self.ws.add_global(seg.ident.to_string());
            }
            return;
        }
        // A write through a pointer place.
        if let Some(ptr) = self.written_pointer(place) {
            match self.prov_of(ptr) {
                Prov::Param(i) => self.ws.add_param(i),
                Prov::Local => {}
                Prov::Unknown => self.ws.top(),
            }
            return;
        }
        // An unclassifiable place: be conservative.
        self.ws.top();
    }

    fn expr(&mut self, e: &syn::Expr) {
        if self.ws == WriteSet::Top {
            return;
        }
        match e {
            syn::Expr::Assign(a) => {
                self.record_write(&a.left);
                self.expr(&a.right);
            }
            // `&raw mut place` / `&mut place` exposes `place` to a possible
            // write: treat it as written (conservative).
            syn::Expr::Reference(r) if r.mutability.is_some() => {
                self.record_write(&r.expr);
                self.expr(&r.expr);
            }
            _ => self.visit_children(e),
        }
    }

    /// Recurse into subexpressions for nested writes.
    fn visit_children(&mut self, e: &syn::Expr) {
        use syn::visit::Visit;
        struct Sub<'a>(&'a mut Analysis);
        impl<'a, 'ast> Visit<'ast> for Sub<'a> {
            fn visit_expr(&mut self, e: &'ast syn::Expr) {
                // Delegate back to the write-aware handler for assignment-shaped
                // nodes; otherwise keep recursing.
                match e {
                    syn::Expr::Assign(_) | syn::Expr::Reference(_) => self.0.expr(e),
                    _ => syn::visit::visit_expr(self, e),
                }
            }
        }
        Sub(self).visit_expr(e);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ws(src: &str) -> WriteSet {
        let f: syn::ItemFn = syn::parse_str(src).unwrap();
        write_set(&f)
    }

    #[test]
    fn pure_scalar_function_writes_nothing() {
        assert_eq!(ws("fn f(x: i32) -> i32 { x + 1 }"), WriteSet::empty());
    }

    #[test]
    fn write_through_pointer_param_is_recorded() {
        let w = ws("unsafe fn f(p: *mut i32, q: *mut i32) { *p = 1; (*q) = 2; }");
        assert_eq!(
            w,
            WriteSet::Known {
                params: [0, 1].into_iter().collect(),
                globals: Default::default()
            }
        );
    }

    #[test]
    fn write_through_field_and_index_of_param() {
        let w = ws("unsafe fn f(p: *mut S) { (*p).n = 1; *p.offset(2) = 3; }");
        assert_eq!(
            w,
            WriteSet::Known {
                params: [0].into_iter().collect(),
                globals: Default::default()
            }
        );
    }

    #[test]
    fn write_through_param_alias_is_tracked() {
        let w = ws("unsafe fn f(p: *mut i32) { let q = p; *q = 7; }");
        assert_eq!(
            w,
            WriteSet::Known {
                params: [0].into_iter().collect(),
                globals: Default::default()
            }
        );
    }

    #[test]
    fn write_to_global_is_recorded() {
        let w = ws("unsafe fn f() { COUNTER = 5; }");
        assert_eq!(
            w,
            WriteSet::Known {
                params: Default::default(),
                globals: ["COUNTER".to_owned()].into_iter().collect()
            }
        );
    }

    #[test]
    fn write_through_local_allocation_does_not_escape() {
        // A pointer from a modelled allocator is the function's own memory, so
        // the write doesn't escape to the caller.
        let w = ws("unsafe fn f() { let p = malloc(8) as *mut i32; *p = 1; }");
        assert_eq!(w, WriteSet::empty());
    }

    #[test]
    fn write_through_unknown_call_result_is_top() {
        // A pointer from an unknown function could alias caller state.
        let w = ws("unsafe fn f() { let p = make(); *p = 1; }");
        assert_eq!(w, WriteSet::Top);
    }

    #[test]
    fn write_through_unknown_pointer_is_top() {
        let w = ws("unsafe fn f(n: i32) { let p = n as *mut i32; *p = 1; }");
        assert_eq!(w, WriteSet::Top);
    }
}
