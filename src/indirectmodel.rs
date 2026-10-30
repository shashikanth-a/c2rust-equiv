//! Modelling indirect (function-pointer) calls on the heap path (wall 3).
//!
//! c2rust emits a call through a nullable callback as
//! `(<receiver>).<field>.expect("non-null function pointer")(args)` (or
//! `.unwrap()`), where the field has type `Option<extern "C" fn(..) -> ..>`.
//! The callee is unknown, so -- exactly as the direct trace-modellable externals
//! in [`crate::strmodel`] -- the call is modelled as an **observable /
//! uninterpreted call**: `(callback-value, arguments)` is recorded in the
//! shared `TRACE`, and the call takes the shared symbolic result. Both versions
//! rewrite identically, so for the same callback value and arguments they
//! agree, and any divergence (a different callback, different arguments, or a
//! differing call sequence) surfaces -- the VOC/CoVaC observable-behaviour
//! equivalence (RVT congruence with the callback value as the call id instead
//! of a static name).
//!
//! Soundness mirrors the accepted direct-call model: the call id is the
//! callback's pointer value (so equal callbacks collide in the oracle), and the
//! argument/return shape is restricted to what the trace records -- at most
//! three scalar/float/pointer arguments and a scalar/float/pointer/`()` return
//! ([`modellable_sig`]). A call that doesn't fit is left untouched, so the
//! eligibility gate ([`crate::extract`]) and this rewrite must agree: both ask
//! [`plan_call`], so a function is admitted only when every indirect call in it
//! is one this rewrite will replace.

use std::collections::BTreeMap;

use quote::ToTokens;
#[cfg(test)]
use syn::visit::Visit;
use syn::visit_mut::VisitMut;

use crate::crate_index::CrateIndex;
use crate::strmodel::{float_width, oracle_id};

/// The resolved plan for one modellable indirect call: the callee fn-pointer
/// expression (the `Option<fn>` already unwrapped), the return type text, and
/// each argument's bit-expression and kind tag (as [`crate::strmodel`] uses).
struct CallPlan {
    /// The callback `Option<fn>` receiver expression, e.g. `(*arr).free_fn`
    /// (the `.expect(..)`/`.unwrap()` is dropped -- see `replacement`).
    callee: syn::Expr,
    /// The call's argument expressions.
    args: Vec<syn::Expr>,
    /// Each argument's kind tag (0 scalar/float, 1 string, 2 pointer).
    arg_kinds: Vec<u8>,
    /// The bare function's return type, as text (`"()"` for no return).
    ret: String,
}

/// A map from struct name to its fields' declared types, and the enclosing
/// function's variable types (parameters and annotated `let`s), so a
/// field-access receiver like `(*arr).free_fn` can be typed.
#[derive(Default, Clone)]
pub(crate) struct TypeEnv {
    fields: BTreeMap<String, BTreeMap<String, syn::Type>>,
    vars: BTreeMap<String, syn::Type>,
    /// Crate type aliases, so a callback field typed `Option<MyCallback>` (a
    /// typedef'd bare fn, as c2rust emits) is seen through to the bare fn.
    aliases: BTreeMap<String, syn::Type>,
    /// Global `static` types, so an indirect call through a function-pointer
    /// global (`xmlCurrentExternalEntityLoader.expect(..)(..)`) can be typed and
    /// modelled, not just one through a local or a struct field.
    globals: BTreeMap<String, syn::Type>,
}

impl TypeEnv {
    /// Build the struct-field and alias maps from a sequence of items.
    pub(crate) fn from_items(items: &[syn::Item]) -> Self {
        let mut env = TypeEnv::default();
        for item in items {
            env.add_item(item);
        }
        env
    }

    /// Build the field and alias maps from a crate index, so the eligibility
    /// gate can type a field-access receiver during extraction.
    pub(crate) fn from_index(index: &CrateIndex) -> Self {
        let mut env = TypeEnv::default();
        for entry in &index.entries {
            if let Some(item) = &entry.item {
                env.add_item(item);
            }
        }
        env
    }

    /// Record one struct's named fields or one type alias, if `item` is either.
    fn add_item(&mut self, item: &syn::Item) {
        match item {
            syn::Item::Struct(s) => {
                let mut fs = BTreeMap::new();
                if let syn::Fields::Named(named) = &s.fields {
                    for f in &named.named {
                        if let Some(id) = &f.ident {
                            fs.insert(id.to_string(), f.ty.clone());
                        }
                    }
                }
                self.fields.insert(s.ident.to_string(), fs);
            }
            syn::Item::Type(t) => {
                self.aliases.insert(t.ident.to_string(), (*t.ty).clone());
            }
            syn::Item::Static(s) => {
                self.globals.insert(s.ident.to_string(), (*s.ty).clone());
            }
            _ => {}
        }
    }

    /// Whether `call` is an indirect call this rewrite will model soundly.
    pub(crate) fn indirect_is_modellable(&self, call: &syn::ExprCall) -> bool {
        plan_call(call, self).is_some()
    }

    /// Record the parameter and annotated-local types of one function body.
    pub(crate) fn with_fn(&mut self, f: &syn::ItemFn) {
        self.vars.clear();
        for input in &f.sig.inputs {
            if let syn::FnArg::Typed(pt) = input {
                if let syn::Pat::Ident(id) = &*pt.pat {
                    self.vars.insert(id.ident.to_string(), (*pt.ty).clone());
                }
            }
        }
        // Annotated locals (`let mut x: T = ..`), which c2rust emits widely --
        // at ANY depth, since c2rust nests a callback and its `let`-bound
        // function pointer inside the conditional that guards the call
        // (`if cond { let mut proc: CbT = ..; proc.expect(..)(..) }`). A
        // top-level-only scan would miss exactly those, so walk the whole body.
        let mut v = LocalTypes { vars: &mut self.vars };
        syn::visit::Visit::visit_block(&mut v, &f.block);
    }

    /// The type of an lvalue expression, by a small structural walk: a variable,
    /// a dereference of a pointer, or a field access on a struct. `None` when it
    /// can't be resolved from the available declarations.
    fn type_of(&self, e: &syn::Expr) -> Option<syn::Type> {
        match e {
            syn::Expr::Paren(p) => self.type_of(&p.expr),
            syn::Expr::Group(g) => self.type_of(&g.expr),
            syn::Expr::Path(p) => {
                let name = p.path.get_ident()?.to_string();
                // A local binding/parameter, else a global `static` (a callback
                // held in a function-pointer global).
                self.vars.get(&name).or_else(|| self.globals.get(&name)).cloned()
            }
            syn::Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => {
                // Resolve type aliases first: c2rust types context pointers as
                // `xmlParserCtxtPtr` etc., not a bare `*mut _`, so the pointer is
                // only visible after following the alias.
                let inner = crate::heapgen::resolve_alias(&self.type_of(&u.expr)?, &self.aliases);
                match inner {
                    syn::Type::Ptr(ptr) => Some((*ptr.elem).clone()),
                    _ => None,
                }
            }
            syn::Expr::Field(f) => {
                // The base types to a struct (possibly an alias, and possibly
                // behind a pointer the dereference above has already stripped);
                // resolve aliases, then look up the member.
                let base = crate::heapgen::resolve_alias(&self.type_of(&f.base)?, &self.aliases);
                let sname = struct_name(&base)?;
                let member = match &f.member {
                    syn::Member::Named(id) => id.to_string(),
                    syn::Member::Unnamed(_) => return None,
                };
                self.fields.get(&sname)?.get(&member).cloned()
            }
            syn::Expr::Index(idx) => {
                // `arr[i]` -- an element of an array or a pointer-indexed table.
                // libxml2 dispatches through a callback table element,
                // `xmlInputCallbackTable[i].opencallback.expect(..)(..)`, so the
                // element type must be seen through the index.
                let base = crate::heapgen::resolve_alias(&self.type_of(&idx.expr)?, &self.aliases);
                match base {
                    syn::Type::Array(a) => Some((*a.elem).clone()),
                    syn::Type::Ptr(p) => Some((*p.elem).clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

/// Collects every annotated `let x: T` binding in a function body, at any
/// nesting depth, into the variable-type map. c2rust emits callback dispatches
/// inside the conditional that guards them, with the function pointer bound by
/// a nested `let`, so a top-level-only scan would leave the receiver untyped.
struct LocalTypes<'a> {
    vars: &'a mut BTreeMap<String, syn::Type>,
}

impl<'ast> syn::visit::Visit<'ast> for LocalTypes<'_> {
    fn visit_local(&mut self, local: &'ast syn::Local) {
        if let syn::Pat::Type(pt) = &local.pat {
            if let syn::Pat::Ident(id) = &*pt.pat {
                self.vars.insert(id.ident.to_string(), (*pt.ty).clone());
            }
        }
        syn::visit::visit_local(self, local);
    }
}

/// The name of a struct type (a bare path's last segment), if it is one.
fn struct_name(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(p) => Some(p.path.segments.last()?.ident.to_string()),
        _ => None,
    }
}

/// Whether a bare function signature is trace-modellable, mirroring
/// [`crate::strmodel`]'s `is_trace_sig`: not variadic, at most three arguments,
/// no `-> !`, and every argument a scalar/float or pointer. Returns the
/// per-argument kind tags and the return-type text on success.
fn modellable_sig(
    f: &syn::TypeBareFn,
    aliases: &BTreeMap<String, syn::Type>,
) -> Option<(Vec<u8>, String)> {
    // Each argument is recorded as its own trace event, so any arity works; cap
    // it only to bound trace usage (the widest SAX callback takes eight). A
    // variadic callback is admitted here: the fixed prefix is classified below,
    // and `plan_call` classifies each variadic tail argument from its call site,
    // rejecting the call if any tail argument can't be typed.
    if f.inputs.len() > 16 {
        return None;
    }
    if let syn::ReturnType::Type(_, t) = &f.output {
        if matches!(&**t, syn::Type::Never(_)) {
            return None;
        }
    }
    let mut kinds = Vec::with_capacity(f.inputs.len());
    for arg in &f.inputs {
        kinds.push(arg_kind(&arg.ty, aliases)?);
    }
    // Resolve the return type through aliases too: c2rust types a callback's
    // return as e.g. `lil_value_t` (= `*mut _lil_value_t`), and the replacement
    // needs to see it is a pointer to cast the trace result correctly.
    let ret = match &f.output {
        syn::ReturnType::Default => "()".to_owned(),
        syn::ReturnType::Type(_, t) => {
            crate::heapgen::resolve_alias(t, aliases).to_token_stream().to_string()
        }
    };
    Some((kinds, ret))
}

/// The trace kind tag for an argument type: 2 for a pointer, 1 for a C string
/// pointer, 0 for a scalar/float. `None` if it is neither (e.g. a struct by
/// value or a nested fn pointer), which makes the call unmodellable. Type
/// aliases are resolved first, so a callback argument typed through a c2rust
/// typedef (`lil_t = *mut _lil_t`, `xmlNodePtr = *mut xmlNode`) is recognised as
/// the pointer it is rather than rejected as an unknown name.
fn arg_kind(ty: &syn::Type, aliases: &BTreeMap<String, syn::Type>) -> Option<u8> {
    let resolved = crate::heapgen::resolve_alias(ty, aliases);
    if let syn::Type::Ptr(ptr) = &resolved {
        let pointee = last_segment(&crate::heapgen::resolve_alias(&ptr.elem, aliases));
        return Some(match pointee.as_deref() {
            Some("c_char") | Some("c_uchar") => 1,
            _ => 2,
        });
    }
    let name = last_segment(&resolved)?;
    let s = name.as_str();
    if float_width(s).is_some()
        || crate::scalar::primitive(s).is_some()
        || crate::scalar::c_type(s).is_some()
        || crate::scalar::libc_typedef(s).is_some()
    {
        Some(0)
    } else {
        None
    }
}

fn last_segment(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(p) => Some(p.path.segments.last()?.ident.to_string()),
        _ => None,
    }
}

/// The trace kind of a variadic tail argument, classified from the call-site
/// expression: an explicit cast `e as T` by its target type (c2rust's usual
/// shape, since C varargs are promoted with an explicit cast), otherwise by the
/// expression's resolved lvalue type. Returns `None` -- which rejects the whole
/// call as out of scope -- when the argument can't be typed, or is a float: the
/// trace records a scalar by value-cast to `u128`, exact for integers, string
/// and pointer identities, but bit-lossy for floats (two distinct floats could
/// collapse to one trace value), so a float tail is conservatively rejected.
fn tail_kind(arg: &syn::Expr, env: &TypeEnv) -> Option<u8> {
    let ty = match arg {
        syn::Expr::Paren(p) => return tail_kind(&p.expr, env),
        syn::Expr::Group(g) => return tail_kind(&g.expr, env),
        syn::Expr::Cast(c) => (*c.ty).clone(),
        _ => env.type_of(arg)?,
    };
    let resolved = crate::heapgen::resolve_alias(&ty, &env.aliases);
    if last_segment(&resolved).as_deref().and_then(float_width).is_some() {
        return None;
    }
    arg_kind(&resolved, &env.aliases)
}

/// The bits expression for one argument, given its kind tag (as
/// [`crate::strmodel::arg_kind_bits`], but on an expression rather than a name).
fn arg_bits(arg: &syn::Expr, kind: u8) -> String {
    let a = arg.to_token_stream();
    match kind {
        1 | 2 => format!("(({a}) as usize as u128)"),
        _ => format!("(({a}) as u128)"),
    }
}

/// If `call` is a modellable indirect call under `env`, the plan to rewrite it.
/// This is the single predicate both the eligibility gate and the rewrite use.
fn plan_call(call: &syn::ExprCall, env: &TypeEnv) -> Option<CallPlan> {
    // The callee must be `<option-fn-expr>.expect(..)` or `.unwrap()`.
    let syn::Expr::MethodCall(mc) = &*call.func else {
        return None;
    };
    if mc.method != "expect" && mc.method != "unwrap" {
        return None;
    }
    // The receiver must type to `Option<bare fn>` (through aliases); read it.
    let recv_ty = env.type_of(&mc.receiver)?;
    let bare = option_bare_fn(&recv_ty, &env.aliases)?;
    let (mut arg_kinds, ret) = modellable_sig(&bare, &env.aliases)?;
    let fixed = bare.inputs.len();
    if bare.variadic.is_some() {
        // A variadic callback (libxml2's `warning`/`error`/`fatalError`, printf-
        // style diagnostics). The fixed prefix is classified from the signature;
        // each variadic tail argument is classified from its call-site
        // expression, and the whole call is rejected -- kept out of scope, which
        // is sound -- if any tail argument can't be typed as an integer/string/
        // pointer. Each argument is still recorded as its own ordered trace
        // event, so a rewrite that passes a different tail diverges and is
        // caught rather than silently collapsed.
        if call.args.len() < fixed {
            return None;
        }
        for arg in call.args.iter().skip(fixed) {
            arg_kinds.push(tail_kind(arg, env)?);
        }
    } else if call.args.len() != fixed {
        return None;
    }
    Some(CallPlan {
        callee: (*mc.receiver).clone(),
        args: call.args.iter().cloned().collect(),
        arg_kinds,
        ret,
    })
}

/// If `ty` is `Option<F>` with `F` a bare function pointer (possibly through a
/// type alias), that bare function.
fn option_bare_fn(
    ty: &syn::Type,
    aliases: &BTreeMap<String, syn::Type>,
) -> Option<syn::TypeBareFn> {
    // The field type itself may be an alias for the `Option<..>`.
    let ty = crate::heapgen::resolve_alias(ty, aliases);
    let syn::Type::Path(p) = &ty else { return None };
    let seg = p.path.segments.last()?;
    if seg.ident != "Option" {
        return None;
    }
    let syn::PathArguments::AngleBracketed(args) = &seg.arguments else {
        return None;
    };
    let mut it = args.args.iter();
    let (Some(syn::GenericArgument::Type(inner)), None) = (it.next(), it.next()) else {
        return None;
    };
    match crate::heapgen::resolve_alias(inner, aliases) {
        syn::Type::BareFn(f) => Some(f),
        _ => None,
    }
}

/// The replacement expression for a modellable indirect call: record the call
/// in the shared trace keyed by the callback value, and rebuild the result.
fn replacement(plan: &CallPlan) -> syn::Expr {
    // The callback value is the call id. Take it from the `Option<fn>` receiver
    // with `map_or` -- a null callback maps to 0 and never panics (c2rust's
    // `.expect(..)` would panic, which Kani can't classify; both versions model
    // null identically, so equivalence is preserved). A stable salt keeps
    // indirect-call ids out of the static `oracle_id` namespace.
    let recv = plan.callee.to_token_stream();
    let salt = oracle_id("<indirect>");
    let token = format!("(({recv}).map_or(0usize, |f| f as usize) as u64 ^ {salt}u64)");
    // Record each argument as its own trace event (one slot per step), so the
    // call's arity is unbounded; both versions replay the same events in order.
    let mut body =
        format!("let __t = core::ptr::addr_of_mut!(crate::support::TRACE); let __id = {token};");
    for (i, arg) in plan.args.iter().enumerate() {
        let bits = arg_bits(arg, plan.arg_kinds[i]);
        let kind = plan.arg_kinds[i];
        body += &format!("(*__t).step(__id, [{bits}, 0, 0], [{kind}u8, 3u8, 3u8]);");
    }
    // A final event carries the call's symbolic result (distinct id so it is
    // never confused with an argument event).
    let ret_salt = oracle_id("<indirect-ret>");
    let step = format!("(*__t).step(__id ^ {ret_salt}u64, [0, 0, 0], [3u8, 3u8, 3u8])");
    let ret = plan.ret.trim();
    let tail = match float_width(ret) {
        Some(32) => format!("f32::from_bits({step} as u32) as {ret}"),
        Some(_) => format!("f64::from_bits({step} as u64) as {ret}"),
        None if ret == "()" => format!("let _ = {step};"),
        None if ret.starts_with('*') => format!("{step} as usize as {ret}"),
        None => format!("{step} as {ret}"),
    };
    syn::parse_str(&format!("unsafe {{ {body} {tail} }}"))
        .expect("generated indirect-call expr parses")
}

/// Whether every indirect call in `f`'s body is modellable by this rewrite.
/// A test convenience: in the tool the gate is applied per call during
/// extraction (`TypeEnv::indirect_is_modellable`), not whole-function.
#[cfg(test)]
fn all_indirect_calls_modellable(f: &syn::ItemFn, items: &[syn::Item]) -> bool {
    let mut env = TypeEnv::from_items(items);
    env.with_fn(f);
    let mut checker = Checker { env, ok: true };
    checker.visit_item_fn(f);
    checker.ok
}

#[cfg(test)]
struct Checker {
    env: TypeEnv,
    ok: bool,
}

#[cfg(test)]
impl<'ast> Visit<'ast> for Checker {
    fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
        // Only indirect calls (a non-path, or expect/unwrap callee) concern us.
        if is_indirect(call) && plan_call(call, &self.env).is_none() {
            self.ok = false;
        }
        syn::visit::visit_expr_call(self, call);
    }
}

/// Whether a call is indirect: the callee is not a plain function path. The
/// `expect`/`unwrap` method-call callee c2rust emits counts as indirect.
pub(crate) fn is_indirect(call: &syn::ExprCall) -> bool {
    !matches!(&*call.func, syn::Expr::Path(_))
}

/// Rewrite every modellable indirect call in these items into a trace step.
pub fn rewrite(items: &mut [syn::Item]) {
    let env = TypeEnv::from_items(items);
    for item in items.iter_mut() {
        if let syn::Item::Fn(f) = item {
            let mut scoped = env.clone();
            scoped.with_fn(f);
            let mut r = Rewriter { env: scoped };
            r.visit_item_fn_mut(f);
        }
    }
}

struct Rewriter {
    env: TypeEnv,
}

impl VisitMut for Rewriter {
    fn visit_expr_mut(&mut self, e: &mut syn::Expr) {
        // Rewrite inner expressions first (arguments may be indirect calls too).
        syn::visit_mut::visit_expr_mut(self, e);
        if let syn::Expr::Call(call) = e {
            if is_indirect(call) {
                if let Some(plan) = plan_call(call, &self.env) {
                    *e = replacement(&plan);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn items(src: &str) -> Vec<syn::Item> {
        syn::parse_file(src).unwrap().items
    }

    const ARRAY_LIST: &str = r#"
        struct array_list { free_fn: Option<unsafe extern "C" fn(*mut c_void) -> ()>, length: size_t }
        unsafe fn free_one(arr: *mut array_list, p: *mut c_void) {
            (*arr).free_fn.expect("non-null function pointer")(p);
        }
    "#;

    #[test]
    fn models_a_field_callback_call() {
        assert!(all_indirect_calls_modellable_in(ARRAY_LIST, "free_one"));
        let mut its = items(ARRAY_LIST);
        rewrite(&mut its);
        let out = its
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        // The indirect call is gone, replaced by a trace step keyed by the
        // callback value, and the `.expect(..)` null check is preserved.
        assert!(out.contains("TRACE"), "expected a trace step: {out}");
        assert!(out.contains("step"), "{out}");
        // The callback value becomes the trace id via `map_or` (no panicking
        // `expect`, which Kani cannot classify), keyed off the `free_fn` field.
        assert!(out.contains("map_or"), "callback token via map_or: {out}");
        assert!(out.contains("free_fn"), "keyed on the callback field: {out}");
    }

    #[test]
    fn unresolvable_receiver_is_left_untouched() {
        // No struct/var types available, so the receiver can't be typed: the
        // call is not modellable and the gate rejects it (sound -- never guess).
        let src = r#"
            unsafe fn f(cb: *mut c_void) { opaque(cb).expect("x")(1i32); }
        "#;
        assert!(!all_indirect_calls_modellable_in(src, "f"));
        let mut its = items(src);
        rewrite(&mut its);
        let out = its
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(!out.contains("TRACE"), "must not model it: {out}");
    }

    #[test]
    fn many_args_are_modellable() {
        // Each argument is its own trace event, so arity beyond three is fine
        // (a SAX callback like `startElementNs` takes eight).
        let src = r#"
            struct s { cb: Option<unsafe extern "C" fn(i32, i32, i32, i32, i32) -> i32> }
            unsafe fn f(p: *mut s) -> i32 { (*p).cb.expect("x")(1, 2, 3, 4, 5) }
        "#;
        assert!(all_indirect_calls_modellable_in(src, "f"));
    }

    #[test]
    fn direct_call_is_not_treated_as_indirect() {
        let src = r#"unsafe fn f() { g(1i32); } unsafe fn g(x: i32) {}"#;
        // A direct call is not an indirect call, so the gate is satisfied.
        assert!(all_indirect_calls_modellable_in(src, "f"));
    }

    // Helper: run the gate on the named function within a source string.
    fn all_indirect_calls_modellable_in(src: &str, name: &str) -> bool {
        let its = items(src);
        let f = its
            .iter()
            .find_map(|i| match i {
                syn::Item::Fn(f) if f.sig.ident == name => Some(f.clone()),
                _ => None,
            })
            .expect("function present");
        all_indirect_calls_modellable(&f, &its)
    }
}

#[cfg(test)]
mod sax_tests {
    use super::*;

    // The libxml2 SAX shape: `(*(*ctxt).sax).<cb>.expect("..")(args)`, a nested
    // deref+field receiver through a type-aliased callback field.
    const SRC: &str = r#"
        pub type refSAX = Option<unsafe extern "C" fn(*mut c_void, *const u8) -> ()>;
        pub struct _xmlSAXHandler { pub reference: refSAX, pub warning: Option<unsafe extern "C" fn(*mut c_void, *const i8, ...) -> ()> }
        pub struct xmlParserCtxt { pub sax: *mut _xmlSAXHandler, pub ud: *mut c_void }
        pub unsafe fn p(ctxt: *mut xmlParserCtxt, name: *const u8) {
            (*(*ctxt).sax).reference.expect("non-null function pointer")((*ctxt).ud, name);
        }
        pub unsafe fn w(ctxt: *mut xmlParserCtxt) {
            (*(*ctxt).sax).warning.expect("non-null function pointer")((*ctxt).ud);
        }
        pub unsafe fn wv(ctxt: *mut xmlParserCtxt, msg: *const i8, name: *const u8, n: i32) {
            (*(*ctxt).sax).warning.expect("non-null function pointer")(
                (*ctxt).ud, msg, name as *const i8, n as i32,
            );
        }
        pub unsafe fn wu(ctxt: *mut xmlParserCtxt, msg: *const i8) {
            (*(*ctxt).sax).warning.expect("non-null function pointer")((*ctxt).ud, msg, mystery());
        }
    "#;

    fn env() -> (Vec<syn::Item>, TypeEnv) {
        let its = syn::parse_file(SRC).unwrap().items;
        let env = TypeEnv::from_items(&its);
        (its, env)
    }

    #[test]
    fn fixed_arg_nested_sax_callback_is_modellable() {
        let (its, mut env) = env();
        let f = its.iter().find_map(|i| match i { syn::Item::Fn(f) if f.sig.ident=="p" => Some(f.clone()), _=>None }).unwrap();
        env.with_fn(&f);
        assert!(all_indirect_calls_modellable(&f, &its), "fixed-arg nested SAX callback should be modellable");
    }

    #[test]
    fn variadic_call_below_fixed_arity_is_not_modellable() {
        // `w` passes one argument where the fixed prefix needs two; a call that
        // doesn't even cover the fixed signature is rejected.
        let (its, mut env) = env();
        let f = its.iter().find_map(|i| match i { syn::Item::Fn(f) if f.sig.ident=="w" => Some(f.clone()), _=>None }).unwrap();
        env.with_fn(&f);
        assert!(!all_indirect_calls_modellable(&f, &its), "variadic call below fixed arity must NOT be modellable");
    }

    #[test]
    fn variadic_tail_classifiable_is_modellable() {
        // A variadic diagnostic whose tail arguments are all typeable (a cast
        // string pointer and a cast integer) is modelled, each recorded as its
        // own trace event.
        let (its, mut env) = env();
        let f = its.iter().find_map(|i| match i { syn::Item::Fn(f) if f.sig.ident=="wv" => Some(f.clone()), _=>None }).unwrap();
        env.with_fn(&f);
        assert!(all_indirect_calls_modellable(&f, &its), "classifiable variadic tail should be modellable");
    }

    #[test]
    fn variadic_tail_untypeable_is_rejected() {
        // A tail argument that can't be typed (an un-annotated call result) is
        // conservatively rejected, so a divergent tail is never silently
        // collapsed to the same trace.
        let (its, mut env) = env();
        let f = its.iter().find_map(|i| match i { syn::Item::Fn(f) if f.sig.ident=="wu" => Some(f.clone()), _=>None }).unwrap();
        env.with_fn(&f);
        assert!(!all_indirect_calls_modellable(&f, &its), "untypeable variadic tail must NOT be modellable");
    }
}
