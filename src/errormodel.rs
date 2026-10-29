//! Modelling libxml2's central error primitive `__xmlRaiseError` as an
//! observable trace call on the heap path.
//!
//! `__xmlRaiseError` is variadic and can't be given a Rust shim, so each call
//! site is rewritten into a sequence of trace events (the VOC/CoVaC approach
//! already used for `printf` in [`crate::varmodel`]): both versions record the
//! same calls in the same order with the same arguments, so they are equivalent
//! exactly when they report the same errors. This is "error reporting is
//! observable" made concrete.
//!
//! Soundness of treating it as *stateless* (the trace doesn't model its write
//! to the `xmlLastError` global): in this crate nothing reads `xmlLastError`
//! except through the `__xmlLastError()` accessor, which is itself out of scope
//! -- so any unit that would observe the write is excluded anyway, and the
//! write can never feed back into the compared result. Both versions making
//! identical traced calls therefore leave identical real error state.
//!
//! Unlike `printf`, `__xmlRaiseError` has a fixed, structured prefix: two
//! error-handler function pointers and three `*mut c_void` context pointers,
//! then scalars, a `level` enum newtype, and message strings, then the variadic
//! format tail. The five leading pointers are compared by correspondence (trace
//! kind 2, the same bijection as heap-pointer arguments) rather than by raw
//! bits -- passing a different handler or context is a real divergence, but a
//! corresponding pointer with a different address is not. The `level` newtype is
//! recorded by its inner scalar. Everything else (and the variadic tail) is
//! recorded with the compile-time-dispatched [`TraceArg`] -- so a format
//! argument of a pointer type Kani can't compare by content leaves the call
//! unmodelled, exactly as for `printf`.

use quote::ToTokens;
use syn::visit_mut::VisitMut;

/// The pointer-prefix shape of a modelled error external: its leading
/// arguments that are pointers (compared by correspondence, trace kind 2)
/// rather than recorded by [`TraceArg`]. The first `fnptr` are function
/// pointers (usually `None`), the next up to `ptr_end` are `*mut c_void`
/// context pointers, and `level`, if set, names a C-enum-newtype argument
/// recorded by its inner scalar. Everything after the prefix (and the variadic
/// tail) goes through [`TraceArg`].
struct Spec {
    fnptr: usize,
    ptr_end: usize,
    level: Option<usize>,
}

/// The modelled error/diagnostic externals and their argument shapes.
fn spec(name: &str) -> Option<Spec> {
    Some(match name {
        // schannel, channel (fn ptrs), data, ctx, node (void*), ..., level, ...
        "__xmlRaiseError" => Spec { fnptr: 2, ptr_end: 5, level: Some(7) },
        // The generic/validity error printers: `(ctx: *mut c_void, msg, ...)`.
        "xmlGenericErrorDefaultFunc"
        | "xmlParserError"
        | "xmlParserWarning"
        | "xmlParserValidityError"
        | "xmlParserValidityWarning" => Spec { fnptr: 0, ptr_end: 1, level: None },
        _ => return None,
    })
}

/// The error-reporting externals modelled as observable trace calls.
pub fn is_error_fn(name: &str) -> bool {
    spec(name).is_some()
}

/// The thread-local accessors that return a *registered handler* function
/// pointer, which c2rust dispatches as `(*__A()).expect("..")(args)`. Each maps
/// to the trace key (the handler's own name, stable across both versions) and
/// the argument [`Spec`]. The global the accessor returns is a function pointer
/// we never build: the dispatch is modelled directly as an observable trace
/// call keyed by the handler name -- the same observational-equivalence stance
/// as [`is_error_fn`] -- so the accessor and its fn-ptr global drop out of the
/// unit entirely (the extractor skip-descends the accessor call, and this
/// rewrite erases every use of it). `xmlGenericError` has the generic-error
/// printer shape (`ctx: *mut c_void`, then a `printf` format tail); the
/// register-node hooks take one node pointer. All return `()`.
fn handler(accessor: &str) -> Option<(&'static str, Spec)> {
    Some(match accessor {
        "__xmlGenericError" => ("xmlGenericError", Spec { fnptr: 0, ptr_end: 1, level: None }),
        "__xmlStructuredError" => {
            ("xmlStructuredError", Spec { fnptr: 0, ptr_end: 2, level: None })
        }
        "__xmlRegisterNodeDefaultValue" => {
            ("xmlRegisterNodeDefaultValue", Spec { fnptr: 0, ptr_end: 1, level: None })
        }
        "__xmlDeregisterNodeDefaultValue" => {
            ("xmlDeregisterNodeDefaultValue", Spec { fnptr: 0, ptr_end: 1, level: None })
        }
        _ => return None,
    })
}

/// Whether `name` is a modelled handler accessor (see [`handler`]).
pub fn is_handler_accessor(name: &str) -> bool {
    handler(name).is_some()
}

/// Peel `Paren`/`Group` wrappers off an expression.
fn unwrap_group(mut e: &syn::Expr) -> &syn::Expr {
    loop {
        e = match e {
            syn::Expr::Paren(p) => &p.expr,
            syn::Expr::Group(g) => &g.expr,
            _ => return e,
        };
    }
}

/// If `e` is a bare call `__A()` (no arguments) to a modelled handler accessor,
/// that accessor's name.
fn accessor_call_name(e: &syn::Expr) -> Option<String> {
    let syn::Expr::Call(c) = unwrap_group(e) else {
        return None;
    };
    if !c.args.is_empty() {
        return None;
    }
    let syn::Expr::Path(p) = &*c.func else {
        return None;
    };
    let name = p.path.segments.last()?.ident.to_string();
    is_handler_accessor(&name).then_some(name)
}

/// If `e` is `(*__A())` -- a dereference of a handler-accessor call -- that
/// accessor's name.
fn deref_accessor_name(e: &syn::Expr) -> Option<String> {
    let syn::Expr::Unary(u) = unwrap_group(e) else {
        return None;
    };
    if !matches!(u.op, syn::UnOp::Deref(_)) {
        return None;
    }
    accessor_call_name(&u.expr)
}

/// If `call` is a handler dispatch `(*__A()).expect("..")(args)` or
/// `.unwrap()(args)` for a modelled handler accessor `__A`, that accessor's
/// name.
fn handler_dispatch_name(call: &syn::ExprCall) -> Option<String> {
    let syn::Expr::MethodCall(mc) = &*call.func else {
        return None;
    };
    if mc.method != "expect" && mc.method != "unwrap" {
        return None;
    }
    deref_accessor_name(&mc.receiver)
}

/// Whether `call` is a handler dispatch (see [`handler_dispatch_name`]). The
/// eligibility gate admits such a call (it is modelled, not a general indirect
/// call), and this rewrite replaces it.
pub fn is_handler_dispatch(call: &syn::ExprCall) -> bool {
    handler_dispatch_name(call).is_some()
}

/// Whether `call` is a bare handler-accessor call `__A()`. The extractor
/// skip-descends it so the accessor and its fn-ptr global are never pulled into
/// the unit -- this rewrite erases every use of `__A()` (the dispatch and the
/// `.is_some()`/`.is_none()` guards), so nothing references it in the scratch.
pub fn is_handler_accessor_call(call: &syn::ExprCall) -> bool {
    if !call.args.is_empty() {
        return false;
    }
    matches!(&*call.func, syn::Expr::Path(p)
        if p.path.segments.last().is_some_and(|s| is_handler_accessor(&s.ident.to_string())))
}

/// Whether an argument expression is a bare `None` (no type context), which
/// must be recorded as the null pointer word rather than transmuted.
fn is_none(arg: &syn::Expr) -> bool {
    matches!(arg, syn::Expr::Path(p)
        if p.qself.is_none() && p.path.is_ident("None"))
}

/// A stable 64-bit id for a call name (FNV-1a), matching [`crate::varmodel`] so
/// a name maps to one trace id everywhere.
fn id(name: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in name.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Rewrite every call to a modelled error external in these items.
pub fn rewrite(items: &mut [syn::Item]) {
    for item in items {
        Rewrite.visit_item_mut(item);
    }
}

struct Rewrite;

impl VisitMut for Rewrite {
    fn visit_expr_mut(&mut self, e: &mut syn::Expr) {
        // Rewrite inner expressions first (arguments may themselves be calls).
        syn::visit_mut::visit_expr_mut(self, e);
        match e {
            // A direct call to a modelled error external, or an accessor-
            // dispatched registered handler `(*__A()).expect("..")(args)`.
            syn::Expr::Call(call) => {
                if let syn::Expr::Path(p) = &*call.func {
                    if p.path.segments.len() == 1 {
                        let name = p.path.segments[0].ident.to_string();
                        if let Some(sp) = spec(&name) {
                            *e = syn::parse_str(&block(&name, &sp, &call.args))
                                .expect("error trace block parses");
                            return;
                        }
                    }
                }
                if let Some(accessor) = handler_dispatch_name(call) {
                    let (key, sp) = handler(&accessor).expect("handler accessor");
                    *e = syn::parse_str(&block(key, &sp, &call.args))
                        .expect("handler trace block parses");
                }
            }
            // A handler presence guard `(*__A()).is_some()` / `.is_none()`:
            // the handler is modelled as registered, so these fold to the
            // constant, erasing the last reference to the accessor. A dead
            // guarded dispatch (e.g. the register-node hooks, gated by the
            // default-zero `__xmlRegisterCallbacks`) stays dead; a live one is
            // traced -- either way sound.
            syn::Expr::MethodCall(mc)
                if (mc.method == "is_some" || mc.method == "is_none")
                    && deref_accessor_name(&mc.receiver).is_some() =>
            {
                let v = if mc.method == "is_some" { "true" } else { "false" };
                *e = syn::parse_str(v).expect("bool literal parses");
            }
            _ => {}
        }
    }
}

/// The replacement block: bind each argument, record it as a trace event (the
/// leading pointers by correspondence, the level newtype by its inner scalar,
/// the rest by [`TraceArg`]), and yield unit (the call returns `()`).
fn block(
    name: &str,
    sp: &Spec,
    args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
) -> String {
    let call_id = id(name);
    let mut binds = String::new();
    let mut steps = String::new();
    for (i, arg) in args.iter().enumerate() {
        if i < sp.ptr_end {
            // A handler or context pointer: compared by correspondence (kind 2),
            // so a different handler/context is caught but a corresponding
            // pointer with a different address is not.
            let word = if is_none(arg) {
                // A bare `None` (the common "no handler") has no type once
                // rebound; record it as the null word directly.
                "0u128".to_owned()
            } else if i < sp.fnptr {
                // A real (typed) function pointer transmutes to its address.
                binds += &format!("let __a{i} = {};\n", arg.to_token_stream());
                format!("core::mem::transmute::<_, usize>(__a{i}) as u128")
            } else {
                // A context/handle pointer: cast to `*mut c_void` so an untyped
                // `null_mut()`, a `*mut c_void`, or a typed pointer (e.g. a
                // register-node hook's `xmlNodePtr`) all coerce, then take its
                // address word. Compared by correspondence, so the exact pointee
                // type is irrelevant.
                binds += &format!(
                    "let __a{i}: *mut core::ffi::c_void = ({}) as *mut core::ffi::c_void;\n",
                    arg.to_token_stream()
                );
                format!("__a{i} as usize as u128")
            };
            steps += &format!("(*__t).step({call_id}u64, [{word}, 0, 0], [2u8, 3u8, 3u8]);\n");
            continue;
        }
        binds += &format!("let __a{i} = {};\n", arg.to_token_stream());
        if sp.level == Some(i) {
            // The `level` C-enum newtype: record its inner scalar by value.
            steps += &format!(
                "(*__t).step({call_id}u64, \
                 [crate::support::TraceArg::bits(&(__a{i}.0)), 0, 0], \
                 [crate::support::TraceArg::kind(&(__a{i}.0)), 3u8, 3u8]);\n"
            );
        } else {
            steps += &format!(
                "(*__t).step({call_id}u64, \
                 [crate::support::TraceArg::bits(&__a{i}), 0, 0], \
                 [crate::support::TraceArg::kind(&__a{i}), 3u8, 3u8]);\n"
            );
        }
    }
    let ret_id = call_id.wrapping_add(1);
    format!(
        "{{ let __t = core::ptr::addr_of_mut!(crate::support::TRACE); {binds} {steps} \
         let _ = (*__t).step({ret_id}u64, [0, 0, 0], [3u8, 3u8, 3u8]); }}"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn items(src: &str) -> Vec<syn::Item> {
        syn::parse_file(src).unwrap().items
    }

    #[test]
    fn rewrites_raise_error_into_trace_events() {
        let mut it = items(
            "pub unsafe fn f(node: *mut core::ffi::c_void, domain: i32) { \
             __xmlRaiseError(None, None, core::ptr::null_mut(), core::ptr::null_mut(), \
             node, domain, 2i32, xmlErrorLevel::XML_ERR_FATAL, \
             core::ptr::null(), 0i32, core::ptr::null(), core::ptr::null(), \
             core::ptr::null(), 0i32, 0i32, b\"m\\0\".as_ptr() as *const i8); }",
        );
        rewrite(&mut it);
        let src = it
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(!src.contains("__xmlRaiseError ("), "call should be gone: {src}");
        assert!(src.contains("TRACE"), "{src}");
        // The three `*mut c_void` context pointers recorded by address word.
        assert!(src.contains("as usize"), "{src}");
        // The level newtype recorded by its inner scalar.
        assert!(src.contains(". 0"), "level inner scalar: {src}");
    }

    #[test]
    fn leaves_other_calls_untouched() {
        let mut it = items("pub unsafe fn f() { some_other_fn(1, 2); }");
        rewrite(&mut it);
        let src = it
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(src.contains("some_other_fn"), "{src}");
        assert!(!src.contains("TRACE"), "{src}");
    }
}
