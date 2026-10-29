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
        let syn::Expr::Call(call) = e else { return };
        let syn::Expr::Path(p) = &*call.func else { return };
        let Some(name) = p.path.segments.last().map(|s| s.ident.to_string()) else {
            return;
        };
        if p.path.segments.len() != 1 || !is_error_fn(&name) {
            return;
        }
        *e = syn::parse_str(&block(&name, &call.args)).expect("error trace block parses");
    }
}

/// The replacement block: bind each argument, record it as a trace event (the
/// leading pointers by correspondence, the level newtype by its inner scalar,
/// the rest by [`TraceArg`]), and yield unit (the call returns `()`).
fn block(
    name: &str,
    args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
) -> String {
    let sp = spec(name).expect("modelled error fn");
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
                // A `*mut c_void` context pointer: annotate so an untyped
                // `null_mut()` or a cast coerces, then take its address word.
                binds += &format!(
                    "let __a{i}: *mut core::ffi::c_void = {};\n",
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
