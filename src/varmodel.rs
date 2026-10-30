//! Modelling variadic I/O calls (`printf`, `fprintf`, …) on the heap path.
//!
//! These can't be given a Rust shim (a variadic function's arguments can't be
//! read portably on the verifier's toolchain), so instead each *call site* is
//! rewritten into a sequence of observable trace events: the call records its
//! arguments (each via the `TraceArg` trait, which resolves the type at compile
//! time -- strings by content, scalars by value) and takes a shared symbolic
//! result. Both versions rewrite identically, so they are equivalent exactly
//! when they make the same formatted calls with the same arguments -- the
//! observable-behaviour equivalence the literature uses for I/O.
//!
//! Only output-to-stream functions are handled (no caller buffer to model);
//! `sprintf`/`snprintf`, which format into a destination buffer, need that
//! buffer's output modelled and are not covered here.

use quote::ToTokens;
use syn::visit_mut::VisitMut;

/// The variadic output functions modelled, with their return type.
fn variadic_ret(name: &str) -> Option<&'static str> {
    Some(match name {
        "printf" | "fprintf" | "vprintf" | "vfprintf" | "dprintf" | "vdprintf" => {
            "::core::ffi::c_int"
        }
        "syslog" | "vsyslog" => "()",
        // Variadic input parsers (`sscanf(buf, fmt, &a, &b, ..)`) and the
        // `open`/`fcntl` syscalls, modelled as observable trace calls: every
        // argument -- including the output pointers, by heap-bijection identity
        // -- is recorded, and a shared symbolic result is returned. The output
        // locations are NOT written (left at their symbolic pre-call state), so
        // a function that relies on the parsed value proves nothing unsoundly:
        // both versions see the identical (unmodelled) outcome, and any use
        // that genuinely diverges is caught by the recorded arguments and the
        // heap comparison. This is conservative (it may fail to prove a true
        // equivalence), never a false proof.
        "sscanf" | "fscanf" | "vsscanf" | "vfscanf" | "__isoc99_sscanf" | "__isoc99_fscanf" => {
            "::core::ffi::c_int"
        }
        "open" | "openat" | "fcntl" => "::core::ffi::c_int",
        _ => return None,
    })
}

/// A formatting function that writes into a destination buffer (the argument at
/// the given index), rather than to a stream. Its output is modelled as a
/// shared symbolic string. Returns the destination argument index.
fn variadic_dst(name: &str) -> Option<usize> {
    match name {
        "sprintf" | "vsprintf" | "snprintf" | "vsnprintf" => Some(0),
        // libxml2's `xmlStrPrintf(buf, len, msg, ...)` formats into `buf`.
        "xmlStrPrintf" => Some(0),
        _ => None,
    }
}

/// Whether a call to `name` is a modelled variadic external.
pub fn is_variadic_modelled(name: &str) -> bool {
    variadic_ret(name).is_some() || variadic_dst(name).is_some()
}

/// A stable 64-bit id for a call name (FNV-1a), matching `strmodel::oracle_id`
/// so a name maps to one trace id everywhere.
fn id(name: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in name.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Rewrite every call to a modelled variadic external in these items.
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
        let syn::Expr::Path(p) = &*call.func else {
            return;
        };
        let Some(name) = p.path.segments.last().map(|s| s.ident.to_string()) else {
            return;
        };
        if p.path.segments.len() != 1 || !is_variadic_modelled(&name) {
            return;
        }
        let src = match variadic_dst(&name) {
            Some(dst) => dst_block(&name, dst, &call.args),
            None => block(&name, variadic_ret(&name).unwrap(), &call.args),
        };
        *e = syn::parse_str(&src).expect("variadic trace block parses");
    }
}

/// The replacement block for a buffer-writing formatter (`sprintf` etc.):
/// record every argument but the destination, then fill the destination with
/// the shared symbolic output.
fn dst_block(
    name: &str,
    dst_idx: usize,
    args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
) -> String {
    let call_id = id(name);
    let mut binds = String::new();
    let mut steps = String::new();
    let mut dst_bind = String::from("core::ptr::null_mut()");
    for (i, arg) in args.iter().enumerate() {
        binds += &format!("let __a{i} = {};\n", arg.to_token_stream());
        if i == dst_idx {
            dst_bind = format!("__a{i} as *mut core::ffi::c_char");
        } else {
            steps += &format!(
                "(*__t).step({call_id}u64, \
                 [crate::support::TraceArg::bits(&__a{i}), 0, 0], \
                 [crate::support::TraceArg::kind(&__a{i}), 3u8, 3u8]);\n"
            );
        }
    }
    let fill_id = call_id.wrapping_add(2);
    let ret_id = call_id.wrapping_add(1);
    format!(
        "{{ let __t = core::ptr::addr_of_mut!(crate::support::TRACE); {binds} {steps} \
         (*__t).fill_cstr({fill_id}u64, {dst_bind}); \
         (*__t).step({ret_id}u64, [0, 0, 0], [3u8, 3u8, 3u8]) as ::core::ffi::c_int }}"
    )
}

/// The replacement block: bind each argument, record it as a trace event, and
/// yield a shared symbolic result cast to the call's return type.
fn block(
    name: &str,
    ret: &str,
    args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
) -> String {
    let call_id = id(name);
    let mut binds = String::new();
    let mut steps = String::new();
    for (i, arg) in args.iter().enumerate() {
        binds += &format!("let __a{i} = {};\n", arg.to_token_stream());
        steps += &format!(
            "(*__t).step({call_id}u64, \
             [crate::support::TraceArg::bits(&__a{i}), 0, 0], \
             [crate::support::TraceArg::kind(&__a{i}), 3u8, 3u8]);\n"
        );
    }
    // A final event carries the call's symbolic result (distinct id so it is
    // never confused with an argument event).
    let ret_id = call_id.wrapping_add(1);
    let tail = if ret == "()" {
        format!("let _ = (*__t).step({ret_id}u64, [0, 0, 0], [3u8, 3u8, 3u8]);")
    } else {
        format!("(*__t).step({ret_id}u64, [0, 0, 0], [3u8, 3u8, 3u8]) as {ret}")
    };
    format!(
        "{{ let __t = core::ptr::addr_of_mut!(crate::support::TRACE); {binds} {steps} {tail} }}"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn items(src: &str) -> Vec<syn::Item> {
        syn::parse_file(src).unwrap().items
    }

    #[test]
    fn rewrites_printf_call_into_trace_events() {
        let mut it =
            items("pub unsafe fn f(x: i32) { printf(b\"%d\\0\".as_ptr() as *const i8, x); }");
        rewrite(&mut it);
        let src = it
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(src.contains("TRACE"), "{src}");
        assert!(src.contains("TraceArg :: bits"), "{src}");
        assert!(!src.contains("printf ("), "call should be gone: {src}");
    }

    #[test]
    fn leaves_other_calls_alone() {
        let mut it = items("pub fn f() -> i32 { g(1) }\npub fn g(x: i32) -> i32 { x }");
        rewrite(&mut it);
        let src = it
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(src.contains("g (1)"), "{src}");
    }
}
