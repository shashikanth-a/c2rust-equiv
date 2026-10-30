//! Callee summaries (Subsystem A, phase A2): turn a callee that has been shown
//! equivalent (or is unchanged) into a shim that stands in for it at call
//! sites, so the caller needn't inline its body. A summary realises the
//! sound "replace a call with a havoc of its `assigns` set" rule (CBMC/Kani
//! function contracts) on the existing observable-call trace:
//!
//!   1. record the call `(id, args)` on the shared trace -- both versions must
//!      make the same call with the same arguments (observable equivalence);
//!   2. havoc the callee's write set (from [`crate::modref`]) to shared
//!      symbolic values -- its written pointer-parameter pointees and (later)
//!      globals -- so both versions see the same, arbitrary, post-state;
//!   3. return a shared symbolic result.
//!
//! Because the havoc over-approximates any deterministic effect and both
//! versions use the identical shim, a proof under the summary implies real
//! equivalence. A callee whose write set isn't fully havocable here (a written
//! struct pointee, a written global, an unrecordable argument, or `Top`) is
//! not summarisable and the caller must inline it instead -- sound, less
//! complete.

use quote::ToTokens;

use crate::modref::WriteSet;
use crate::strmodel::{arg_kind_bits, float_width, oracle_id};

/// Doc marker on a generated summary shim. The shim's body uses the scratch
/// template's trace support (`crate::support::TRACE`, `step`, `fill_cstr`),
/// which only exists in that template, so the heap body scope check skips a
/// callee carrying this marker -- it is trusted generated code, not source
/// under test. See [`is_summary_shim`].
pub(crate) const SUMMARY_MARKER: &str = "c2rust_equiv_summary_shim";

/// Whether `item` is a generated summary shim (carries [`SUMMARY_MARKER`]).
pub(crate) fn is_summary_shim(item: &syn::Item) -> bool {
    let syn::Item::Fn(f) = item else { return false };
    f.attrs.iter().any(|a| {
        a.path().is_ident("doc")
            && matches!(
                &a.meta,
                syn::Meta::NameValue(nv)
                    if matches!(
                        &nv.value,
                        syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. })
                            if s.value() == SUMMARY_MARKER
                    )
            )
    })
}

/// Generate a summary shim for `name` with signature `sig` and write set `ws`,
/// or `None` if it can't be summarised soundly (the caller then inlines it).
pub fn summarize(name: &str, sig: &syn::Signature, ws: &WriteSet) -> Option<syn::ItemFn> {
    let WriteSet::Known { params, globals } = ws else {
        return None;
    };
    // Globals in the write set need type-aware havoc; deferred (phase A2b), so
    // a global-writing callee isn't summarised yet.
    if !globals.is_empty() {
        return None;
    }

    // Collect parameters: name and type text.
    let mut ps: Vec<(String, String)> = Vec::new();
    for (i, input) in sig.inputs.iter().enumerate() {
        let syn::FnArg::Typed(pt) = input else {
            return None; // a receiver: not a free function
        };
        let name = match &*pt.pat {
            syn::Pat::Ident(id) => id.ident.to_string(),
            _ => format!("a{i}"),
        };
        ps.push((name, pt.ty.to_token_stream().to_string()));
    }
    let ret = match &sig.output {
        syn::ReturnType::Default => "()".to_owned(),
        syn::ReturnType::Type(_, t) => t.to_token_stream().to_string(),
    };

    let id = oracle_id(name);
    let mut body = String::from("let __t = core::ptr::addr_of_mut!(crate::support::TRACE);\n");

    // 1. Record each argument as an observable-call event.
    for (n, t) in &ps {
        let (bits, kind) = arg_kind_bits(n, t);
        body += &format!("(*__t).step({id}u64, [{bits}, 0, 0], [{kind}u8, 3u8, 3u8]);\n");
    }

    // 2. Havoc each written pointer-parameter pointee to a shared symbolic
    //    value. A scalar pointee is overwritten; a C-string pointee is filled;
    //    any other written pointee isn't havocable here -> not summarisable.
    let havoc_id = id.wrapping_add(2);
    for &i in params {
        let (pname, pty) = ps.get(i)?;
        let pointee = pointee_type(pty)?;
        if is_cstr_pointee(&pointee) {
            body +=
                &format!("(*__t).fill_cstr({havoc_id}u64, {pname} as *mut core::ffi::c_char);\n");
        } else if is_scalar(&pointee) {
            let v = format!("(*__t).step({havoc_id}u64, [0, 0, 0], [3u8, 3u8, 3u8])");
            let val = match float_width(&pointee) {
                Some(32) => format!("f32::from_bits({v} as u32) as {pointee}"),
                Some(_) => format!("f64::from_bits({v} as u64) as {pointee}"),
                None => format!("{v} as {pointee}"),
            };
            body += &format!("if !{pname}.is_null() {{ *{pname} = {val}; }}\n");
        } else {
            return None; // struct / unknown pointee: inline instead
        }
    }

    // 3. Return a shared symbolic result.
    let ret_id = id.wrapping_add(1);
    let v = format!("(*__t).step({ret_id}u64, [0, 0, 0], [3u8, 3u8, 3u8])");
    let tail = if ret == "()" {
        format!("let _ = {v};")
    } else if float_width(&ret).is_some() {
        match float_width(&ret) {
            Some(32) => format!("f32::from_bits({v} as u32) as {ret}"),
            _ => format!("f64::from_bits({v} as u64) as {ret}"),
        }
    } else if ret.trim_start().starts_with('*') {
        format!("{v} as usize as {ret}")
    } else {
        format!("{v} as {ret}")
    };
    body += &tail;

    let decl = ps
        .iter()
        .map(|(n, t)| format!("{n}: {t}"))
        .collect::<Vec<_>>()
        .join(", ");
    let src =
        format!("#[doc = \"{SUMMARY_MARKER}\"] pub unsafe fn {name}({decl}) -> {ret} {{ {body} }}");
    syn::parse_str(&src).ok()
}

/// The pointee type text of a `*mut T`/`*const T` type, else `None`.
fn pointee_type(ty: &str) -> Option<String> {
    let t = ty.trim();
    let rest = t.strip_prefix('*')?.trim_start();
    let rest = rest
        .strip_prefix("mut")
        .or_else(|| rest.strip_prefix("const"))?
        .trim_start();
    Some(rest.to_owned())
}

fn last_seg(ty: &str) -> &str {
    ty.rsplit("::").next().unwrap_or(ty).trim()
}

fn is_cstr_pointee(ty: &str) -> bool {
    matches!(last_seg(ty), "c_char" | "c_uchar")
}

fn is_scalar(ty: &str) -> bool {
    let n = last_seg(ty);
    float_width(ty).is_some()
        || crate::scalar::primitive(n).is_some()
        || crate::scalar::c_type(n).is_some()
        || crate::scalar::libc_typedef(n).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn sig(s: &str) -> syn::Signature {
        let f: syn::ItemFn = syn::parse_str(&format!("{s} {{ unimplemented!() }}")).unwrap();
        f.sig
    }
    fn known(params: &[usize]) -> WriteSet {
        WriteSet::Known {
            params: params.iter().copied().collect(),
            globals: BTreeSet::new(),
        }
    }
    fn src_of(f: &syn::ItemFn) -> String {
        f.to_token_stream().to_string()
    }

    #[test]
    fn pure_scalar_callee_summary_records_args_and_returns() {
        let f = summarize("add", &sig("fn add(x: i32, y: i32) -> i32"), &known(&[])).unwrap();
        let s = src_of(&f);
        assert!(s.contains("TRACE"));
        assert!(s.contains("step"));
        // No pointee havoc for a pure scalar callee.
        assert!(!s.contains("fill_cstr"));
    }

    #[test]
    fn out_param_pointee_is_havoced() {
        let f = summarize(
            "setint",
            &sig("fn setint(p: *mut i32, v: i32)"),
            &known(&[0]),
        )
        .unwrap();
        let s = src_of(&f);
        assert!(s.contains("* p ="), "scalar pointee havoced: {s}");
        assert!(s.contains("is_null"));
    }

    #[test]
    fn string_out_param_is_filled() {
        let f = summarize("fill", &sig("fn fill(d: *mut c_char)"), &known(&[0])).unwrap();
        assert!(src_of(&f).contains("fill_cstr"));
    }

    #[test]
    fn struct_out_param_is_not_summarisable() {
        assert!(summarize("f", &sig("fn f(p: *mut Node)"), &known(&[0])).is_none());
    }

    #[test]
    fn global_writer_is_not_summarisable() {
        let ws = WriteSet::Known {
            params: BTreeSet::new(),
            globals: ["G".to_owned()].into_iter().collect(),
        };
        assert!(summarize("f", &sig("fn f(x: i32)"), &ws).is_none());
    }

    #[test]
    fn top_is_not_summarisable() {
        assert!(summarize("f", &sig("fn f(x: i32)"), &WriteSet::Top).is_none());
    }
}
