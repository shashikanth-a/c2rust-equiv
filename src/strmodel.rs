//! Rust models of the read-only C string functions, for the heap path.
//!
//! Kani does not call `extern "C"` functions outside a small built-in set, and
//! `strlen`/`strcmp`/... are not in it (only `malloc`/`mem*` are). So for a
//! function that calls them, [`inject`] turns each `extern` declaration of a
//! modelled string function into a real Rust definition with the same
//! signature; the crate's bare call sites then resolve to that definition
//! rather than a foreign symbol. Allocation and memory functions stay `extern`,
//! since Kani models those itself.
//!
//! The models are sound over NUL-terminated buffers, which `gen_cstr`
//! guarantees for string arguments: every read stops at or before the NUL that
//! `gen_cstr` places at the end of the buffer. The set here must stay in step
//! with `unit::is_modelled_c_fn`'s string names.

use quote::ToTokens;
use std::collections::BTreeMap;

/// The C string functions this module can define in Rust. Read-only: functions
/// that write through a destination pointer (`strcpy`, `strcat`) are excluded,
/// because the destination's bounds aren't modelled.
pub fn is_str_model(name: &str) -> bool {
    matches!(
        name,
        "strlen"
            | "strcmp"
            | "strncmp"
            | "strchr"
            | "strrchr"
            // The assertion handler and errno accessor also get Rust bodies.
            | "__assert_rtn"
            | "__assert_fail"
            | "__error"
            | "__errno_location"
    )
}

/// Replace every `extern` declaration of a modelled C string function with a
/// real Rust definition of the same signature, so Kani resolves calls to it.
/// Other foreign items (allocators, memory functions) are left untouched.
pub fn inject(items: &mut Vec<syn::Item>) {
    let mut wanted: BTreeMap<String, syn::Signature> = BTreeMap::new();
    for item in items.iter_mut() {
        if let syn::Item::ForeignMod(m) = item {
            m.items.retain(|it| {
                if let syn::ForeignItem::Fn(f) = it {
                    let name = f.sig.ident.to_string();
                    if is_str_model(&name) {
                        wanted.entry(name).or_insert_with(|| f.sig.clone());
                        return false;
                    }
                }
                true
            });
        }
    }
    // Drop extern blocks that held only string declarations.
    items.retain(|it| !matches!(it, syn::Item::ForeignMod(m) if m.items.is_empty()));
    for (name, sig) in wanted {
        if let Some(def) = define(&name, &sig) {
            items.push(syn::Item::Fn(def));
        }
    }
}

/// Build a Rust definition for one modelled string function, reusing the
/// `extern` declaration's exact parameter and return types so call sites keep
/// type-checking. Returns `None` if the signature doesn't match what the body
/// expects (e.g. the wrong number of arguments).
fn define(name: &str, sig: &syn::Signature) -> Option<syn::ItemFn> {
    let mut params = Vec::new();
    for (i, input) in sig.inputs.iter().enumerate() {
        let syn::FnArg::Typed(pt) = input else {
            return None;
        };
        let ident = match &*pt.pat {
            syn::Pat::Ident(pi) => pi.ident.to_string(),
            _ => format!("a{i}"),
        };
        params.push((ident, pt.ty.to_token_stream().to_string()));
    }
    let ret = match &sig.output {
        syn::ReturnType::Default => "()".to_owned(),
        syn::ReturnType::Type(_, t) => t.to_token_stream().to_string(),
    };
    let names: Vec<&str> = params.iter().map(|(n, _)| n.as_str()).collect();
    let body = body(name, &names, &ret)?;
    let decl = params
        .iter()
        .map(|(n, t)| format!("{n}: {t}"))
        .collect::<Vec<_>>()
        .join(", ");
    let src = format!("pub unsafe fn {name}({decl}) -> {ret} {body}");
    syn::parse_str(&src).ok()
}

/// The body for one modelled string function, as a brace-delimited block.
/// `a` holds the argument names, `ret` the return type as source. Returns
/// `None` when the argument count doesn't match the function.
fn body(name: &str, a: &[&str], ret: &str) -> Option<String> {
    // C string comparisons are on `unsigned char`; cast through `u8` so a
    // model matches C regardless of `c_char`'s platform signedness.
    let block = match (name, a) {
        ("strlen", [s]) => format!(
            "{{ let mut n: usize = 0; while *{s}.add(n) != 0 {{ n += 1; }} n as {ret} }}"
        ),
        ("strcmp", [s1, s2]) => format!(
            "{{ let mut i: usize = 0; loop {{ \
               let x = *{s1}.add(i) as u8 as i32; let y = *{s2}.add(i) as u8 as i32; \
               if x != y {{ return (x - y) as {ret}; }} \
               if x == 0 {{ return 0 as {ret}; }} i += 1; }} }}"
        ),
        ("strncmp", [s1, s2, n]) => format!(
            "{{ let mut i: usize = 0; while i < {n} as usize {{ \
               let x = *{s1}.add(i) as u8 as i32; let y = *{s2}.add(i) as u8 as i32; \
               if x != y {{ return (x - y) as {ret}; }} \
               if x == 0 {{ return 0 as {ret}; }} i += 1; }} 0 as {ret} }}"
        ),
        ("strchr", [s, c]) => format!(
            "{{ let mut p = {s}; loop {{ \
               if *p as u8 == {c} as u8 {{ return p as {ret}; }} \
               if *p == 0 {{ return core::ptr::null::<core::ffi::c_char>() as {ret}; }} \
               p = p.add(1); }} }}"
        ),
        ("strrchr", [s, c]) => format!(
            "{{ let mut p = {s}; let mut last = core::ptr::null::<core::ffi::c_char>() as {ret}; \
               loop {{ \
               if *p as u8 == {c} as u8 {{ last = p as {ret}; }} \
               if *p == 0 {{ return last; }} p = p.add(1); }} }}"
        ),
        // A failed assertion aborts in C; model it as a panic, which Kani
        // treats as cutting the path (so it never counts as a divergence).
        ("__assert_rtn" | "__assert_fail", _) => {
            "{ panic!(\"assertion failed\") }".to_owned()
        }
        // errno: a single per-run cell, zero-initialised. Both versions get
        // their own, so errno-dependent behaviour stays consistent in-run.
        ("__error" | "__errno_location", []) => {
            "{ static mut ERRNO: core::ffi::c_int = 0; core::ptr::addr_of_mut!(ERRNO) as _ }".to_owned()
        }
        _ => return None,
    };
    Some(block)
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;

    fn items(src: &str) -> Vec<syn::Item> {
        syn::parse_file(src).unwrap().items
    }

    #[test]
    fn extern_string_decls_become_rust_definitions() {
        let mut it = items(
            "extern \"C\" { \
               fn strlen(s: *const core::ffi::c_char) -> usize; \
               fn malloc(n: usize) -> *mut u8; \
             }",
        );
        inject(&mut it);
        // `malloc` stays an extern declaration; `strlen` becomes a definition.
        let src = it
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(src.contains("pub unsafe fn strlen"));
        assert!(src.contains("while * s . add"));
        // The extern block is kept (malloc is still foreign), with only malloc.
        let externs = it
            .iter()
            .filter(|i| matches!(i, syn::Item::ForeignMod(_)))
            .count();
        assert_eq!(externs, 1);
    }

    #[test]
    fn extern_block_of_only_strings_is_removed() {
        let mut it = items(
            "extern \"C\" { fn strcmp(a: *const i8, b: *const i8) -> i32; }",
        );
        inject(&mut it);
        assert!(!it.iter().any(|i| matches!(i, syn::Item::ForeignMod(_))));
        assert_eq!(it.iter().filter(|i| matches!(i, syn::Item::Fn(_))).count(), 1);
    }

    #[test]
    fn defined_models_parse_and_typecheck_as_syntax() {
        // Each model must at least produce a parseable function for its sig.
        for (src, _) in [
            ("fn strlen(s: *const i8) -> u64;", "strlen"),
            ("fn strcmp(a: *const i8, b: *const i8) -> i32;", "strcmp"),
            ("fn strncmp(a: *const i8, b: *const i8, n: u64) -> i32;", "strncmp"),
            ("fn strchr(s: *const i8, c: i32) -> *mut i8;", "strchr"),
            ("fn strrchr(s: *const i8, c: i32) -> *mut i8;", "strrchr"),
        ] {
            let f: syn::ForeignItemFn =
                syn::parse_str(src).unwrap_or_else(|e| panic!("parse {src}: {e}"));
            let def = define(&f.sig.ident.to_string(), &f.sig)
                .unwrap_or_else(|| panic!("no model for {src}"));
            // A well-formed function item round-trips through the parser.
            let text = def.to_token_stream().to_string();
            syn::parse_str::<syn::ItemFn>(&text).unwrap();
        }
    }

    #[test]
    fn unknown_or_write_functions_are_not_modelled() {
        assert!(!is_str_model("strcpy"));
        assert!(!is_str_model("strcat"));
        assert!(!is_str_model("getprogname"));
    }
}
