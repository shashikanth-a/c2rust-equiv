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
    ) || is_pure_oracle(name)
}

/// Pure, deterministic libc functions of scalar arguments: math, and the
/// `ctype` classifiers/converters. Modelled as uninterpreted functions keyed
/// by their arguments (so both versions agree for equal arguments). Sound
/// because they are side-effect free and depend only on their arguments.
pub fn is_pure_oracle(name: &str) -> bool {
    matches!(
        name,
        // <math.h>, one or two floating-point arguments.
        "exp" | "exp2" | "log" | "log2" | "log10" | "sqrt" | "cbrt" | "sin" | "cos" | "tan"
            | "asin" | "acos" | "atan" | "sinh" | "cosh" | "tanh" | "fabs" | "ceil" | "floor"
            | "round" | "trunc" | "rint" | "nearbyint"
            | "fmod" | "pow" | "atan2" | "hypot" | "copysign" | "fmax" | "fmin" | "fdim"
        // <ctype.h> and integer helpers, one integer argument.
            | "abs" | "labs" | "toupper" | "tolower" | "isdigit" | "isalpha" | "isspace"
            | "isupper" | "islower" | "isalnum" | "ispunct" | "iscntrl" | "isprint"
            | "isxdigit" | "isgraph" | "isblank"
    )
}

/// Whether a foreign function can be modelled by the external-call trace: not
/// variadic, and every argument a scalar or float (recorded by value). Such a
/// call is an observable event -- both versions must make the same calls in the
/// same order (VOC/CoVaC observable-behaviour equivalence). Pointer and string
/// arguments need correspondence-based comparison and aren't handled yet.
pub fn is_trace_modellable(item: &Option<syn::Item>) -> bool {
    matches!(item, Some(syn::Item::ForeignMod(m))
        if matches!(m.items.as_slice(), [syn::ForeignItem::Fn(f)] if is_trace_sig(&f.sig)))
}

fn is_trace_sig(sig: &syn::Signature) -> bool {
    // Each argument is recorded as its own trace event (see `trace_body`), so
    // an arity above three is modellable rather than rejected; the cap only
    // bounds trace usage. Variadic externals are handled separately (varmodel).
    if sig.variadic.is_some() || sig.inputs.len() > 16 {
        return false;
    }
    // A diverging function (`-> !`) isn't modelled as a returning trace call.
    if matches!(&sig.output, syn::ReturnType::Type(_, t) if matches!(&**t, syn::Type::Never(_))) {
        return false;
    }
    // Each argument must be recordable: a scalar/float (by value), or a pointer
    // (compared by content for strings, by heap bijection otherwise).
    sig.inputs.iter().all(|a| match a {
        syn::FnArg::Typed(pt) => {
            matches!(&*pt.ty, syn::Type::Ptr(_))
                || scalar_or_float(&pt.ty.to_token_stream().to_string())
        }
        syn::FnArg::Receiver(_) => false,
    })
}

/// How a trace argument is recorded: its bit expression and kind tag
/// (0 scalar/float, 1 NUL-terminated string, 2 pointer by bijection).
pub(crate) fn arg_kind_bits(name: &str, ty: &str) -> (String, u8) {
    let t = ty.trim();
    if t.starts_with('*') {
        // A pointer: a `c_char`/`c_uchar` pointee is a string (compared by
        // content), anything else is compared through the heap bijection.
        let pointee = t.rsplit("::").next().unwrap_or(t).trim();
        let kind = if pointee == "c_char" || pointee == "c_uchar" { 1 } else { 2 };
        (format!("({name} as usize as u128)"), kind)
    } else if float_width(ty).is_some() {
        (format!("({name}.to_bits() as u128)"), 0)
    } else {
        (format!("({name} as u128)"), 0)
    }
}

/// Whether a type's spelling is a scalar or float the trace records by value.
fn scalar_or_float(ty: &str) -> bool {
    let last = ty.rsplit("::").next().unwrap_or(ty).trim();
    float_width(ty).is_some()
        || crate::scalar::primitive(last).is_some()
        || crate::scalar::c_type(last).is_some()
        || crate::scalar::libc_typedef(last).is_some()
}

/// The body of a trace shim: record `(id, args)` as an observable call and
/// return the shared symbolic result, rebuilt to the return type.
fn trace_body(name: &str, args: &[(String, String)], ret: &str) -> String {
    let id = oracle_id(name);
    // The statements preceding the result, and the `step` whose shared symbolic
    // value becomes the call's result.
    let (prefix, v) = if args.len() <= 3 {
        let mut slots = [String::from("0u128"), String::from("0u128"), String::from("0u128")];
        let mut kinds = [3u8, 3, 3];
        for (i, (n, t)) in args.iter().enumerate() {
            let (bits, kind) = arg_kind_bits(n, t);
            slots[i] = bits;
            kinds[i] = kind;
        }
        let v = format!(
            "(*core::ptr::addr_of_mut!(crate::support::TRACE)).step({id}u64, [{}, {}, {}], [{}u8, {}u8, {}u8])",
            slots[0], slots[1], slots[2], kinds[0], kinds[1], kinds[2]
        );
        (String::new(), v)
    } else {
        // More than three arguments: the three-slot event can't hold them, so
        // record each as its own ordered event keyed by the function id (as the
        // indirect-call model does), then a final event with a distinct id for
        // the shared symbolic result. Both versions emit the identical
        // sequence, so a divergent argument is caught, not collapsed.
        let mut prefix =
            String::from("let __t = core::ptr::addr_of_mut!(crate::support::TRACE);");
        for (n, t) in args {
            let (bits, kind) = arg_kind_bits(n, t);
            prefix += &format!("(*__t).step({id}u64, [{bits}, 0u128, 0u128], [{kind}u8, 3u8, 3u8]);");
        }
        let ret_id = oracle_id(&format!("{name}#ret"));
        let v = format!("(*__t).step({ret_id}u64, [0u128, 0u128, 0u128], [3u8, 3u8, 3u8])");
        (prefix, v)
    };
    let result = match float_width(ret) {
        Some(32) => format!("f32::from_bits({v} as u32) as {ret}"),
        Some(_) => format!("f64::from_bits({v} as u64) as {ret}"),
        None if ret == "()" => format!("{{ let _ = {v}; }}"),
        // A pointer result goes through `usize`; a scalar casts directly.
        None if ret.trim_start().starts_with('*') => format!("{v} as usize as {ret}"),
        None => format!("{v} as {ret}"),
    };
    format!("{{ {prefix} {result} }}")
}

/// A 64-bit id for an oracle function, stable across the two versions (both
/// hash the same name) and distinct between functions (FNV-1a).
pub(crate) fn oracle_id(name: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in name.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Classify a scalar type's spelling as float (and width) or integer, for
/// extracting its bits into an oracle key and rebuilding a result.
pub(crate) fn float_width(ty: &str) -> Option<u32> {
    let last = ty.rsplit("::").next().unwrap_or(ty).trim();
    match last {
        "f64" | "c_double" => Some(64),
        "f32" | "c_float" => Some(32),
        _ => None,
    }
}

/// The body of a pure-oracle shim: combine the arguments' bits into a key,
/// look the result up in the shared oracle, and rebuild the return type.
fn oracle_body(name: &str, args: &[(String, String)], ret: &str) -> Option<String> {
    if args.is_empty() || args.len() > 2 {
        return None;
    }
    let bits = |(n, t): &(String, String)| match float_width(t) {
        Some(_) => format!("({n}.to_bits() as u128)"),
        None => format!("({n} as u128)"),
    };
    let key = match args {
        [a] => bits(a),
        [a, b] => format!("({} | ({} << 64))", bits(a), bits(b)),
        _ => unreachable!(),
    };
    let id = oracle_id(name);
    let v = format!("crate::support::ORACLE.get({id}u64, {key})");
    let result = match float_width(ret) {
        Some(32) => format!("f32::from_bits({v} as u32) as {ret}"),
        Some(_) => format!("f64::from_bits({v} as u64) as {ret}"),
        None if ret == "()" => format!("{{ let _ = {v}; }}"),
        None => format!("{v} as {ret}"),
    };
    Some(format!("{{ {result} }}"))
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
                    // A string/oracle model, or any other non-variadic scalar
                    // external modelled as an observable trace call. The
                    // memory functions Kani models natively stay `extern`.
                    if is_str_model(&name)
                        || (is_trace_sig(&f.sig) && !crate::unit::is_modelled_c_fn(&name))
                    {
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
    let body = if is_pure_oracle(name) {
        oracle_body(name, &params, &ret)?
    } else if is_str_model(name) {
        let names: Vec<&str> = params.iter().map(|(n, _)| n.as_str()).collect();
        body(name, &names, &ret)?
    } else {
        // A side-effecting external modelled as an observable trace call.
        trace_body(name, &params, &ret)
    };
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

    #[test]
    fn many_arg_foreign_fn_is_trace_modellable_and_shim_parses() {
        // Four-plus arguments (scalars and pointers, as `fread`/`fwrite`) exceed
        // the old three-slot limit; the call is now trace-modellable and its
        // shim -- one `step` per argument plus a result event -- parses.
        let src = "fn fread(p: *mut u8, sz: u64, n: u64, s: *mut u8) -> u64;";
        let f: syn::ForeignItemFn = syn::parse_str(src).unwrap();
        assert!(is_trace_sig(&f.sig), "4-arg scalar/ptr sig should be trace-modellable");
        let def = define("fread", &f.sig).expect("shim defined");
        let text = def.to_token_stream().to_string();
        syn::parse_str::<syn::ItemFn>(&text).unwrap();
        assert_eq!(text.matches(". step (").count(), 5, "4 arg events + 1 result event");
    }

    #[test]
    fn seventeen_arg_foreign_fn_is_not_modelled() {
        let args = (0..17).map(|i| format!("a{i}: i32")).collect::<Vec<_>>().join(", ");
        let f: syn::ForeignItemFn =
            syn::parse_str(&format!("fn big({args}) -> i32;")).unwrap();
        assert!(!is_trace_sig(&f.sig));
    }
}
