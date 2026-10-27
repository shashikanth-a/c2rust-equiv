//! Generate a scratch crate holding both versions of a function, a Kani
//! harness and a native runner.

use std::fs;
use std::io;
use std::path::Path;

use quote::ToTokens;
use syn::visit_mut::VisitMut;

use crate::heapgen::{Shape, SigShapes};
use crate::scalar;
use crate::unit::FnUnit;

const SUPPORT: &str = include_str!("scratch_template/support.rs");
const HEAP_SUPPORT: &str = include_str!("scratch_template/heap_support.rs");

/// The scratch crate's package name, which is also the runner binary's name.
pub const PACKAGE: &str = "equiv_scratch";

/// Source files of the two versions, as they appear in Kani's check locations.
pub const OLD_FILE: &str = "src/old.rs";
pub const NEW_FILE: &str = "src/new.rs";

/// Harnesses: each calls one version first, so a panic there cuts the path
/// before the other version runs.
pub const OLD_FIRST: &str = "proofs::old_then_new";
pub const NEW_FIRST: &str = "proofs::new_then_old";

fn cargo_toml(edition: &str) -> String {
    format!(
        r#"[package]
name = "{PACKAGE}"
version = "0.0.0"
edition = "{edition}"
publish = false

[workspace]

[lints.rust]
unexpected_cfgs = {{ level = "allow", check-cfg = ["cfg(kani)"] }}

# Overflow checks match Kani, which always enables them. Debug assertions
# stay off: with them, the standard library aborts on undefined-behaviour
# preconditions (as in `get_unchecked`), which would end a replay of
# several inputs instead of showing what each version does.
[profile.release]
opt-level = 1
overflow-checks = true
debug-assertions = false
"#
    )
}

pub fn write(dir: &Path, old: &FnUnit, new: &FnUnit, edition: &str, unwind: u32) -> io::Result<()> {
    fs::create_dir_all(dir.join("src"))?;
    fs::write(dir.join("Cargo.toml"), cargo_toml(edition))?;
    fs::write(dir.join(OLD_FILE), module_source(old, false))?;
    fs::write(dir.join(NEW_FILE), module_source(new, false))?;
    fs::write(dir.join("src/support.rs"), SUPPORT)?;
    fs::write(dir.join("src/lib.rs"), lib_source(old, new, unwind))?;
    fs::write(
        dir.join("src/main.rs"),
        format!(
            "#[cfg(not(kani))]\nfn main() {{\n    {PACKAGE}::run_main();\n}}\n\n#[cfg(kani)]\nfn main() {{}}\n"
        ),
    )?;
    Ok(())
}

/// How deep the symbolic heaps are built in the heap path.
pub const HEAP_DEPTH: usize = 3;

/// Write a scratch crate for the heap path: the two versions, the generated
/// `gen_`/`clone_`/`same_` code for the structs in the signature, and a
/// pointer-aware Kani harness. There is no native runner (symbolic heaps can't
/// yet be rebuilt from Kani's concrete bytes), so `main` is empty and the
/// caller runs only Kani on this crate.
pub fn write_heap(
    dir: &Path,
    old: &FnUnit,
    new: &FnUnit,
    edition: &str,
    unwind: u32,
    shapes: &SigShapes,
    generated: &str,
) -> io::Result<()> {
    fs::create_dir_all(dir.join("src"))?;
    fs::write(dir.join("Cargo.toml"), cargo_toml(edition))?;
    fs::write(dir.join(OLD_FILE), module_source(old, true))?;
    fs::write(dir.join(NEW_FILE), module_source(new, true))?;
    fs::write(dir.join("src/support.rs"), HEAP_SUPPORT)?;
    fs::write(
        dir.join("src/lib.rs"),
        heap_lib_source(old, new, shapes, generated, unwind),
    )?;
    fs::write(dir.join("src/main.rs"), "fn main() {}\n")?;
    Ok(())
}

fn module_source(unit: &FnUnit, inject_str_models: bool) -> String {
    let mut items = unit.items();
    items.iter_mut().for_each(make_standalone);
    // On the heap path, give the modelled C string functions Rust bodies so
    // Kani resolves calls to them instead of refusing a foreign symbol.
    if inject_str_models {
        crate::strmodel::inject(&mut items);
        crate::allocmodel::inject(&mut items);
    }
    let file = syn::File {
        shebang: None,
        attrs: vec![],
        items,
    };
    format!("#![allow(warnings)]\n\n{}", prettyplease::unparse(&file))
}

fn lib_source(old: &FnUnit, new: &FnUnit, unwind: u32) -> String {
    let sig = &old.function.sig;
    let mut arg_types = Vec::new();
    for input in &sig.inputs {
        if let syn::FnArg::Typed(pat_ty) = input {
            arg_types.push(qualify(&pat_ty.ty, "old"));
        }
    }
    let ret = match &sig.output {
        syn::ReturnType::Default => "()".to_owned(),
        syn::ReturnType::Type(_, ty) => qualify(ty, "old"),
    };
    let n = arg_types.len();
    let tuple = |items: &[String]| match items.len() {
        1 => format!("({},)", items[0]),
        _ => format!("({})", items.join(", ")),
    };
    let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
    let args_ty = tuple(&arg_types);
    let pat = tuple(&names);
    let call_args = names.join(", ");
    let old_name = old.name();
    let new_name = new.name();
    format!(
        r#"#![allow(warnings)]

pub mod new;
pub mod old;
mod support;

pub use support::*;

pub type Args = {args_ty};
pub type Ret = {ret};

pub fn call_old(args: Args) -> Ret {{
    let {pat} = args;
    unsafe {{ old::{old_name}({call_args}) }}
}}

pub fn call_new(args: Args) -> Ret {{
    let {pat} = args;
    unsafe {{ new::{new_name}({call_args}) }}
}}

#[cfg(kani)]
mod proofs {{
    use super::*;

    #[kani::proof]
    #[kani::unwind({unwind})]
    fn old_then_new() {{
        let args: Args = kani::any();
        let o = call_old(args);
        let n = call_new(args);
        assert!(Scalar::bits(&o) == Scalar::bits(&n), "results differ");
    }}

    #[kani::proof]
    #[kani::unwind({unwind})]
    fn new_then_old() {{
        let args: Args = kani::any();
        let n = call_new(args);
        let o = call_old(args);
        assert!(Scalar::bits(&o) == Scalar::bits(&n), "results differ");
    }}
}}
"#
    )
}

/// The crate root for the heap path: the generated code, and two harnesses
/// that build a symbolic `old` heap, clone it into an isomorphic `new` heap,
/// run both versions and compare the returned value and the mutated heaps.
fn heap_lib_source(
    old: &FnUnit,
    new: &FnUnit,
    shapes: &SigShapes,
    generated: &str,
    unwind: u32,
) -> String {
    let sig = &old.function.sig;
    let old_name = old.name();
    let new_name = new.name();
    let depth = HEAP_DEPTH;

    let arg_types: Vec<&syn::Type> = sig
        .inputs
        .iter()
        .filter_map(|a| match a {
            syn::FnArg::Typed(pt) => Some(&*pt.ty),
            syn::FnArg::Receiver(_) => None,
        })
        .collect();

    // Build each argument once (old's), clone the heap ones into new's. A
    // single clone map across all arguments preserves aliasing between them.
    let mut build = String::new();
    let mut clone = String::new();
    let mut old_args = Vec::new();
    let mut new_args = Vec::new();
    let mut heap_args: Vec<(usize, &str)> = Vec::new();
    let mut cell_args: Vec<usize> = Vec::new();
    let mut cstr_args: Vec<usize> = Vec::new();
    for (i, shape) in shapes.args.iter().enumerate() {
        match shape {
            Shape::Scalar => {
                let ty = qualify(arg_types[i], "old");
                build += &format!("        let a{i}: {ty} = kani::any();\n");
                old_args.push(format!("a{i}"));
                new_args.push(format!("a{i}"));
            }
            Shape::Heap(name) => {
                build += &format!("        let a{i} = gen_{name}(DEPTH);\n");
                clone += &format!("        let b{i} = clone_{name}(a{i}, &mut map);\n");
                old_args.push(format!("a{i}"));
                new_args.push(format!("b{i}"));
                heap_args.push((i, name));
            }
            // A read-only C string: both versions get identical bytes, and
            // there's no post-state to compare. `gen_cstr` yields `*mut c_char`;
            // cast at the call to the argument's declared pointer type (e.g.
            // `*const c_uchar` for libxml2's `xmlChar`).
            Shape::CStr => {
                build += &format!("        let a{i} = gen_cstr();\n");
                clone += &format!("        let b{i} = clone_cstr(a{i});\n");
                old_args.push(format!("a{i} as {}", qualify(arg_types[i], "old")));
                new_args.push(format!("b{i} as {}", qualify(arg_types[i], "new")));
                cstr_args.push(i);
            }
            // A pointer to one scalar: both versions get an identical cell; its
            // post-state is compared, catching a divergent write through `*mut`.
            Shape::ScalarCell => {
                let ty = qualify(arg_types[i], "old");
                build += &format!("        let a{i}: {ty} = gen_cell();\n");
                clone += &format!("        let b{i} = clone_cell(a{i});\n");
                old_args.push(format!("a{i}"));
                new_args.push(format!("b{i}"));
                cell_args.push(i);
            }
        }
    }
    let old_call = format!("old::{old_name}({})", old_args.join(", "));
    let new_call = format!("new::{new_name}({})", new_args.join(", "));

    // Compare the return value, then every heap argument's post-state, all
    // under one correspondence so aliasing between them is checked too.
    let ret_cmp = match &shapes.ret {
        Shape::Scalar => {
            "        assert!(Bits::bits(&o) == Bits::bits(&n), \"results differ\");\n".to_owned()
        }
        Shape::Heap(name) => {
            format!("        assert!(same_{name}(o, n, &mut corr), \"results differ\");\n")
        }
        // A returned C string / scalar pointer: compare the pointed-to content.
        // `o`/`n` are the functions' own return types; cast to the comparer's.
        Shape::CStr => "        assert!(same_cstr(o as *const core::ffi::c_char, n as *const core::ffi::c_char), \"results differ\");\n".to_owned(),
        Shape::ScalarCell => {
            "        assert!(same_cell(o, n), \"results differ\");\n".to_owned()
        }
    };
    let mut arg_cmp = String::new();
    for (i, name) in &heap_args {
        arg_cmp +=
            &format!("        assert!(same_{name}(a{i}, b{i}, &mut corr), \"heaps differ\");\n");
    }
    for i in &cell_args {
        arg_cmp += &format!("        assert!(same_cell(a{i}, b{i}), \"cell differs\");\n");
    }
    // A C-string argument's post-state: catches a divergent write through a
    // `*mut` buffer (for `*const` it is unchanged, so trivially equal).
    for i in &cstr_args {
        arg_cmp += &format!("        assert!(same_cstr(a{i}, b{i}), \"string differs\");\n");
    }
    // `corr` is used only by struct-pointer comparisons; a C-string-only
    // signature has none, so declaring it unconditionally would warn.
    let needs_corr = matches!(shapes.ret, Shape::Heap(_)) || !heap_args.is_empty();
    let corr_decl = if needs_corr {
        "        let mut corr = Corr::default();\n"
    } else {
        ""
    };
    // The clone map preserves aliasing between struct-pointer arguments; C
    // strings are cloned without it, so a C-string-only signature needs none.
    let map_decl = if heap_args.is_empty() {
        ""
    } else {
        "        let mut map = CloneMap::default();\n"
    };

    let harness = |name: &str, first_new: bool| {
        let calls = if first_new {
            format!("        let n = {new_call};\n        let o = {old_call};\n")
        } else {
            format!("        let o = {old_call};\n        let n = {new_call};\n")
        };
        format!(
            "    #[kani::proof]\n\
             \x20   #[kani::unwind({unwind})]\n\
             \x20   fn {name}() {{ unsafe {{\n\
             {build}\
             {map_decl}\
             {clone}\
             {calls}\
             {corr_decl}\
             {ret_cmp}{arg_cmp}\
             \x20   }} }}\n"
        )
    };

    format!(
        r#"#![allow(warnings)]

pub mod new;
pub mod old;
mod support;

pub use support::*;

{generated}

#[cfg(kani)]
mod proofs {{
    use super::*;
    const DEPTH: usize = {depth};

{old_then_new}
{new_then_old}}}
"#,
        old_then_new = harness("old_then_new", false),
        new_then_old = harness("new_then_old", true),
    )
}

/// Make a type from inside `module` usable from the crate root.
fn qualify(ty: &syn::Type, module: &str) -> String {
    struct Qualify<'a>(&'a str);
    impl VisitMut for Qualify<'_> {
        fn visit_type_path_mut(&mut self, t: &mut syn::TypePath) {
            syn::visit_mut::visit_type_path_mut(self, t);
            let p = &mut t.path;
            if t.qself.is_none() && p.leading_colon.is_none() && p.segments.len() == 1 {
                let name = p.segments[0].ident.to_string();
                if scalar::primitive(&name).is_none() {
                    p.segments.insert(
                        0,
                        syn::Ident::new(self.0, proc_macro2::Span::call_site()).into(),
                    );
                }
            }
        }
    }
    let mut ty = ty.clone();
    Qualify(module).visit_type_mut(&mut ty);
    ty.to_token_stream().to_string()
}

/// Drop attributes such as `#[no_mangle]`, which would clash between the two
/// versions, and make the item public so the harness can call it.
///
/// Functions also get the Rust ABI: a panic in an `extern "C"` function aborts
/// the process, which the native runner couldn't observe as a panic. Function
/// pointer types change to match.
fn make_standalone(item: &mut syn::Item) {
    struct RustAbi;
    impl VisitMut for RustAbi {
        fn visit_type_bare_fn_mut(&mut self, f: &mut syn::TypeBareFn) {
            f.abi = None;
            syn::visit_mut::visit_type_bare_fn_mut(self, f);
        }
    }
    RustAbi.visit_item_mut(item);
    let public: syn::Visibility = syn::parse_quote!(pub);
    match item {
        syn::Item::Fn(f) => {
            f.attrs.clear();
            f.vis = public;
            f.sig.abi = None;
        }
        syn::Item::Const(c) => {
            c.attrs.clear();
            c.vis = public;
        }
        syn::Item::Type(t) => {
            t.attrs.clear();
            t.vis = public;
        }
        _ => {}
    }
}
