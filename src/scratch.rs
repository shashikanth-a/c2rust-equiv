//! Generate a scratch crate holding both versions of a function, a Kani
//! harness and a native runner.

use std::fs;
use std::io;
use std::path::Path;

use quote::ToTokens;
use syn::visit_mut::VisitMut;

use crate::scalar;
use crate::unit::FnUnit;

const SUPPORT: &str = include_str!("scratch_template/support.rs");

/// The scratch crate's package name, which is also the runner binary's name.
pub const PACKAGE: &str = "equiv_scratch";

/// Source files of the two versions, as they appear in Kani's check locations.
pub const OLD_FILE: &str = "src/old.rs";
pub const NEW_FILE: &str = "src/new.rs";

/// Harnesses: each calls one version first, so a panic there cuts the path
/// before the other version runs.
pub const OLD_FIRST: &str = "proofs::old_then_new";
pub const NEW_FIRST: &str = "proofs::new_then_old";

pub fn write(dir: &Path, old: &FnUnit, new: &FnUnit, edition: &str, unwind: u32) -> io::Result<()> {
    fs::create_dir_all(dir.join("src"))?;
    fs::write(
        dir.join("Cargo.toml"),
        format!(
            r#"[package]
name = "{PACKAGE}"
version = "0.0.0"
edition = "{edition}"
publish = false

[workspace]

[lints.rust]
unexpected_cfgs = {{ level = "allow", check-cfg = ["cfg(kani)"] }}

# Overflow checks match Kani, which always enables them.
[profile.release]
opt-level = 1
overflow-checks = true
debug-assertions = true
"#
        ),
    )?;
    fs::write(dir.join(OLD_FILE), module_source(old))?;
    fs::write(dir.join(NEW_FILE), module_source(new))?;
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

fn module_source(unit: &FnUnit) -> String {
    let mut items = unit.items();
    items.iter_mut().for_each(make_standalone);
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
/// the process, which the native runner couldn't observe as a panic.
fn make_standalone(item: &mut syn::Item) {
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
