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
    // The allocator-hook shims live once in the shared `support` module so both
    // versions' globals point at the same function (identical address), kept out
    // of the per-unit modules where two copies would look like divergent call
    // sequences. Emitted only when an allocator hook is actually used.
    let mut support = HEAP_SUPPORT.to_owned();
    if crate::allocmodel::needs_shims(&old.items()) || crate::allocmodel::needs_shims(&new.items())
    {
        support.push('\n');
        support.push_str(crate::allocmodel::shims_source());
    }
    fs::write(dir.join("src/support.rs"), support)?;
    fs::write(
        dir.join("src/lib.rs"),
        heap_lib_source(old, new, shapes, generated, unwind),
    )?;
    fs::write(dir.join("src/main.rs"), "fn main() {}\n")?;
    Ok(())
}

/// Write a scratch crate for route B (relational, single-iteration loop
/// equivalence). Like the heap crate, but each version's module also carries a
/// generated `__looprel_iter` helper (one loop-body iteration, the counter a
/// parameter), and old's module a `__looprel_bound` helper; the harness draws a
/// symbolic counter in `[0, bound)`, runs one iteration of each version on
/// corresponding heaps, and compares the heaps and modelled globals. No loop
/// runs, so nothing unrolls and there is no unwinding wall. See `looprel`.
#[allow(clippy::too_many_arguments)]
pub fn write_looprel(
    dir: &Path,
    old: &FnUnit,
    new: &FnUnit,
    edition: &str,
    unwind: u32,
    shapes: &SigShapes,
    generated: &str,
    plan: &crate::looprel::Plan,
) -> io::Result<()> {
    fs::create_dir_all(dir.join("src"))?;
    fs::write(dir.join("Cargo.toml"), cargo_toml(edition))?;
    let old_extra = looprel_helper_items(&old.function, plan, &plan.old_iter_body, true);
    let new_extra = looprel_helper_items(&new.function, plan, &plan.new_iter_body, false);
    fs::write(dir.join(OLD_FILE), module_source_with(old, true, old_extra))?;
    fs::write(dir.join(NEW_FILE), module_source_with(new, true, new_extra))?;
    let mut support = HEAP_SUPPORT.to_owned();
    if crate::allocmodel::needs_shims(&old.items()) || crate::allocmodel::needs_shims(&new.items())
    {
        support.push('\n');
        support.push_str(crate::allocmodel::shims_source());
    }
    fs::write(dir.join("src/support.rs"), support)?;
    fs::write(
        dir.join("src/lib.rs"),
        looprel_lib_source(old, shapes, generated, plan, unwind),
    )?;
    fs::write(dir.join("src/main.rs"), "fn main() {}\n")?;
    Ok(())
}

/// The oracle/trace id used for a counter-indexed write, modelled as a trace
/// event. The angle brackets keep it out of the C-identifier namespace, so it
/// never collides with a modelled external call's id.
fn write_event_id() -> u64 {
    crate::strmodel::oracle_id("<looprel-write>")
}

/// Rewrite each counter-indexed write `*<base>.offset(<idx>) = <val>` (or
/// `.add`) into a trace event carrying the *address* and the *value*, without
/// performing the write. The address is computed with `wrapping_offset` /
/// `wrapping_add` -- pure pointer arithmetic with no in-bounds requirement and
/// no dereference -- so the buffer is never materialised and an out-of-range
/// index is not undefined behaviour. The two versions share one symbolic heap
/// (nothing is mutated), so a write to a different field yields a different
/// base address and a write to a different index a different offset; both show
/// up as a divergent event. The value is recorded by its bits, so a divergent
/// value diverges too. Ordering and count are checked by the trace's
/// record/replay, so a reordered or dropped write is caught as well.
struct WriteInstrumenter {
    id: u64,
}
impl VisitMut for WriteInstrumenter {
    fn visit_expr_mut(&mut self, e: &mut syn::Expr) {
        if let syn::Expr::Assign(a) = e {
            if let syn::Expr::Unary(u) = &*a.left {
                if matches!(u.op, syn::UnOp::Deref(_)) {
                    if let Some((base, method, idx)) = offset_place_parts(&u.expr) {
                        let wrapping = if method == "add" {
                            syn::Ident::new("wrapping_add", proc_macro2::Span::call_site())
                        } else {
                            syn::Ident::new("wrapping_offset", proc_macro2::Span::call_site())
                        };
                        let val = (*a.right).clone();
                        let id = self.id;
                        *e = syn::parse_quote!({
                            let __addr =
                                (#base).#wrapping(#idx) as *const u8 as usize;
                            let __v = crate::Bits::bits(&(#val));
                            let __tr = core::ptr::addr_of_mut!(crate::TRACE);
                            (*__tr).step(#id, [__addr as u128, __v, 0u128], [0u8, 0u8, 3u8]);
                        });
                        return;
                    }
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, e);
    }
}

/// Split an `.offset`/`.add` place into (receiver, method-name, index arg).
fn offset_place_parts(place: &syn::Expr) -> Option<(syn::Expr, String, syn::Expr)> {
    match place {
        syn::Expr::Paren(p) => offset_place_parts(&p.expr),
        syn::Expr::MethodCall(m)
            if (m.method == "offset" || m.method == "add") && m.args.len() == 1 =>
        {
            Some((
                (*m.receiver).clone(),
                m.method.to_string(),
                m.args[0].clone(),
            ))
        }
        _ => None,
    }
}

/// Build the per-module route-B helpers for one version: `__looprel_iter` (the
/// loop's preamble then one body iteration, with the counter as a parameter and
/// every counter-indexed write rewritten into a trace obligation) and, when
/// `with_bound`, `__looprel_bound` (the preamble then the bound expression).
/// They reuse the original function's signature so every parameter the body
/// reads is in scope, and live in the version's own module so its local names
/// and types resolve.
fn looprel_helper_items(
    func: &syn::ItemFn,
    plan: &crate::looprel::Plan,
    iter_body: &[syn::Stmt],
    with_bound: bool,
) -> Vec<syn::Item> {
    let counter = &plan.counter;
    let counter_ty = &plan.counter_ty;

    let mut iter_sig = func.sig.clone();
    iter_sig.ident = syn::Ident::new("__looprel_iter", proc_macro2::Span::call_site());
    iter_sig.output = syn::ReturnType::Default;
    iter_sig.unsafety = Some(Default::default());
    let counter_param: syn::FnArg = syn::parse_quote!(#counter: #counter_ty);
    iter_sig.inputs.push(counter_param);
    let mut iter_stmts = plan.preamble.clone();
    iter_stmts.extend(iter_body.iter().cloned());
    // Abstract the counter-indexed writes into trace obligations.
    let mut instr = WriteInstrumenter {
        id: write_event_id(),
    };
    for s in &mut iter_stmts {
        instr.visit_stmt_mut(s);
    }
    let iter_fn = syn::ItemFn {
        attrs: vec![],
        vis: syn::parse_quote!(pub),
        sig: iter_sig,
        block: Box::new(syn::Block {
            brace_token: Default::default(),
            stmts: iter_stmts,
        }),
    };
    let mut items = vec![syn::Item::Fn(iter_fn)];

    if with_bound {
        let mut bound_sig = func.sig.clone();
        bound_sig.ident = syn::Ident::new("__looprel_bound", proc_macro2::Span::call_site());
        bound_sig.output = syn::parse_quote!(-> #counter_ty);
        bound_sig.unsafety = Some(Default::default());
        let bound_expr = plan.bound.clone();
        let mut bound_stmts = plan.preamble.clone();
        bound_stmts.push(syn::Stmt::Expr(bound_expr, None));
        let bound_fn = syn::ItemFn {
            attrs: vec![],
            vis: syn::parse_quote!(pub),
            sig: bound_sig,
            block: Box::new(syn::Block {
                brace_token: Default::default(),
                stmts: bound_stmts,
            }),
        };
        items.push(syn::Item::Fn(bound_fn));
    }
    items
}

/// The crate root for route B (stage 3, non-materialising): the generated heap
/// code, and two harnesses that build **one** symbolic heap, draw a symbolic
/// counter `__c` in `[0, __bound)`, and run one loop iteration of each version
/// on that **shared** heap. Nothing is mutated -- every counter-indexed write is
/// abstracted into an (address, value) trace obligation (see
/// [`WriteInstrumenter`]) rather than performed -- so sharing is sound and the
/// buffer is never materialised. All obligations (writes and external calls, in
/// order and count) are discharged by the trace's record/replay; there is no
/// post-state to compare (the function returns `()`).
fn looprel_lib_source(
    old: &FnUnit,
    shapes: &SigShapes,
    generated: &str,
    plan: &crate::looprel::Plan,
    unwind: u32,
) -> String {
    let depth = HEAP_DEPTH;
    let sig = &old.function.sig;
    let arg_types: Vec<&syn::Type> = sig
        .inputs
        .iter()
        .filter_map(|a| match a {
            syn::FnArg::Typed(pt) => Some(&*pt.ty),
            syn::FnArg::Receiver(_) => None,
        })
        .collect();

    // Build one symbolic value per argument, shared by both versions. A heap or
    // cell pointer is cast to the new module's (layout-identical) type for new's
    // call; a scalar is passed by value to both. Pointer arguments are only read
    // and address-computed (never written), so sharing cannot let one version
    // observe the other's effects.
    let mut build = String::new();
    let mut old_args = Vec::new();
    let mut new_args = Vec::new();
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
                old_args.push(format!("a{i}"));
                new_args.push(format!("a{i} as {}", qualify(arg_types[i], "new")));
            }
            Shape::ScalarCell => {
                let ty = qualify(arg_types[i], "old");
                build += &format!("        let a{i}: {ty} = gen_cell();\n");
                old_args.push(format!("a{i}"));
                new_args.push(format!("a{i} as {}", qualify(arg_types[i], "new")));
            }
            // Other shapes are rejected before reaching here (see
            // `try_loop_relational`); guard anyway so a future shape can't be
            // silently mis-shared.
            _ => {
                build += "        compile_error!(\"unsupported route-B argument shape\");\n";
            }
        }
    }
    let counter_ty = qualify(&plan.counter_ty, "old");
    let old_arglist = old_args.join(", ");
    let new_arglist = new_args.join(", ");
    let iter = |module: &str, args: &str| {
        if args.is_empty() {
            format!("{module}::__looprel_iter(__c)")
        } else {
            format!("{module}::__looprel_iter({args}, __c)")
        }
    };
    let old_iter = iter("old", &old_arglist);
    let new_iter = iter("new", &new_arglist);
    let bound_call = if old_arglist.is_empty() {
        "old::__looprel_bound()".to_owned()
    } else {
        format!("old::__looprel_bound({old_arglist})")
    };
    // Draw a symbolic counter in the loop's real index range.
    let counter_setup = format!(
        "        let __bound: {counter_ty} = {bound_call};\n\
         \x20       let __c: {counter_ty} = kani::any();\n\
         \x20       kani::assume(__c >= 0 as {counter_ty} && __c < __bound);\n"
    );

    let rec = "        let __tr = core::ptr::addr_of_mut!(TRACE);\n        (*__tr).record();\n";
    let replay = "        (*__tr).replay();\n";
    let finish = "        (*__tr).finish();\n";
    let harness = |name: &str, first_new: bool| {
        let calls = if first_new {
            format!("{rec}        {new_iter};\n{replay}        {old_iter};\n{finish}")
        } else {
            format!("{rec}        {old_iter};\n{replay}        {new_iter};\n{finish}")
        };
        format!(
            "    #[kani::proof]\n\
             \x20   #[kani::unwind({unwind})]\n\
             \x20   fn {name}() {{ unsafe {{\n\
             {build}\
             {counter_setup}\
             {calls}\
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

fn module_source(unit: &FnUnit, inject_str_models: bool) -> String {
    module_source_with(unit, inject_str_models, Vec::new())
}

/// Like [`module_source`], but appends `extra` items (made standalone and
/// run through the same model rewrites) after the unit's own. Route B uses it
/// to emit per-module `__looprel_iter` / `__looprel_bound` helpers that must
/// resolve the unit's own names, so they live inside the module, not the crate
/// root.
fn module_source_with(unit: &FnUnit, inject_str_models: bool, extra: Vec<syn::Item>) -> String {
    let mut items = unit.items();
    items.extend(extra);
    items.iter_mut().for_each(make_standalone);
    // A fn-ptr `static mut` global is modelled by a symbolic word the harness
    // injects into both versions, so its concrete default is irrelevant;
    // neutralise the initializer to `None` to avoid pulling the named default
    // function (and its transitive dependencies) into the unit.
    if inject_str_models {
        let aliases = crate::heapgen::alias_table_from_items(&items);
        for it in &mut items {
            if let syn::Item::Static(s) = it {
                if crate::unit::is_fnptr_mut_static(s, &aliases) {
                    s.expr = syn::parse_quote!(None);
                }
            }
        }
    }
    // On the heap path, give the modelled C string functions Rust bodies so
    // Kani resolves calls to them instead of refusing a foreign symbol.
    if inject_str_models {
        crate::strmodel::inject(&mut items);
        crate::allocmodel::inject(&mut items);
        crate::varmodel::rewrite(&mut items);
        crate::errormodel::rewrite(&mut items);
        crate::indirectmodel::rewrite(&mut items);
        crate::mutexmodel::rewrite(&mut items);
        // Model floating-point division as an uninterpreted operation (keyed on
        // operand bits, via the shared `FpDiv` trait): CBMC's IEEE-754 divider
        // makes an otherwise-trivial float equivalence proof time out. Sound for
        // equivalence; see `fpmodel`. Runs last so it also abstracts any `/`
        // introduced by the models above.
        crate::fpmodel::rewrite(&mut items);
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
    let old_name = old.name();
    let new_name = new.name();
    let depth = HEAP_DEPTH;

    let ArgPlan {
        build,
        clone,
        old_args,
        new_args,
        arg_cmp,
        corr_decl,
        map_decl,
    } = arg_plan(old, shapes);
    let old_call = format!("old::{old_name}({})", old_args.join(", "));
    let new_call = format!("new::{new_name}({})", new_args.join(", "));

    // Compare the return value (the per-argument/global comparisons are in
    // `arg_cmp`, built by `arg_plan`).
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
        // A returned function pointer: compared by identity (its word value).
        Shape::OpaqueArg(_) => "        assert!(unsafe { core::mem::transmute::<_, usize>(o) } \
             == unsafe { core::mem::transmute::<_, usize>(n) }, \"results differ\");\n"
            .to_owned(),
        // A returned C-enum newtype: compare the inner scalar (distinct types).
        Shape::ScalarNewtype(_) => {
            "        assert!(o.0 == n.0, \"results differ\");\n".to_owned()
        }
    };

    // The first version called records its external-call trace; the second
    // must replay it exactly (same calls, same order, same arguments), so both
    // have identical observable behaviour (VOC/CoVaC observable equivalence).
    let rec = "        let __tr = core::ptr::addr_of_mut!(TRACE);\n        (*__tr).record();\n";
    let replay = "        (*__tr).replay();\n";
    let finish = "        (*__tr).finish();\n";
    let harness = |name: &str, first_new: bool| {
        let calls = if first_new {
            format!(
                "{rec}        let n = {new_call};\n{replay}        let o = {old_call};\n{finish}"
            )
        } else {
            format!(
                "{rec}        let o = {old_call};\n{replay}        let n = {new_call};\n{finish}"
            )
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

/// The argument-building, cloning and post-state comparison shared by the heap
/// harness and the route-B relational harness: both build one symbolic set of
/// arguments (old's), clone the heap ones into new's isomorphic copies, and
/// compare the two versions' heaps, cells, strings and modelled globals
/// afterwards. The heap harness wraps this around whole-function calls; route B
/// wraps it around a single symbolic loop iteration.
struct ArgPlan {
    build: String,
    clone: String,
    old_args: Vec<String>,
    new_args: Vec<String>,
    arg_cmp: String,
    corr_decl: String,
    map_decl: String,
}

fn arg_plan(old: &FnUnit, shapes: &SigShapes) -> ArgPlan {
    let sig = &old.function.sig;
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
            // A function-pointer argument: an opaque symbolic word over all
            // values (null-niche `Option<fn>` makes every `usize` valid),
            // passed by value to both versions. It is carried data (a call
            // through it is a modelled trace call), so there is no post-state
            // to compare -- both versions hold the same value.
            Shape::OpaqueArg(ty) => {
                build += &format!(
                    "        let a{i}: {ty} = \
                     unsafe {{ core::mem::transmute::<usize, {ty}>(kani::any::<usize>()) }};\n"
                );
                old_args.push(format!("a{i}"));
                new_args.push(format!("a{i}"));
            }
            // A C-enum newtype: build old's value with a symbolic inner scalar,
            // give new the same inner wrapped in its own (distinct) type.
            Shape::ScalarNewtype(name) => {
                build += &format!("        let a{i} = old::{name}(kani::any());\n");
                old_args.push(format!("a{i}"));
                new_args.push(format!("new::{name}(a{i}.0)"));
            }
        }
    }

    // Every heap argument's post-state, all under one correspondence so
    // aliasing between them is checked too.
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
    // Each modelled scalar `static mut` global: both versions start from the
    // same initializer, so their final values must agree (a read copies the
    // value out, avoiding a reference to a `static mut`).
    for g in old.items().iter().filter_map(|it| match it {
        syn::Item::Static(s) if crate::unit::is_scalar_mut_static(s) => Some(s.ident.to_string()),
        _ => None,
    }) {
        arg_cmp += &format!(
            "        {{ let og = old::{g}; let ng = new::{g}; \
             assert!(Bits::bits(&og) == Bits::bits(&ng), \"global {g} differs\"); }}\n"
        );
    }
    // Each modelled struct `static mut` global (e.g. `xmlLastError`): both
    // versions start from the same initializer, so their final states must
    // agree field-by-field. The write is observable output; the comparison
    // follows pointers under `corr`, so a diverging error message is caught.
    let gitems = old.items();
    let gstructs = crate::heapgen::data_struct_fields_from_items(&gitems);
    let galiases = crate::heapgen::alias_table_from_items(&gitems);
    let struct_globals: Vec<(String, String, Option<String>)> = gitems
        .iter()
        .filter_map(|it| match it {
            syn::Item::Static(s) => {
                crate::unit::modelled_struct_mut_static(s, &gstructs, &galiases).map(|t| {
                    (
                        s.ident.to_string(),
                        t,
                        crate::unit::mut_static_array_len(s, &galiases),
                    )
                })
            }
            _ => None,
        })
        .collect();
    for (g, ty, arr) in &struct_globals {
        match arr {
            // A `static mut [T; N]` global: compare the two versions' final
            // state element by element, each a struct comparison under `corr`.
            Some(len) => {
                arg_cmp += &format!(
                    "        {{ let mut __i = 0usize; while __i < ({len}) as usize {{ \
                     let og = core::ptr::addr_of!(old::{g}[__i]); \
                     let ng = core::ptr::addr_of!(new::{g}[__i]); \
                     assert!(sameval_{ty}(og, ng, &mut corr), \"global {g} differs\"); \
                     __i += 1; }} }}\n"
                );
            }
            None => {
                arg_cmp += &format!(
                    "        {{ let og = core::ptr::addr_of!(old::{g}); \
                     let ng = core::ptr::addr_of!(new::{g}); \
                     assert!(sameval_{ty}(og, ng, &mut corr), \"global {g} differs\"); }}\n"
                );
            }
        }
    }
    // Each fn-ptr `static mut` global: inject one symbolic word, shared by both
    // versions, before the call. Its concrete default is a function address
    // that differs between the two compiled crates, so carrying that by value
    // would falsely diverge; a single symbolic word generalises over every
    // value and is read identically by both runs. Read-only (write-guarded), so
    // no final comparison -- the stored word is compared wherever it flows (a
    // heap field, under `corr`).
    for (gi, g) in gitems
        .iter()
        .filter_map(|it| match it {
            syn::Item::Static(s) if crate::unit::is_fnptr_mut_static(s, &galiases) => {
                Some(s.ident.to_string())
            }
            _ => None,
        })
        .enumerate()
    {
        build += &format!(
            "        let __g{gi}: usize = kani::any(); \
             old::{g} = core::mem::transmute(__g{gi}); \
             new::{g} = core::mem::transmute(__g{gi});\n"
        );
    }
    // `corr` is used only by struct-pointer comparisons; a C-string-only
    // signature has none, so declaring it unconditionally would warn.
    let needs_corr =
        matches!(shapes.ret, Shape::Heap(_)) || !heap_args.is_empty() || !struct_globals.is_empty();
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

    ArgPlan {
        build,
        clone,
        old_args,
        new_args,
        arg_cmp,
        corr_decl: corr_decl.to_owned(),
        map_decl: map_decl.to_owned(),
    }
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
            // A C-variadic fn pointer must keep its `extern "C"` ABI: a Rust-ABI
            // variadic is illegal (E0045). Such a pointer is only ever held by
            // identity (never called on the heap path -- its call site is
            // rewritten to a trace), so the panic-abort concern that motivates
            // the Rust-ABI rewrite does not apply to it.
            if f.variadic.is_none() {
                f.abi = None;
            }
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
        // Modelled scalar `static mut` globals: public so the harness can read
        // and compare each version's final value.
        syn::Item::Static(s) => {
            s.attrs.clear();
            s.vis = public;
        }
        _ => {}
    }
}
