//! The generated heap code must be *provable*, not merely well-typed: this is
//! the real question for the whole approach. This assembles a Kani crate with
//! two versions of a linked-list function, the generated builder, cloner and
//! comparer, and a harness that builds a symbolic `old` heap, clones it into an
//! isomorphic `new` heap, runs both versions and compares the results with the
//! generated `same_`, then runs `cargo kani` and checks it proves equivalence.
//!
//! Ignored by default: Kani is slow and not always installed. Run with
//! `cargo test --test heapgen_kani -- --ignored` where `cargo kani` is on PATH.

use std::fs;
use std::process::Command;

use c2rust_equiv::{heapgen, CrateIndex};

/// The real heap-support types (`Corr`, `Link`, `CloneMap`) from the template.
fn heap_support() -> String {
    let support = include_str!("../src/scratch_template/support.rs");
    let marker = "// --- Symbolic-heap support";
    let start = support.find(marker).expect("heap-support section present");
    support[start..].to_owned()
}

const DEF: &str = "pub struct Node { pub v: i32, pub tag: [u8; 2], pub next: *mut Node }";

// The two modules: each defines its own `Node` (distinct types, as the two
// crates would be) and one version of "return the last node of the list"
// (null stays null) -- the c2rust-style loop and an idiomatic rewrite. They
// are equivalent, so Kani must prove it.
const VERSIONS: &str = r#"
pub mod old {
    pub struct Node { pub v: i32, pub tag: [u8; 2], pub next: *mut Node }
    pub unsafe fn last(mut p: *mut Node) -> *mut Node {
        if p.is_null() { return core::ptr::null_mut(); }
        while !(*p).next.is_null() { p = (*p).next; }
        p
    }
}
pub mod new {
    pub struct Node { pub v: i32, pub tag: [u8; 2], pub next: *mut Node }
    pub unsafe fn last(p: *mut Node) -> *mut Node {
        if p.is_null() { return core::ptr::null_mut(); }
        let mut c = p;
        while !(*c).next.is_null() { c = (*c).next; }
        c
    }
}
"#;

fn proof_harness() -> String {
    // Depth 3 bounds the list length; unwind must cover the walk plus the guard.
    r#"
#[cfg(kani)]
mod proofs {
    use super::*;
    #[kani::proof]
    #[kani::unwind(5)]
    fn last_equiv() {
        unsafe {
            let p = gen_Node(3);
            let mut map = CloneMap::default();
            let q = clone_Node(p, &mut map);
            let ra = old::last(p);
            let rb = new::last(q);
            assert!(same_Node(ra, rb, &mut Corr::default()), "results differ");
        }
    }
}
"#
    .to_owned()
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn generated_proof_verifies() {
    let mut index = CrateIndex::default();
    index.add_source("lib.rs", DEF).unwrap();
    let g = heapgen::generate(&index, "Node", "old", "new").unwrap();

    let dir = tempfile::tempdir().unwrap();
    fs::create_dir_all(dir.path().join("src")).unwrap();
    fs::write(
        dir.path().join("Cargo.toml"),
        "[package]\nname = \"g\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\
         [workspace]\n[lints.rust]\nunexpected_cfgs = { level = \"allow\", check-cfg = [\"cfg(kani)\"] }\n",
    )
    .unwrap();
    // Assemble: both modules define Node; the two versions of `last` extend
    // them; generated code and support live at the crate root; the proof
    // harness builds, clones, runs and compares.
    let src = format!(
        "#![allow(warnings)]\n\
         {VERSIONS}\n\
         {support}\n{builder}\n{cloner}\n{comparer}\n{harness}",
        support = heap_support(),
        builder = g.builder,
        cloner = g.cloner,
        comparer = g.comparer,
        harness = proof_harness(),
    );
    fs::write(dir.path().join("src/lib.rs"), &src).unwrap();

    let out = Command::new("cargo")
        .args(["kani", "--harness", "last_equiv"])
        .current_dir(dir.path())
        .output()
        .expect("run cargo kani");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stdout.contains("VERIFICATION:- SUCCESSFUL"),
        "Kani did not prove equivalence.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
