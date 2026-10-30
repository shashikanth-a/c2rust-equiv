//! The generated `clone_`/`same_` code must behave correctly at run time, not
//! only type-check. This builds a crate with the real heap-support types from
//! `src/scratch_template/support.rs` and the generated code for a struct with
//! two pointer fields, then exercises it on shared (diamond) and cyclic heaps:
//!
//! - a deep copy preserves sharing (two fields at one object stay shared) and
//!   terminates on cycles (a back-edge resolves to the registered copy);
//! - structural comparison accepts an isomorphic copy; and
//! - it rejects a heap that unshares one object into two equal ones, which is
//!   exactly the injectivity property `specs/Heap.als` checks.

use std::fs;
use std::process::Command;

use c2rust_equiv::{heapgen, CrateIndex};

/// The heap-support types (`Corr`, `Link`, `CloneMap`), taken from the real
/// template so the test exercises the shipped code, not a copy.
fn heap_support() -> String {
    include_str!("../src/scratch_template/heap_support.rs").to_owned()
}

// A node with two pointer fields, so a diamond and the injectivity check are
// expressible. `kani::any()` is only referenced by the (unused) builder.
const DEF: &str = "pub struct N { pub v: i32, pub l: *mut N, pub r: *mut N }";

// Driver that constructs heaps by hand, runs the generated code, and exits
// non-zero with a message on the first wrong result.
const DRIVER: &str = r#"
unsafe fn node(v: i32, l: *mut old::N, r: *mut old::N) -> *mut old::N {
    Box::into_raw(Box::new(old::N { v, l, r }))
}

fn main() {
    unsafe {
        // Diamond: root.l and root.r are the same object.
        let shared = node(7, core::ptr::null_mut(), core::ptr::null_mut());
        let root = node(1, shared, shared);

        let mut map = CloneMap::default();
        let copy = clone_N(root, &mut map);

        // Sharing preserved: the two fields of the copy point at one object.
        assert!((*copy).l == (*copy).r && !(*copy).l.is_null(), "sharing lost");
        // Distinct allocation from the source.
        assert!(copy as *const () != root as *const (), "clone aliases source");
        // Scalars copied.
        assert!((*copy).v == 1 && (*(*copy).l).v == 7, "scalars not copied");

        // An isomorphic copy compares equal.
        assert!(same_N(root, copy, &mut Corr::default()), "isomorphic copy rejected");

        // Unshare the diamond into two equal-but-distinct nodes. The injective
        // correspondence must reject this: root.l and root.r both correspond to
        // one source object, so mapping them to two partners conflicts.
        let a = Box::into_raw(Box::new(new::N { v: 7, l: core::ptr::null_mut(), r: core::ptr::null_mut() }));
        let b = Box::into_raw(Box::new(new::N { v: 7, l: core::ptr::null_mut(), r: core::ptr::null_mut() }));
        let unshared = Box::into_raw(Box::new(new::N { v: 1, l: a, r: b }));
        assert!(!same_N(root, unshared, &mut Corr::default()), "unsharing not detected");

        // A differing scalar is rejected.
        (*copy).v = 2;
        assert!(!same_N(root, copy, &mut Corr::default()), "scalar difference missed");
        (*copy).v = 1;

        // Self-cycle: clone must terminate and keep the cycle.
        let c = node(5, core::ptr::null_mut(), core::ptr::null_mut());
        (*c).l = c;
        (*c).r = c;
        let mut m2 = CloneMap::default();
        let cc = clone_N(c, &mut m2);
        assert!((*cc).l == cc && (*cc).r == cc, "cycle not preserved");
        assert!(same_N(c, cc, &mut Corr::default()), "cyclic copy rejected");

        println!("ok");
    }
}
"#;

#[test]
fn generated_code_behaves_on_shared_and_cyclic_heaps() {
    let mut index = CrateIndex::default();
    index.add_source("lib.rs", DEF).unwrap();
    let g = heapgen::generate(&index, "N", &Default::default(), "old", "new").unwrap();

    let dir = tempfile::tempdir().unwrap();
    fs::create_dir_all(dir.path().join("src")).unwrap();
    fs::write(
        dir.path().join("Cargo.toml"),
        "[package]\nname = \"g\"\nversion = \"0.0.0\"\nedition = \"2021\"\n[workspace]\n[[bin]]\nname = \"g\"\npath = \"src/main.rs\"\n",
    )
    .unwrap();
    let src = format!(
        "#![allow(warnings)]\n\
         pub mod old {{ {DEF} }}\n\
         pub mod new {{ {DEF} }}\n\
         pub mod kani {{ pub fn any<T>() -> T {{ unimplemented!() }} \
         pub trait Arbitrary {{}} impl<T> Arbitrary for T {{}} }}\n\
         use kani::any;\n\
         {support}\n{builder}\n{cloner}\n{comparer}\n{DRIVER}",
        support = heap_support(),
        builder = g.builder,
        cloner = g.cloner,
        comparer = g.comparer,
    );
    fs::write(dir.path().join("src/main.rs"), src).unwrap();

    let out = Command::new("cargo")
        .args(["run", "--quiet"])
        .current_dir(dir.path())
        .env("CARGO_TARGET_DIR", dir.path().join("target"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "driver failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "ok");
}
