//! The code `heapgen` emits must be valid Rust. This assembles the builder,
//! cloner and comparer for a linked-list struct, with the `Corr` and
//! `CloneMap` support types and a stand-in `kani::any`, and type-checks the
//! crate with `cargo build`.

use std::fs;
use std::process::Command;

use c2rust_equiv::{heapgen, CrateIndex};

const SUPPORT: &str = r#"
pub mod old { pub struct N { pub v: i32, pub next: *mut N } }
pub mod new { pub struct N { pub v: i32, pub next: *mut N } }
pub mod kani { pub fn any<T>() -> T { unimplemented!() } }

pub enum Link { New, Seen, Conflict }
#[derive(Default)]
pub struct Corr { pairs: Vec<(*const (), *const ())> }
impl Corr {
    pub fn link(&mut self, a: *const (), b: *const ()) -> Link {
        for &(x, y) in &self.pairs {
            if x == a && y == b { return Link::Seen; }
            if x == a || y == b { return Link::Conflict; }
        }
        self.pairs.push((a, b));
        Link::New
    }
}

#[derive(Default)]
pub struct CloneMap { pairs: Vec<(*const (), *const ())> }
impl CloneMap {
    pub fn get(&self, a: *const ()) -> Option<*const ()> {
        self.pairs.iter().find(|&&(x, _)| x == a).map(|&(_, y)| y)
    }
    pub fn insert(&mut self, a: *const (), b: *const ()) { self.pairs.push((a, b)); }
}
"#;

#[test]
fn generated_code_type_checks() {
    let mut index = CrateIndex::default();
    index
        .add_source("lib.rs", "pub struct N { pub v: i32, pub next: *mut N }")
        .unwrap();
    let g = heapgen::generate(&index, "N", "old", "new").unwrap();

    let dir = tempfile::tempdir().unwrap();
    fs::create_dir_all(dir.path().join("src")).unwrap();
    fs::write(
        dir.path().join("Cargo.toml"),
        "[package]\nname = \"g\"\nversion = \"0.0.0\"\nedition = \"2021\"\n[workspace]\n",
    )
    .unwrap();
    let src = format!(
        "#![allow(warnings)]\nuse kani::any;\n{SUPPORT}\n{}\n{}\n{}\n",
        g.builder, g.cloner, g.comparer
    );
    fs::write(dir.path().join("src/lib.rs"), src).unwrap();

    let out = Command::new("cargo")
        .args(["build", "--quiet"])
        .current_dir(dir.path())
        .env("CARGO_TARGET_DIR", dir.path().join("target"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "generated code did not compile:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
