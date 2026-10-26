//! Extracting functions and their callee closures from a crate.

use c2rust_equiv::{extract, CrateIndex};

const LIB: &str = r#"
use ::libc;
extern "C" {
    fn helper(x: libc::c_int) -> libc::c_int;
    fn abs(x: libc::c_int) -> libc::c_int;
    static mut counter: libc::c_int;
}
pub type size_t = libc::c_ulong;
pub const LIMIT: size_t = 16;

#[no_mangle]
pub unsafe extern "C" fn uses_helper(x: libc::c_int) -> libc::c_int {
    helper(x).wrapping_add(1)
}
#[no_mangle]
pub unsafe extern "C" fn uses_alias(n: size_t) -> size_t {
    if n > LIMIT { LIMIT } else { n }
}
#[no_mangle]
pub unsafe extern "C" fn uses_abs(x: libc::c_int) -> libc::c_int {
    abs(x)
}
#[no_mangle]
pub unsafe extern "C" fn uses_global(x: libc::c_int) -> libc::c_int {
    counter + x
}
#[no_mangle]
pub unsafe extern "C" fn prints(x: libc::c_int) -> libc::c_int {
    println!("{}", x);
    x
}
#[no_mangle]
pub unsafe extern "C" fn takes_ptr(p: *mut libc::c_int) -> libc::c_int {
    *p
}
pub fn uses_std(x: i32) -> i32 {
    std::cmp::max(x, 0)
}
"#;

const OTHER: &str = r#"
use ::libc;
#[no_mangle]
pub unsafe extern "C" fn helper(x: libc::c_int) -> libc::c_int {
    x.wrapping_mul(2)
}
"#;

fn index() -> CrateIndex {
    let mut index = CrateIndex::default();
    index.add_source("src/lib.rs", LIB).unwrap();
    index.add_source("src/other.rs", OTHER).unwrap();
    index
}

fn category(name: &str) -> Result<String, String> {
    let index = index();
    let [e] = index.find_functions(name)[..] else {
        panic!("{name} not found")
    };
    match extract(&index, e) {
        Ok(unit) => Ok(unit.source()),
        Err(skip) => Err(skip.category),
    }
}

#[test]
fn foreign_declaration_resolves_to_definition() {
    let source = category("uses_helper").unwrap();
    assert!(
        source.contains("pub unsafe extern \"C\" fn helper"),
        "{source}"
    );
    assert!(source.contains("::core::ffi::c_int"), "{source}");
    assert!(!source.contains("libc"), "{source}");
}

#[test]
fn aliases_and_constants_are_included() {
    let source = category("uses_alias").unwrap();
    assert!(
        source.contains("pub type size_t = ::core::ffi::c_ulong;"),
        "{source}"
    );
    assert!(source.contains("pub const LIMIT: size_t = 16;"), "{source}");
}

#[test]
fn std_paths_are_kept() {
    let source = category("uses_std").unwrap();
    assert!(source.contains("std::cmp::max"), "{source}");
}

#[test]
fn out_of_scope_functions_are_skipped() {
    assert_eq!(category("uses_abs"), Err("foreign call".into()));
    assert_eq!(category("uses_global"), Err("global".into()));
    assert_eq!(category("prints"), Err("io".into()));
    assert_eq!(category("takes_ptr"), Err("raw pointer".into()));
}

#[test]
fn ids_name_file_and_function() {
    let index = index();
    let ids: Vec<String> = index.functions().map(|e| index.id(e)).collect();
    assert!(ids.contains(&"src/lib.rs::uses_helper".to_owned()));
    assert!(ids.contains(&"src/other.rs::helper".to_owned()));
}
