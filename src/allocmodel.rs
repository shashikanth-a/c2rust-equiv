//! Modelling libxml2's allocator indirection for the heap path.
//!
//! libxml2 routes every allocation through global function pointers --
//! `xmlMalloc`, `xmlMallocAtomic`, `xmlRealloc`, `xmlFree` (declared
//! `extern "C" { static mut xmlMalloc: xmlMallocFunc; ... }` and called as
//! `xmlMalloc.expect("...")(size)`). Those globals are defined in libxml2's
//! own `globals.c`, outside any one function's unit, so extraction otherwise
//! rejects such functions as out-of-scope global access -- which is most of
//! the library.
//!
//! On the heap path, [`inject`] gives each referenced allocator global a
//! module-local definition that points at a shim calling Kani's modelled
//! `malloc`/`realloc`/`free` (reached by `#[link_name]`, so the shim's own
//! names never clash with a crate `extern` block). Both versions get identical
//! definitions, so they allocate the same way and stay comparable. The symbols
//! are reached by name, matching libxml2's default (`xmlMalloc == malloc`).

use syn::visit::Visit;

/// The allocator globals this models. `size_t` is `usize` in libxml2's output,
/// so the shims take `usize`.
const GLOBALS: &[&str] = &["xmlMalloc", "xmlMallocAtomic", "xmlRealloc", "xmlFree"];

/// Whether `name` is an allocator global this models.
pub fn is_alloc_global(name: &str) -> bool {
    GLOBALS.contains(&name)
}

/// The shims and the modelled-allocator `extern` block, shared by the globals.
const SHIMS: &str = r#"
unsafe extern "C" fn __equiv_malloc(n: usize) -> *mut ::core::ffi::c_void {
    __equiv_malloc_sym(n)
}
unsafe extern "C" fn __equiv_realloc(
    p: *mut ::core::ffi::c_void,
    n: usize,
) -> *mut ::core::ffi::c_void {
    __equiv_realloc_sym(p, n)
}
unsafe extern "C" fn __equiv_free(p: *mut ::core::ffi::c_void) {
    __equiv_free_sym(p)
}
extern "C" {
    #[link_name = "malloc"]
    fn __equiv_malloc_sym(n: usize) -> *mut ::core::ffi::c_void;
    #[link_name = "realloc"]
    fn __equiv_realloc_sym(p: *mut ::core::ffi::c_void, n: usize) -> *mut ::core::ffi::c_void;
    #[link_name = "free"]
    fn __equiv_free_sym(p: *mut ::core::ffi::c_void);
}
"#;

/// The module-local `static mut` definition for one allocator global, typed
/// identically to c2rust's `xmlMallocFunc`/`xmlReallocFunc`/`xmlFreeFunc` but
/// spelled out, so it doesn't depend on those aliases being in the unit.
fn global_def(name: &str) -> &'static str {
    match name {
        "xmlMalloc" => "static mut xmlMalloc: Option<unsafe extern \"C\" fn(usize) -> *mut ::core::ffi::c_void> = Some(__equiv_malloc);",
        "xmlMallocAtomic" => "static mut xmlMallocAtomic: Option<unsafe extern \"C\" fn(usize) -> *mut ::core::ffi::c_void> = Some(__equiv_malloc);",
        "xmlRealloc" => "static mut xmlRealloc: Option<unsafe extern \"C\" fn(*mut ::core::ffi::c_void, usize) -> *mut ::core::ffi::c_void> = Some(__equiv_realloc);",
        "xmlFree" => "static mut xmlFree: Option<unsafe extern \"C\" fn(*mut ::core::ffi::c_void)> = Some(__equiv_free);",
        _ => unreachable!(),
    }
}

/// Define every allocator global the unit references. Does nothing when none is
/// used, so non-libxml2 units are untouched.
pub fn inject(items: &mut Vec<syn::Item>) {
    let mut used = Referenced::default();
    for item in items.iter() {
        used.visit_item(item);
    }
    let names: Vec<&str> = GLOBALS.iter().copied().filter(|g| used.0.contains(*g)).collect();
    if names.is_empty() {
        return;
    }
    for item in syn::parse_file(SHIMS).expect("shims parse").items {
        items.push(item);
    }
    for name in names {
        items.push(syn::parse_str(global_def(name)).expect("global def parses"));
    }
}

/// Collects which allocator-global names appear as path identifiers.
#[derive(Default)]
struct Referenced(std::collections::BTreeSet<String>);

impl<'ast> Visit<'ast> for Referenced {
    fn visit_ident(&mut self, id: &'ast syn::Ident) {
        let s = id.to_string();
        if is_alloc_global(&s) {
            self.0.insert(s);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;

    fn items(src: &str) -> Vec<syn::Item> {
        syn::parse_file(src).unwrap().items
    }

    #[test]
    fn injects_only_referenced_globals_with_shims() {
        let mut it = items(
            "pub unsafe fn f() -> *mut u8 { \
               xmlMalloc.expect(\"\")(8) as *mut u8 \
             }",
        );
        inject(&mut it);
        let src = it.iter().map(|i| i.to_token_stream().to_string()).collect::<String>();
        assert!(src.contains("static mut xmlMalloc"));
        assert!(src.contains("fn __equiv_malloc"));
        assert!(src.contains("link_name = \"malloc\""));
        // Unreferenced globals are not defined.
        assert!(!src.contains("static mut xmlFree"));
    }

    #[test]
    fn does_nothing_without_allocator_use() {
        let mut it = items("pub fn f(x: i32) -> i32 { x + 1 }");
        let before = it.len();
        inject(&mut it);
        assert_eq!(it.len(), before);
    }

    #[test]
    fn free_and_realloc_are_defined_when_used() {
        let mut it = items(
            "pub unsafe fn f(p: *mut ::core::ffi::c_void) { \
               xmlFree.expect(\"\")(p); \
               let _ = xmlRealloc.expect(\"\")(p, 16); \
             }",
        );
        inject(&mut it);
        let src = it.iter().map(|i| i.to_token_stream().to_string()).collect::<String>();
        assert!(src.contains("static mut xmlFree"));
        assert!(src.contains("static mut xmlRealloc"));
        assert!(!src.contains("static mut xmlMalloc :"));
    }
}
