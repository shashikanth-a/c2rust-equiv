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
//!
//! The string-duplication hook `xmlMemStrdup` is handled the same way, with a
//! native allocate-and-copy shim over the NUL-terminated input, matching its
//! default (`xmlMemStrdup == xmlStrdup`, i.e. a `strdup`).

use syn::visit::Visit;

/// The allocator globals this models. `size_t` is `usize` in libxml2's output,
/// so the shims take `usize`.
const GLOBALS: &[&str] = &[
    "xmlMalloc",
    "xmlMallocAtomic",
    "xmlRealloc",
    "xmlFree",
    "xmlMemStrdup",
    // The C standard I/O streams: foreign `*mut FILE` globals libxml2 writes to
    // through `fprintf`/`fputc` (themselves modelled as observable traces) or
    // stashes as a `void*` user-data handle. They are opaque stream identities,
    // never dereferenced, so a module-local non-null sentinel (identical in both
    // versions) models them -- spelled `*mut c_void` so the definition needn't
    // pull the `FILE` struct, matching the `__stderrp as *mut c_void` use sites.
    "__stderrp",
    "__stdoutp",
    "__stdinp",
];

/// Whether `name` is an allocator global this models.
pub fn is_alloc_global(name: &str) -> bool {
    GLOBALS.contains(&name)
}

/// Whether `call` is a call through a modelled allocator-hook global, i.e.
/// `xmlMalloc.expect("..")(..)` / `xmlFree.unwrap()(..)`. Such a call is *not*
/// a general indirect call to reject: [`inject`] gives the global a concrete
/// `Some(shim)` definition pointing at Kani's modelled `malloc`/`realloc`/
/// `free`, so the `.expect()` unwraps to a real function and the call works
/// natively (and allocates valid memory). Both versions get the same
/// definition, so they stay comparable. This gates the eligibility checks so
/// such a call -- which dominates libxml2 -- is admitted.
pub fn is_alloc_hook_call(call: &syn::ExprCall) -> bool {
    let syn::Expr::MethodCall(mc) = &*call.func else {
        return false;
    };
    if mc.method != "expect" && mc.method != "unwrap" {
        return false;
    }
    match &*mc.receiver {
        syn::Expr::Path(p) => p
            .path
            .get_ident()
            .is_some_and(|id| is_alloc_global(&id.to_string())),
        _ => false,
    }
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
unsafe extern "C" fn __equiv_strdup(s: *const ::core::ffi::c_char) -> *mut ::core::ffi::c_char {
    if s.is_null() {
        return ::core::ptr::null_mut();
    }
    let mut n: usize = 0;
    while *s.add(n) != 0 {
        n += 1;
    }
    let p = __equiv_malloc_sym(n + 1) as *mut ::core::ffi::c_char;
    if !p.is_null() {
        let mut i: usize = 0;
        while i <= n {
            *p.add(i) = *s.add(i);
            i += 1;
        }
    }
    p
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
        // The string-duplication hook `xmlStrdupFunc`. Modelled by a native
        // allocate-and-copy shim over the NUL-terminated input (`gen_cstr`
        // guarantees termination), so both versions produce a fresh buffer with
        // identical content -- compared by correspondence + content like any
        // heap string. `xmlMemStrdup == xmlStrdup` is libxml2's default.
        "xmlMemStrdup" => "static mut xmlMemStrdup: Option<unsafe extern \"C\" fn(*const ::core::ffi::c_char) -> *mut ::core::ffi::c_char> = Some(__equiv_strdup);",
        // A non-null sentinel stream identity, the same in both versions. Never
        // dereferenced (every I/O call on it is a modelled trace); a function
        // that checks `!is_null()` sees the same answer in both.
        "__stderrp" | "__stdoutp" | "__stdinp" => {
            match name {
                "__stderrp" => "static mut __stderrp: *mut ::core::ffi::c_void = 1usize as *mut ::core::ffi::c_void;",
                "__stdoutp" => "static mut __stdoutp: *mut ::core::ffi::c_void = 1usize as *mut ::core::ffi::c_void;",
                _ => "static mut __stdinp: *mut ::core::ffi::c_void = 1usize as *mut ::core::ffi::c_void;",
            }
        }
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
    let names: Vec<&str> = GLOBALS
        .iter()
        .copied()
        .filter(|g| used.0.contains(*g))
        .collect();
    if names.is_empty() {
        return;
    }
    // Drop any `extern` declaration of an allocator global we're about to
    // define module-locally, so the two don't collide; prune foreign blocks
    // left empty.
    for item in items.iter_mut() {
        if let syn::Item::ForeignMod(m) = item {
            m.items.retain(|it| {
                !matches!(it, syn::ForeignItem::Static(s) if is_alloc_global(&s.ident.to_string()))
            });
        }
    }
    items.retain(|it| !matches!(it, syn::Item::ForeignMod(m) if m.items.is_empty()));
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
        let src = it
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(src.contains("static mut xmlMalloc"));
        assert!(src.contains("fn __equiv_malloc"));
        assert!(src.contains("link_name = \"malloc\""));
        // Unreferenced globals are not defined.
        assert!(!src.contains("static mut xmlFree"));
    }

    #[test]
    fn strdup_hook_is_defined_when_used() {
        let mut it = items(
            "pub unsafe fn f(s: *const ::core::ffi::c_char) -> *mut ::core::ffi::c_char { \
               xmlMemStrdup.expect(\"\")(s) \
             }",
        );
        inject(&mut it);
        let src = it
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(src.contains("static mut xmlMemStrdup"));
        assert!(src.contains("fn __equiv_strdup"));
        assert!(!src.contains("static mut xmlMalloc :"));
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
        let src = it
            .iter()
            .map(|i| i.to_token_stream().to_string())
            .collect::<String>();
        assert!(src.contains("static mut xmlFree"));
        assert!(src.contains("static mut xmlRealloc"));
        assert!(!src.contains("static mut xmlMalloc :"));
    }
}
