// Consumed by the extraction integration (Subsystem A, phase A3b) and the
// check driver; exercised now by its own tests. Allow dead code until wired.
#![allow(dead_code)]

//! Compositional driver (Subsystem A, phase A3): decide which callees can be
//! replaced by a summary when checking a function pair, so the caller needn't
//! inline them.
//!
//! A callee `h` may be summarised only when `old::h` is equivalent to
//! `new::h`. The simplest sound case, handled here, is when they are
//! **token-identical** (an unchanged helper): equivalence is immediate, no
//! proof needed. The bottom-up extension -- summarise a changed callee once it
//! has itself been proven equivalent -- layers on top via a proof cache
//! (phase A4); this builds the catalog of the always-safe unchanged ones.
//!
//! A callee is summarised only if it is also *summarisable* (its write set is
//! fully havocable -- see [`crate::summary`]); otherwise it is inlined.

use std::collections::BTreeMap;

use quote::ToTokens;

use crate::crate_index::CrateIndex;
use crate::modref::write_set;
use crate::summary::summarize;

/// A function's code, ignoring formatting, comments and doc comments -- the
/// canonical form for deciding whether two versions are identical.
fn canonical(item: &syn::Item) -> Option<String> {
    let syn::Item::Fn(f) = item else { return None };
    let mut f = f.clone();
    f.attrs.retain(|a| !a.path().is_ident("doc"));
    Some(f.to_token_stream().to_string())
}

/// Build the catalog of summary shims for callees that are identical across
/// the two crates and summarisable. Keyed by function name; the shim replaces
/// the callee at its call sites in both versions.
pub fn summary_catalog(old: &CrateIndex, new: &CrateIndex) -> BTreeMap<String, syn::ItemFn> {
    // Index new's functions by name for matching.
    let mut new_by_name: BTreeMap<String, &syn::Item> = BTreeMap::new();
    for e in new.functions() {
        if let Some(item) = &new.entries[e].item {
            if let syn::Item::Fn(f) = item {
                new_by_name.insert(f.sig.ident.to_string(), item);
            }
        }
    }

    let mut catalog = BTreeMap::new();
    for e in old.functions() {
        let Some(item) = &old.entries[e].item else {
            continue;
        };
        let syn::Item::Fn(f) = item else { continue };
        let name = f.sig.ident.to_string();
        let Some(new_item) = new_by_name.get(&name) else {
            continue;
        };
        // Only unchanged callees are summarised here (sound without a proof).
        if canonical(item) != canonical(new_item) {
            continue;
        }
        if let Some(shim) = summarize(&name, &f.sig, &write_set(f)) {
            catalog.insert(name, shim);
        }
    }
    catalog
}

#[cfg(test)]
mod tests {
    use super::*;

    fn index(src: &str) -> CrateIndex {
        let mut i = CrateIndex::default();
        i.add_source("lib.rs", src).unwrap();
        i
    }

    #[test]
    fn unchanged_summarisable_callee_is_catalogued() {
        let old = index("pub unsafe fn helper(p: *mut i32, v: i32) { *p = v; }");
        let new = index("pub unsafe fn helper(p: *mut i32, v: i32) { *p = v; }");
        let cat = summary_catalog(&old, &new);
        assert!(cat.contains_key("helper"));
    }

    #[test]
    fn changed_callee_is_not_catalogued() {
        let old = index("pub unsafe fn helper(p: *mut i32, v: i32) { *p = v; }");
        let new = index("pub unsafe fn helper(p: *mut i32, v: i32) { *p = v + 1; }");
        assert!(!summary_catalog(&old, &new).contains_key("helper"));
    }

    #[test]
    fn unchanged_but_unsummarisable_callee_is_skipped() {
        // Writes a struct pointee -> not havocable -> must inline, not summarise.
        let src = "pub unsafe fn helper(p: *mut Node) { (*p).next = p; }";
        let cat = summary_catalog(&index(src), &index(src));
        assert!(!cat.contains_key("helper"));
    }

    #[test]
    fn pure_unchanged_callee_is_catalogued() {
        let src = "pub fn sq(x: i32) -> i32 { x * x }";
        assert!(summary_catalog(&index(src), &index(src)).contains_key("sq"));
    }
}
