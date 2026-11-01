//! Compositional driver: decide which callees can be
//! replaced by a summary when checking a function pair, so the caller needn't
//! inline them.
//!
//! A callee `h` may be summarised only when `old::h` is equivalent to
//! `new::h`. The simplest sound case, handled here, is when they are
//! **token-identical** (an unchanged helper): equivalence is immediate, no
//! proof needed. The bottom-up extension -- summarise a changed callee once it
//! has itself been proven equivalent -- layers on top via a proof cache
//! on top via that cache; this builds the catalog of the always-safe unchanged ones.
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
    summary_catalog_with(old, new, &std::collections::BTreeSet::new())
}

/// Like [`summary_catalog`], but a callee also qualifies when its name is in
/// `proven` -- a set of callees already shown equivalent bottom-up (RVT, phase
/// A4), cached by the check driver. Such a callee may have *changed* between
/// the versions; having been proven equivalent, replacing it by a shared
/// summary on both sides stays sound (the summary over-approximates its one
/// agreed behaviour). A still-unproven changed callee is left to be inlined.
pub fn summary_catalog_with(
    old: &CrateIndex,
    new: &CrateIndex,
    proven: &std::collections::BTreeSet<String>,
) -> BTreeMap<String, syn::ItemFn> {
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
        // A callee may be summarised when it is either unchanged (token-
        // identical -- equivalent without a proof) or already proven equivalent
        // bottom-up. Otherwise it must be inlined.
        let unchanged = canonical(item) == canonical(new_item);
        if !unchanged && !proven.contains(&name) {
            continue;
        }
        if let Some(shim) = summarize(&name, &f.sig, &write_set(f)) {
            catalog.insert(name, shim);
        }
    }
    catalog
}

/// The summary shim for one callee `name` defined in `old`, if it is
/// summarisable. Used by the check driver to add a callee that has
/// just been proven equivalent to the summary catalog, so its callers can
/// replace it with the shim instead of inlining it.
pub fn proven_shim(old: &CrateIndex, name: &str) -> Option<syn::ItemFn> {
    for e in old.functions() {
        if let Some(syn::Item::Fn(f)) = &old.entries[e].item {
            if f.sig.ident == name {
                return summarize(name, &f.sig, &write_set(f));
            }
        }
    }
    None
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
    fn changed_callee_is_catalogued_once_proven() {
        // A4: a callee that changed between versions is not in the base catalog,
        // but is summarised once the driver has proven it equivalent bottom-up.
        let old = index("pub unsafe fn helper(p: *mut i32, v: i32) { *p = v; }");
        let new = index("pub unsafe fn helper(p: *mut i32, v: i32) { *p = v + 1 - 1; }");
        assert!(!summary_catalog(&old, &new).contains_key("helper"));
        let proven = ["helper".to_owned()].into_iter().collect();
        assert!(summary_catalog_with(&old, &new, &proven).contains_key("helper"));
    }

    #[test]
    fn proven_shim_is_produced_for_a_summarisable_callee() {
        let old = index("pub unsafe fn helper(p: *mut i32, v: i32) { *p = v; }");
        assert!(proven_shim(&old, "helper").is_some());
        // A non-summarisable callee (writes a struct pointee) yields no shim.
        let o2 = index("pub unsafe fn helper(p: *mut Node) { (*p).next = p; }");
        assert!(proven_shim(&o2, "helper").is_none());
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
