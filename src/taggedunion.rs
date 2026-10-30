//! Inferring the discriminant of a tagged union, so the heap path can build it.
//!
//! A C tagged union is a struct holding a discriminant (an enum) and a union
//! whose live field is chosen by that discriminant, e.g. json-c's `json_object`
//! with `o_type: json_type` tagging `o: data`. To build or compare one soundly
//! the generator must know, for each discriminant value, which union field is
//! live: building the wrong field would read a scalar as a pointer and
//! dereference it, a false counterexample. Kani/CBMC will not catch this for
//! us -- a union read just reads the bytes -- so the map must be correct.
//!
//! The map is assembled from independent sources and accepted only when they
//! agree; a conflict makes the union unsupported rather than guessed:
//!
//! - [`mine_accessors`]: read it from `match (*x).tag { D => ... (*x).u.field ... }`
//!   arms across the crate (the primary, automatic source);
//! - [`TagMap::merge`]: fold in another source (a constructor-dataflow pass, or
//!   an explicit annotation) and detect conflicts.
//!
//! This module only *infers* the map. The generator in `heapgen` consumes it to
//! emit a tag-consistent builder, cloner and comparer.

use std::collections::BTreeMap;

use crate::crate_index::CrateIndex;

/// A tagged union found in a struct: the union-typed field, the discriminant
/// field tagging it, and which union sub-field each discriminant selects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TagMap {
    /// The struct field of union type (e.g. `o`).
    pub union_field: String,
    /// The struct field holding the discriminant (e.g. `o_type`).
    pub tag_field: String,
    /// Each discriminant (the full path as written, e.g.
    /// `json_type::json_type_boolean`) to the union sub-field it selects
    /// (e.g. `c_boolean`). A discriminant with no union access (e.g. a null
    /// variant) maps to `None`.
    pub variants: BTreeMap<String, Option<String>>,
}

impl TagMap {
    /// Fold another source's observations into this map. Agreement strengthens
    /// confidence; a real conflict -- a discriminant selecting two *different*
    /// fields, or a different tag field -- returns `None`, so the union is left
    /// unsupported rather than built from a guess.
    ///
    /// `None` for a discriminant means only that a source saw no union access
    /// under it (absence of evidence, e.g. an arm returning a cached value), so
    /// a definite `Some(field)` dominates it rather than conflicting.
    pub fn merge(mut self, other: &TagMap) -> Option<TagMap> {
        if self.union_field != other.union_field || self.tag_field != other.tag_field {
            return None;
        }
        for (disc, field) in &other.variants {
            if !combine(self.variants.entry(disc.clone()).or_insert(None), field) {
                return None;
            }
        }
        Some(self)
    }
}

/// Fold a newly observed field selection into an existing one for the same
/// discriminant. A definite field dominates "no access seen" (`None`);
/// returns `false` only on a real conflict of two different definite fields.
fn combine(existing: &mut Option<String>, observed: &Option<String>) -> bool {
    match (&existing, observed) {
        (Some(a), Some(b)) if a != b => false,
        (None, Some(_)) => {
            *existing = observed.clone();
            true
        }
        _ => true,
    }
}

/// The member name of a field-access expression's outermost `.member`, peeling
/// a single leading deref, e.g. `(*x).o_type` -> `o_type`, `x.o_type` ->
/// `o_type`. `None` for anything else.
fn field_member(expr: &syn::Expr) -> Option<String> {
    if let syn::Expr::Field(f) = expr {
        if let syn::Member::Named(id) = &f.member {
            return Some(id.to_string());
        }
    }
    None
}

/// Whether `expr` is an access `_.<union_field>.<sub>` with `sub` in
/// `subfields`; if so, the selected sub-field name.
fn union_subfield_access(
    expr: &syn::Expr,
    union_field: &str,
    subfields: &[String],
) -> Option<String> {
    let syn::Expr::Field(outer) = expr else {
        return None;
    };
    let syn::Member::Named(sub) = &outer.member else {
        return None;
    };
    let sub = sub.to_string();
    if !subfields.contains(&sub) {
        return None;
    }
    // The base must itself be `_.<union_field>`.
    if field_member(&outer.base).as_deref() == Some(union_field) {
        Some(sub)
    } else {
        None
    }
}

/// Collect every union sub-field accessed anywhere inside an expression.
fn accessed_subfields(expr: &syn::Expr, union_field: &str, subfields: &[String]) -> Vec<String> {
    use syn::visit::Visit;
    struct V<'a> {
        union_field: &'a str,
        subfields: &'a [String],
        found: Vec<String>,
    }
    impl<'a, 'ast> Visit<'ast> for V<'a> {
        fn visit_expr(&mut self, e: &'ast syn::Expr) {
            if let Some(sub) = union_subfield_access(e, self.union_field, self.subfields) {
                if !self.found.contains(&sub) {
                    self.found.push(sub);
                }
            }
            syn::visit::visit_expr(self, e);
        }
    }
    let mut v = V {
        union_field,
        subfields,
        found: Vec::new(),
    };
    v.visit_expr(expr);
    v.found
}

/// The discriminant path a match arm's pattern names (e.g.
/// `json_type::json_type_boolean`), or `None` for a wildcard, binding, or other
/// non-path pattern.
fn arm_discriminant(pat: &syn::Pat) -> Option<String> {
    use quote::ToTokens;
    match pat {
        syn::Pat::Path(p) => Some(p.path.to_token_stream().to_string().replace(' ', "")),
        // `Enum::Variant(..)` or `Enum::Variant { .. }` shaped tags, just in case.
        syn::Pat::TupleStruct(t) => Some(t.path.to_token_stream().to_string().replace(' ', "")),
        _ => None,
    }
}

/// Mine the crate's function bodies for the tag map of one struct's union
/// field, from `match _.<tag> { D => ... _.<union_field>.<sub> ... }` arms.
///
/// `union_field` is the struct's union-typed field and `subfields` the union's
/// members. Returns `None` if no match statement implicates the field, or if
/// the evidence conflicts (the same discriminant selecting two sub-fields, or
/// two different candidate tag fields), in which case the union stays
/// unsupported rather than guessed.
pub fn mine_accessors(
    index: &CrateIndex,
    union_field: &str,
    subfields: &[String],
) -> Option<TagMap> {
    use syn::visit::Visit;

    struct Miner<'a> {
        union_field: &'a str,
        subfields: &'a [String],
        tag_field: Option<String>,
        variants: BTreeMap<String, Option<String>>,
        conflict: bool,
    }
    impl<'a, 'ast> Visit<'ast> for Miner<'a> {
        fn visit_expr_match(&mut self, m: &'ast syn::ExprMatch) {
            // Does any arm of this match touch our union field?
            let touches = m
                .arms
                .iter()
                .any(|a| !accessed_subfields(&a.body, self.union_field, self.subfields).is_empty());
            if touches {
                if let Some(tag) = field_member(&m.expr) {
                    self.record(&tag, m);
                }
            }
            syn::visit::visit_expr_match(self, m);
        }
    }
    impl<'a> Miner<'a> {
        fn record(&mut self, tag: &str, m: &syn::ExprMatch) {
            match &self.tag_field {
                // A second, different tag field for the same union is a
                // conflict: we can't tell which discriminates it.
                Some(t) if t != tag => {
                    self.conflict = true;
                    return;
                }
                Some(_) => {}
                None => self.tag_field = Some(tag.to_owned()),
            }
            for arm in &m.arms {
                let Some(disc) = arm_discriminant(&arm.pat) else {
                    continue;
                };
                let subs = accessed_subfields(&arm.body, self.union_field, self.subfields);
                // An arm touching several union fields (generic copy code) is
                // ambiguous; skip it rather than record a wrong pairing.
                let field = match subs.as_slice() {
                    [] => None,
                    [one] => Some(one.clone()),
                    _ => continue,
                };
                if !combine(self.variants.entry(disc).or_insert(None), &field) {
                    self.conflict = true;
                }
            }
        }
    }

    let mut miner = Miner {
        union_field,
        subfields,
        tag_field: None,
        variants: BTreeMap::new(),
        conflict: false,
    };
    for entry in &index.entries {
        if let Some(syn::Item::Fn(f)) = &entry.item {
            miner.visit_item_fn(f);
        }
    }
    if miner.conflict {
        return None;
    }
    let tag_field = miner.tag_field?;
    // At least one discriminant must select a real field, or there's nothing
    // to build.
    if !miner.variants.values().any(|v| v.is_some()) {
        return None;
    }
    Some(TagMap {
        union_field: union_field.to_owned(),
        tag_field,
        variants: miner.variants,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn index(src: &str) -> CrateIndex {
        let mut index = CrateIndex::default();
        index.add_source("lib.rs", src).unwrap();
        index
    }

    const SUBS: &[&str] = &["c_boolean", "c_double", "c_int64"];

    fn subs() -> Vec<String> {
        SUBS.iter().map(|s| s.to_string()).collect()
    }

    // Two accessors, as c2rust emits them, that agree on the mapping.
    const ACCESSORS: &str = r#"
        pub unsafe fn get_boolean(jso: *const json_object) -> i32 {
            match (*jso).o_type {
                json_type::json_type_boolean => return (*jso).o.c_boolean,
                json_type::json_type_int => return ((*jso).o.c_int64 != 0) as i32,
                json_type::json_type_double => return ((*jso).o.c_double != 0.0) as i32,
                _ => return 0,
            }
        }
        pub unsafe fn get_int64(jso: *const json_object) -> i64 {
            match (*jso).o_type {
                json_type::json_type_int => return (*jso).o.c_int64,
                json_type::json_type_boolean => return (*jso).o.c_boolean as i64,
                json_type::json_type_double => return (*jso).o.c_double as i64,
                _ => return 0,
            }
        }
    "#;

    #[test]
    fn mines_tag_field_and_variant_map_from_accessors() {
        let m = mine_accessors(&index(ACCESSORS), "o", &subs()).unwrap();
        assert_eq!(m.tag_field, "o_type");
        assert_eq!(m.union_field, "o");
        assert_eq!(
            m.variants.get("json_type::json_type_boolean"),
            Some(&Some("c_boolean".to_owned()))
        );
        assert_eq!(
            m.variants.get("json_type::json_type_int"),
            Some(&Some("c_int64".to_owned()))
        );
        assert_eq!(
            m.variants.get("json_type::json_type_double"),
            Some(&Some("c_double".to_owned()))
        );
    }

    #[test]
    fn conflicting_accessors_abstain() {
        // A second accessor that maps `boolean` to the wrong field.
        let bad = format!(
            "{ACCESSORS}\n pub unsafe fn wrong(jso: *const json_object) -> i64 {{ \
             match (*jso).o_type {{ json_type::json_type_boolean => return (*jso).o.c_int64, \
             _ => return 0 }} }}"
        );
        assert!(mine_accessors(&index(&bad), "o", &subs()).is_none());
    }

    #[test]
    fn no_match_on_the_union_yields_nothing() {
        let src = "pub unsafe fn f(x: i32) -> i32 { match x { 0 => 1, _ => 2 } }";
        assert!(mine_accessors(&index(src), "o", &subs()).is_none());
    }

    #[test]
    fn merge_agreeing_sources_keeps_entries_and_detects_conflict() {
        let base = mine_accessors(&index(ACCESSORS), "o", &subs()).unwrap();
        // An annotation-style source that adds a null variant and agrees.
        let mut extra = BTreeMap::new();
        extra.insert("json_type::json_type_null".to_owned(), None);
        extra.insert(
            "json_type::json_type_boolean".to_owned(),
            Some("c_boolean".to_owned()),
        );
        let ann = TagMap {
            union_field: "o".to_owned(),
            tag_field: "o_type".to_owned(),
            variants: extra,
        };
        let merged = base.clone().merge(&ann).unwrap();
        assert_eq!(
            merged.variants.get("json_type::json_type_null"),
            Some(&None)
        );
        // A conflicting source is rejected.
        let mut bad = BTreeMap::new();
        bad.insert(
            "json_type::json_type_boolean".to_owned(),
            Some("c_int64".to_owned()),
        );
        let conflict = TagMap {
            union_field: "o".to_owned(),
            tag_field: "o_type".to_owned(),
            variants: bad,
        };
        assert!(base.merge(&conflict).is_none());
    }

    #[test]
    fn an_arm_touching_several_fields_is_skipped_not_recorded() {
        // A generic copy that reads two union fields under one discriminant:
        // ambiguous, so that discriminant simply isn't recorded.
        let src = r#"
            pub unsafe fn copy(jso: *const json_object) -> i64 {
                match (*jso).o_type {
                    json_type::json_type_int => return (*jso).o.c_int64,
                    json_type::json_type_double => {
                        let _ = (*jso).o.c_int64;
                        return (*jso).o.c_double as i64;
                    }
                    _ => return 0,
                }
            }
        "#;
        let m = mine_accessors(&index(src), "o", &subs()).unwrap();
        assert_eq!(
            m.variants.get("json_type::json_type_int"),
            Some(&Some("c_int64".to_owned()))
        );
        // The double arm touched two fields, so it was not recorded.
        assert_eq!(m.variants.get("json_type::json_type_double"), None);
    }
}
