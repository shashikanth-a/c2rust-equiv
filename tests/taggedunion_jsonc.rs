//! Confirm the tag-map inference recovers json-c's real `json_object` mapping
//! from the transpiled source, not just synthetic fixtures.

use std::path::Path;

use c2rust_equiv::crate_index::CrateIndex;
use c2rust_equiv::taggedunion::mine_accessors;

const JSONC: &str = "drafts/eval/examples/json-c/rust/src/json_object.rs";

#[test]
fn infers_json_object_tag_map_from_real_source() {
    if !Path::new(JSONC).exists() {
        eprintln!("skipping: {JSONC} not present");
        return;
    }
    let mut index = CrateIndex::default();
    index
        .add_source(JSONC, &std::fs::read_to_string(JSONC).unwrap())
        .unwrap();

    let subfields: Vec<String> = [
        "c_boolean",
        "c_double",
        "c_int64",
        "c_object",
        "c_array",
        "c_string",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    let m = mine_accessors(&index, "o", &subfields).expect("should infer a map");

    assert_eq!(m.tag_field, "o_type");
    // The scalar variants are the ones accessors read directly.
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
    eprintln!("inferred json_object tag map: {:#?}", m.variants);
}

#[test]
fn json_object_builds_with_union_and_opaque_field_support() {
    // json_object now generates end to end: the tag map is inferred, the
    // `string` variant's by-value nested aggregate (`C2Rust_Unnamed`) builds,
    // the object/array variants' `lh_table`/`array_list` are pulled in, and
    // json_object's own function-pointer (`_delete`/`_to_json_string`) and
    // `c_void` (`_userdata`) fields are carried as opaque identity words. (It
    // was blocked on all of these before the heap path grew those features.)
    if !Path::new(JSONC).exists() {
        eprintln!("skipping: {JSONC} not present");
        return;
    }
    let mut index = CrateIndex::default();
    index
        .add_source(JSONC, &std::fs::read_to_string(JSONC).unwrap())
        .unwrap();
    let gen =
        c2rust_equiv::heapgen::generate(&index, "json_object", &Default::default(), "old", "new")
            .expect("json_object now builds");
    // A tag-dispatched builder and comparer, with the referenced aggregates
    // pulled into the closure.
    assert!(
        gen.builder.contains("fn gen_json_object"),
        "{}",
        gen.builder
    );
    assert!(
        gen.comparer.contains("fn same_json_object"),
        "{}",
        gen.comparer
    );
    assert!(gen.referenced.contains("lh_table"));
}

// The crate-wide catalog (wall 4): a function's own closure may not contain the
// accessor that proves the union discriminant, so it is mined from the full
// crate index at extraction time and carried on the FnUnit. Here the whole
// json-c crate is indexed and a json_object-touching function extracted; its
// union_tags must carry the `o` map with the real `o_type` discriminant.
#[test]
fn crate_wide_catalog_infers_json_object_discriminant() {
    let root = Path::new("drafts/eval/examples/json-c");
    if !root.exists() {
        eprintln!("skipping: {} not present", root.display());
        return;
    }
    let index = CrateIndex::load(root).unwrap();
    let entry = index
        .find_functions("get_string_component")
        .into_iter()
        .next()
        .expect("get_string_component present");
    let unit = c2rust_equiv::extract_heap_composed(&index, entry, &Default::default())
        .expect("extracts on the heap path");
    let map = unit
        .union_tags
        .get("o")
        .expect("crate-wide catalog carries the `o` union map");
    assert_eq!(map.tag_field, "o_type");
    assert_eq!(
        map.variants.get("json_type::json_type_boolean"),
        Some(&Some("c_boolean".to_owned())),
        "boolean variant selects c_boolean"
    );
}
