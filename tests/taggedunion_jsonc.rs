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
    index.add_source(JSONC, &std::fs::read_to_string(JSONC).unwrap()).unwrap();

    let subfields: Vec<String> = ["c_boolean", "c_double", "c_int64", "c_object", "c_array", "c_string"]
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
