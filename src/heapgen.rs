//! Generating symbolic heaps and structural comparison for pointer inputs.
//!
//! This is the start of milestone 1 (see `drafts/plan.md`): given a struct
//! from the [`CrateIndex`], emit Kani code that
//!
//! - builds a bounded symbolic instance on the heap (`gen_<T>`), with each
//!   pointer field null or a fresh object one level down, to a depth bound, and
//! - compares two instances structurally (`same_<T>`), following pointers
//!   through a correspondence map that must stay functional and injective, so
//!   that an object shared by two fields is distinguished from two equal
//!   objects (`specs/Heap.als`).
//!
//! It handles structs whose fields are scalars or raw pointers to other such
//! structs. Unions, function pointers, arrays and globals are later steps; a
//! field it doesn't understand yields [`Unsupported`], so the caller falls
//! back to the current scalar-only path rather than emitting unsound code.

use std::collections::{BTreeMap, BTreeSet};

use crate::crate_index::{CrateIndex, Kind};
use crate::scalar;

/// A field whose type the generator can't yet build or compare.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unsupported {
    pub struct_name: String,
    pub field: String,
    pub detail: String,
}

/// What a struct field maps to in generated code.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Field {
    /// A scalar: built with `kani::any()`, compared with `==`.
    Scalar(String),
    /// A raw pointer to a named struct: built recursively, compared through
    /// the correspondence map.
    Pointer(String),
}

/// The generated builder and comparer for one struct, plus the structs it
/// points to (which the caller must also generate).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Generated {
    pub builder: String,
    pub comparer: String,
    /// Structs this one points to, so the caller can close the set.
    pub referenced: BTreeSet<String>,
}

/// A struct the generator can read: its name and fields, in order.
struct StructDef {
    name: String,
    fields: Vec<(String, syn::Type)>,
}

fn struct_def(item: &syn::Item) -> Option<StructDef> {
    let syn::Item::Struct(s) = item else {
        return None;
    };
    let fields = match &s.fields {
        syn::Fields::Named(named) => named
            .named
            .iter()
            .map(|f| (f.ident.as_ref().unwrap().to_string(), f.ty.clone()))
            .collect(),
        // Tuple structs: fields are positional (`.0`, `.1`, ...).
        syn::Fields::Unnamed(unnamed) => unnamed
            .unnamed
            .iter()
            .enumerate()
            .map(|(i, f)| (i.to_string(), f.ty.clone()))
            .collect(),
        syn::Fields::Unit => vec![],
    };
    Some(StructDef {
        name: s.ident.to_string(),
        fields,
    })
}

/// The structs defined in a crate, by name. A name defined twice is dropped,
/// since the generator can't tell which layout a pointer refers to.
fn struct_table(index: &CrateIndex) -> BTreeMap<String, StructDef> {
    let mut table: BTreeMap<String, StructDef> = BTreeMap::new();
    let mut ambiguous: BTreeSet<String> = BTreeSet::new();
    for entry in &index.entries {
        if entry.kind != Kind::Type {
            continue;
        }
        if let Some(def) = entry.item.as_ref().and_then(struct_def) {
            if table.contains_key(&def.name) {
                ambiguous.insert(def.name.clone());
            }
            table.insert(def.name.clone(), def);
        }
    }
    for name in ambiguous {
        table.remove(&name);
    }
    table
}

/// The last path segment of a type, if it's a plain path (`a::b::C` -> `C`).
fn last_segment(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(p) if p.qself.is_none() => {
            p.path.segments.last().map(|s| s.ident.to_string())
        }
        _ => None,
    }
}

/// Classify a field type, given the set of struct names we can build.
fn classify(ty: &syn::Type, structs: &BTreeSet<&String>) -> Result<Field, String> {
    // A scalar, by its last path segment.
    if let Some(name) = last_segment(ty) {
        if scalar::primitive(&name).is_some()
            || scalar::c_type(&name).is_some()
            || scalar::libc_typedef(&name).is_some()
        {
            return Ok(Field::Scalar(name));
        }
    }
    // A raw pointer to a struct we can build.
    if let syn::Type::Ptr(ptr) = ty {
        if let Some(name) = last_segment(&ptr.elem) {
            if structs.contains(&name) {
                return Ok(Field::Pointer(name));
            }
            return Err(format!("pointer to `{name}`, which is not a plain struct"));
        }
        return Err("pointer to a non-struct type".to_owned());
    }
    Err(format!(
        "type `{}` is not a scalar or a pointer to a struct",
        last_segment(ty).unwrap_or_else(|| "?".to_owned())
    ))
}

/// Generate the builder and comparer for one struct.
///
/// `module` is the module path the struct lives under in the scratch crate
/// (`old` or `new`), so generated code names `old::T` or `new::T`.
pub fn generate(
    index: &CrateIndex,
    struct_name: &str,
    module: &str,
) -> Result<Generated, Unsupported> {
    let table = struct_table(index);
    let names: BTreeSet<&String> = table.keys().collect();
    let def = table.get(struct_name).ok_or_else(|| Unsupported {
        struct_name: struct_name.to_owned(),
        field: String::new(),
        detail: "not a plain struct in the crate".to_owned(),
    })?;

    let mut fields = Vec::new();
    let mut referenced = BTreeSet::new();
    for (name, ty) in &def.fields {
        match classify(ty, &names) {
            Ok(Field::Pointer(target)) => {
                referenced.insert(target.clone());
                fields.push((name.clone(), Field::Pointer(target)));
            }
            Ok(field) => fields.push((name.clone(), field)),
            Err(detail) => {
                return Err(Unsupported {
                    struct_name: struct_name.to_owned(),
                    field: name.clone(),
                    detail,
                })
            }
        }
    }

    Ok(Generated {
        builder: builder(struct_name, module, &fields),
        comparer: comparer(struct_name, module, &fields),
        referenced,
    })
}

fn fn_suffix(module: &str, struct_name: &str) -> String {
    format!("{module}_{struct_name}")
}

/// `gen_<module>_<T>(depth) -> *mut module::T`: null below the bound or by a
/// symbolic choice, else a fresh object with symbolic scalars and recursively
/// built pointees.
fn builder(struct_name: &str, module: &str, fields: &[(String, Field)]) -> String {
    let suffix = fn_suffix(module, struct_name);
    let mut inits = String::new();
    for (name, field) in fields {
        let value = match field {
            Field::Scalar(_) => "kani::any()".to_owned(),
            Field::Pointer(target) => format!("gen_{}(depth - 1)", fn_suffix(module, target)),
        };
        inits += &format!("            {name}: {value},\n");
    }
    format!(
        "pub unsafe fn gen_{suffix}(depth: usize) -> *mut {module}::{struct_name} {{\n\
         \x20   if depth == 0 || kani::any() {{\n\
         \x20       return core::ptr::null_mut();\n\
         \x20   }}\n\
         \x20   let obj = {module}::{struct_name} {{\n\
         {inits}\
         \x20   }};\n\
         \x20   Box::into_raw(Box::new(obj))\n\
         }}\n"
    )
}

/// `same_<module>_<T>(a, b, corr) -> bool`: equal scalars, matching null-ness,
/// and corresponding pointees, with `corr` kept functional and injective.
fn comparer(struct_name: &str, module: &str, fields: &[(String, Field)]) -> String {
    let suffix = fn_suffix(module, struct_name);
    let mut checks = String::new();
    for (name, field) in fields {
        let line = match field {
            Field::Scalar(_) => format!("    if (*a).{name} != (*b).{name} {{ return false; }}\n"),
            Field::Pointer(target) => format!(
                "    if !same_{}((*a).{name}, (*b).{name}, corr) {{ return false; }}\n",
                fn_suffix(module, target)
            ),
        };
        checks += &line;
    }
    // `corr` is the correspondence map; `link` returns false when adding the
    // pair would break functionality (a already mapped elsewhere) or
    // injectivity (b already mapped from elsewhere).
    format!(
        "pub unsafe fn same_{suffix}(\n\
         \x20   a: *const {module}::{struct_name},\n\
         \x20   b: *const {module}::{struct_name},\n\
         \x20   corr: &mut Corr,\n\
         ) -> bool {{\n\
         \x20   if a.is_null() || b.is_null() {{\n\
         \x20       return a.is_null() == b.is_null();\n\
         \x20   }}\n\
         \x20   match corr.link(a as *const (), b as *const ()) {{\n\
         \x20       Link::New => {{}}\n\
         \x20       Link::Seen => return true,\n\
         \x20       Link::Conflict => return false,\n\
         \x20   }}\n\
         {checks}\
         \x20   true\n\
         }}\n"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn index(src: &str) -> CrateIndex {
        let mut index = CrateIndex::default();
        index.add_source("lib.rs", src).unwrap();
        index
    }

    #[test]
    fn scalar_only_struct() {
        let g = generate(&index("pub struct P { pub x: i32, pub y: u8 }"), "P", "old").unwrap();
        assert!(g.referenced.is_empty());
        assert!(g.builder.contains("gen_old_P(depth: usize) -> *mut old::P"));
        assert!(g.builder.contains("x: kani::any(),"));
        assert!(g.comparer.contains("if (*a).x != (*b).x { return false; }"));
        assert!(g.comparer.contains("corr.link("));
    }

    #[test]
    fn pointer_field_recurses_and_is_referenced() {
        let src = "pub struct N { pub v: i32, pub next: *mut N }";
        let g = generate(&index(src), "N", "new").unwrap();
        assert_eq!(g.referenced, ["N".to_owned()].into_iter().collect());
        assert!(g.builder.contains("next: gen_new_N(depth - 1),"));
        assert!(g
            .comparer
            .contains("if !same_new_N((*a).next, (*b).next, corr) { return false; }"));
    }

    #[test]
    fn c_type_and_typedef_fields_are_scalars() {
        let src = "pub struct S { pub a: c_int, pub b: size_t, pub c: f64 }";
        let g = generate(&index(src), "S", "old").unwrap();
        assert!(g.referenced.is_empty());
        // Three field initializers (the null-guard also calls `kani::any()`).
        assert_eq!(g.builder.matches("kani::any(),").count(), 3);
    }

    #[test]
    fn pointer_to_unknown_type_is_unsupported() {
        let src = "pub struct S { pub p: *mut FILE }";
        let err = generate(&index(src), "S", "old").unwrap_err();
        assert_eq!(err.field, "p");
        assert!(err.detail.contains("FILE"));
    }

    #[test]
    fn unsupported_field_type_bails() {
        // A function pointer field: not yet handled.
        let src = "pub struct S { pub f: Option<unsafe extern \"C\" fn()> }";
        let err = generate(&index(src), "S", "old").unwrap_err();
        assert_eq!(err.field, "f");
    }
}
