//! Generating symbolic heaps and structural comparison for pointer inputs.
//!
//! This is the start of milestone 1 (see `drafts/plan.md`): given a struct
//! from the [`CrateIndex`], emit Kani code that
//!
//! - builds a bounded symbolic instance on the heap (`gen_<T>`), with each
//!   pointer field null or a fresh object one level down, to a depth bound,
//! - deep-copies that instance from `old`'s layout into `new`'s (`clone_<T>`),
//!   preserving sharing and cycles, so both versions get isomorphic inputs, and
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

use quote::ToTokens;

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
    /// A fixed-size array of a scalar (e.g. `[c_char; 32]`): each element
    /// `kani::any()`, copied whole (arrays of scalars are `Copy`), compared
    /// with `==` (arrays are `PartialEq` for every length).
    ScalarArray,
}

/// The generated builder, cloner and comparer for one struct, plus the structs
/// it points to (which the caller must also generate).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Generated {
    pub builder: String,
    /// A deep copy from `old`'s layout into `new`'s, preserving sharing and
    /// cycles, so both versions receive isomorphic symbolic heaps.
    pub cloner: String,
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
    // A fixed-size array of a scalar.
    if let syn::Type::Array(arr) = ty {
        if let Some(name) = last_segment(&arr.elem) {
            if scalar::primitive(&name).is_some()
                || scalar::c_type(&name).is_some()
                || scalar::libc_typedef(&name).is_some()
            {
                return Ok(Field::ScalarArray);
            }
        }
        return Err("array of a non-scalar element type".to_owned());
    }
    Err(format!(
        "type `{}` is not a scalar or a pointer to a struct",
        last_segment(ty).unwrap_or_else(|| "?".to_owned())
    ))
}

/// Generate the builder, cloner and comparer for one struct.
///
/// `old` and `new` are the module paths the two crates live under in the
/// scratch crate. Equivalence harnesses build a symbolic heap of `old::T`
/// (`gen_<T>`), clone it into an isomorphic `new::T` (`clone_<T>`), run both
/// versions, then compare the two heaps structurally (`same_<T>`).
pub fn generate(
    index: &CrateIndex,
    struct_name: &str,
    old: &str,
    new: &str,
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
        builder: builder(struct_name, old, &fields),
        cloner: cloner(struct_name, old, new, &fields),
        comparer: comparer(struct_name, old, new, &fields),
        referenced,
    })
}

/// Generate the builder, cloner and comparer for every struct reachable from
/// `roots` (following pointer fields), concatenated as one block of source.
/// Fails if any reachable struct has a field the generator can't handle.
pub fn generate_all(
    index: &CrateIndex,
    roots: &BTreeSet<String>,
    old: &str,
    new: &str,
) -> Result<String, Unsupported> {
    let mut done = BTreeSet::new();
    let mut queue: Vec<String> = roots.iter().cloned().collect();
    let mut out = String::new();
    while let Some(name) = queue.pop() {
        if !done.insert(name.clone()) {
            continue;
        }
        let g = generate(index, &name, old, new)?;
        out.push_str(&g.builder);
        out.push('\n');
        out.push_str(&g.cloner);
        out.push('\n');
        out.push_str(&g.comparer);
        out.push('\n');
        for r in g.referenced {
            if !done.contains(&r) {
                queue.push(r);
            }
        }
    }
    Ok(out)
}

/// How one argument or return value is supplied to the two versions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape {
    /// A scalar: `kani::any()`, copied across unchanged.
    Scalar,
    /// A raw pointer to a named struct: built with `gen_<T>` and cloned with
    /// `clone_<T>`, compared with `same_<T>`.
    Heap(String),
}

/// The shapes of a function's arguments and return value for the heap path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SigShapes {
    pub args: Vec<Shape>,
    pub ret: Shape,
    /// The structs named directly in the signature, so the caller knows which
    /// builders to generate (then closed over each one's `referenced` set).
    pub structs: BTreeSet<String>,
}

/// Classify a function signature for the heap path: every argument and the
/// return value must be a scalar or a raw pointer to a struct the generator
/// supports. The `()` return becomes [`Shape::Scalar`] (nothing to compare).
///
/// Type aliases aren't followed here (a later step): a pointer written through
/// a typedef is reported unsupported rather than silently mishandled.
pub fn signature_shapes(
    index: &CrateIndex,
    sig: &syn::Signature,
) -> Result<SigShapes, Unsupported> {
    let table = struct_table(index);
    let names: BTreeSet<&String> = table.keys().collect();
    let mut structs = BTreeSet::new();

    let shape_of = |ty: &syn::Type, structs: &mut BTreeSet<String>| -> Result<Shape, String> {
        // An empty tuple return is unit: a scalar here, with nothing to compare.
        if let syn::Type::Tuple(t) = ty {
            if t.elems.is_empty() {
                return Ok(Shape::Scalar);
            }
        }
        match classify(ty, &names)? {
            Field::Scalar(_) | Field::ScalarArray => Ok(Shape::Scalar),
            Field::Pointer(target) => {
                structs.insert(target.clone());
                Ok(Shape::Heap(target))
            }
        }
    };

    let mut args = Vec::new();
    for input in &sig.inputs {
        let syn::FnArg::Typed(pat_ty) = input else {
            return Err(Unsupported {
                struct_name: String::new(),
                field: "self".to_owned(),
                detail: "method with a receiver".to_owned(),
            });
        };
        let shape = shape_of(&pat_ty.ty, &mut structs).map_err(|detail| Unsupported {
            struct_name: String::new(),
            field: pat_ty.pat.to_token_stream().to_string(),
            detail,
        })?;
        args.push(shape);
    }

    let ret = match &sig.output {
        syn::ReturnType::Default => Shape::Scalar,
        syn::ReturnType::Type(_, ty) => {
            shape_of(ty, &mut structs).map_err(|detail| Unsupported {
                struct_name: String::new(),
                field: "<return>".to_owned(),
                detail,
            })?
        }
    };

    Ok(SigShapes { args, ret, structs })
}

/// `gen_<T>(depth) -> *mut old::T`: null below the bound or by a symbolic
/// choice, else a fresh object with symbolic scalars and recursively built
/// pointees.
fn builder(struct_name: &str, old: &str, fields: &[(String, Field)]) -> String {
    let mut inits = String::new();
    for (name, field) in fields {
        let value = match field {
            Field::Scalar(_) => "kani::any()".to_owned(),
            Field::ScalarArray => "core::array::from_fn(|_| kani::any())".to_owned(),
            Field::Pointer(target) => format!("gen_{target}(depth - 1)"),
        };
        inits += &format!("            {name}: {value},\n");
    }
    format!(
        "pub unsafe fn gen_{struct_name}(depth: usize) -> *mut {old}::{struct_name} {{\n\
         \x20   if depth == 0 || kani::any() {{\n\
         \x20       return core::ptr::null_mut();\n\
         \x20   }}\n\
         \x20   let obj = {old}::{struct_name} {{\n\
         {inits}\
         \x20   }};\n\
         \x20   Box::into_raw(Box::new(obj))\n\
         }}\n"
    )
}

/// `clone_<T>(src, map) -> *mut new::T`: a deep copy from `old`'s layout into
/// `new`'s. The pointer is registered in `map` before the fields recurse, so
/// shared objects become shared and cycles terminate instead of looping.
fn cloner(struct_name: &str, old: &str, new: &str, fields: &[(String, Field)]) -> String {
    // Scalars are copied in the initializer; pointer fields start null and are
    // filled after the object is registered, so a cycle back to it resolves.
    let mut inits = String::new();
    let mut links = String::new();
    for (name, field) in fields {
        match field {
            // Scalars and scalar arrays are `Copy`: copy them in the initializer.
            Field::Scalar(_) | Field::ScalarArray => {
                inits += &format!("        {name}: (*src).{name},\n")
            }
            Field::Pointer(target) => {
                inits += &format!("        {name}: core::ptr::null_mut(),\n");
                links += &format!("    (*dst).{name} = clone_{target}((*src).{name}, map);\n");
            }
        }
    }
    format!(
        "pub unsafe fn clone_{struct_name}(\n\
         \x20   src: *const {old}::{struct_name},\n\
         \x20   map: &mut CloneMap,\n\
         ) -> *mut {new}::{struct_name} {{\n\
         \x20   if src.is_null() {{\n\
         \x20       return core::ptr::null_mut();\n\
         \x20   }}\n\
         \x20   if let Some(dst) = map.get(src as *const ()) {{\n\
         \x20       return dst as *mut {new}::{struct_name};\n\
         \x20   }}\n\
         \x20   let dst = Box::into_raw(Box::new({new}::{struct_name} {{\n\
         {inits}\
         \x20   }}));\n\
         \x20   map.insert(src as *const (), dst as *const ());\n\
         {links}\
         \x20   dst\n\
         }}\n"
    )
}

/// `same_<T>(a, b, corr) -> bool`: equal scalars across `old::T` and `new::T`,
/// matching null-ness, and corresponding pointees, with `corr` kept functional
/// and injective.
fn comparer(struct_name: &str, old: &str, new: &str, fields: &[(String, Field)]) -> String {
    let mut checks = String::new();
    for (name, field) in fields {
        let line = match field {
            // Arrays of scalars are `PartialEq` for every length, like scalars.
            Field::Scalar(_) | Field::ScalarArray => {
                format!("    if (*a).{name} != (*b).{name} {{ return false; }}\n")
            }
            Field::Pointer(target) => format!(
                "    if !same_{target}((*a).{name}, (*b).{name}, corr) {{ return false; }}\n",
            ),
        };
        checks += &line;
    }
    // `corr` is the correspondence map; `link` returns false when adding the
    // pair would break functionality (a already mapped elsewhere) or
    // injectivity (b already mapped from elsewhere).
    format!(
        "pub unsafe fn same_{struct_name}(\n\
         \x20   a: *const {old}::{struct_name},\n\
         \x20   b: *const {new}::{struct_name},\n\
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
        let g = generate(
            &index("pub struct P { pub x: i32, pub y: u8 }"),
            "P",
            "old",
            "new",
        )
        .unwrap();
        assert!(g.referenced.is_empty());
        assert!(g.builder.contains("gen_P(depth: usize) -> *mut old::P"));
        assert!(g.builder.contains("x: kani::any(),"));
        // The comparer spans the two modules.
        assert!(g.comparer.contains("a: *const old::P,"));
        assert!(g.comparer.contains("b: *const new::P,"));
        assert!(g.comparer.contains("if (*a).x != (*b).x { return false; }"));
        assert!(g.comparer.contains("corr.link("));
        // Scalars are copied straight across in the cloner.
        assert!(g.cloner.contains("-> *mut new::P"));
        assert!(g.cloner.contains("x: (*src).x,"));
    }

    #[test]
    fn pointer_field_recurses_and_is_referenced() {
        let src = "pub struct N { pub v: i32, pub next: *mut N }";
        let g = generate(&index(src), "N", "old", "new").unwrap();
        assert_eq!(g.referenced, ["N".to_owned()].into_iter().collect());
        assert!(g.builder.contains("next: gen_N(depth - 1),"));
        assert!(g
            .comparer
            .contains("if !same_N((*a).next, (*b).next, corr) { return false; }"));
    }

    #[test]
    fn cloner_registers_before_recursing_and_nulls_pointers() {
        let src = "pub struct N { pub v: i32, pub next: *mut N }";
        let g = generate(&index(src), "N", "old", "new").unwrap();
        // The pointer field is null in the initializer...
        assert!(g.cloner.contains("next: core::ptr::null_mut(),"));
        // ...the object is registered in the map...
        let map_at = g.cloner.find("map.insert(src").unwrap();
        // ...and only then is the pointer field linked, so cycles terminate.
        let link_at = g
            .cloner
            .find("(*dst).next = clone_N((*src).next, map);")
            .unwrap();
        assert!(map_at < link_at, "must register before recursing");
    }

    #[test]
    fn scalar_array_field_builds_clones_and_compares_elementwise() {
        let src = "pub struct S { pub buf: [c_char; 32], pub n: i32 }";
        let g = generate(&index(src), "S", "old", "new").unwrap();
        assert!(g.referenced.is_empty());
        // Built per element, so elements are independently symbolic.
        assert!(g
            .builder
            .contains("buf: core::array::from_fn(|_| kani::any()),"));
        // Copied whole (arrays of scalars are Copy).
        assert!(g.cloner.contains("buf: (*src).buf,"));
        // Compared with `==` (arrays are PartialEq for every length).
        assert!(g
            .comparer
            .contains("if (*a).buf != (*b).buf { return false; }"));
    }

    #[test]
    fn array_of_non_scalar_is_unsupported() {
        let src = "pub struct S { pub kids: [*mut S; 4] }";
        let err = generate(&index(src), "S", "old", "new").unwrap_err();
        assert_eq!(err.field, "kids");
        assert!(err.detail.contains("array"));
    }

    #[test]
    fn c_type_and_typedef_fields_are_scalars() {
        let src = "pub struct S { pub a: c_int, pub b: size_t, pub c: f64 }";
        let g = generate(&index(src), "S", "old", "new").unwrap();
        assert!(g.referenced.is_empty());
        // Three field initializers (the null-guard also calls `kani::any()`).
        assert_eq!(g.builder.matches("kani::any(),").count(), 3);
    }

    #[test]
    fn pointer_to_unknown_type_is_unsupported() {
        let src = "pub struct S { pub p: *mut FILE }";
        let err = generate(&index(src), "S", "old", "new").unwrap_err();
        assert_eq!(err.field, "p");
        assert!(err.detail.contains("FILE"));
    }

    #[test]
    fn unsupported_field_type_bails() {
        // A function pointer field: not yet handled.
        let src = "pub struct S { pub f: Option<unsafe extern \"C\" fn()> }";
        let err = generate(&index(src), "S", "old", "new").unwrap_err();
        assert_eq!(err.field, "f");
    }

    fn sig(s: &str) -> syn::Signature {
        let f: syn::ItemFn = syn::parse_str(&format!("{s} {{ unimplemented!() }}")).unwrap();
        f.sig
    }

    #[test]
    fn signature_mixing_scalars_and_heap_pointers() {
        let idx = index("pub struct T { pub v: i32, pub next: *mut T }");
        let s = signature_shapes(&idx, &sig("fn f(n: *mut T, k: i32) -> *mut T")).unwrap();
        assert_eq!(s.args, vec![Shape::Heap("T".to_owned()), Shape::Scalar]);
        assert_eq!(s.ret, Shape::Heap("T".to_owned()));
        assert_eq!(s.structs, ["T".to_owned()].into_iter().collect());
    }

    #[test]
    fn scalar_only_signature_names_no_structs() {
        let idx = index("pub struct T { pub v: i32 }");
        let s = signature_shapes(&idx, &sig("fn f(a: c_int) -> size_t")).unwrap();
        assert_eq!(s.args, vec![Shape::Scalar]);
        assert_eq!(s.ret, Shape::Scalar);
        assert!(s.structs.is_empty());
    }

    #[test]
    fn unit_return_is_a_scalar_shape() {
        let idx = index("pub struct T { pub v: i32 }");
        let s = signature_shapes(&idx, &sig("fn f(a: i32)")).unwrap();
        assert_eq!(s.ret, Shape::Scalar);
    }

    #[test]
    fn generate_all_closes_over_referenced_structs() {
        let src = "pub struct A { pub b: *mut B, pub x: i32 }\npub struct B { pub y: i32 }";
        let roots = ["A".to_owned()].into_iter().collect();
        let code = generate_all(&index(src), &roots, "old", "new").unwrap();
        // Reached A directly and B through A's pointer field.
        assert!(code.contains("gen_A(depth: usize) -> *mut old::A"));
        assert!(code.contains("gen_B(depth: usize) -> *mut old::B"));
        assert!(code.contains("clone_B("));
        assert!(code.contains("same_B("));
    }

    #[test]
    fn generate_all_fails_on_an_unsupported_reachable_struct() {
        let src = "pub struct A { pub b: *mut B }\npub struct B { pub f: *mut FILE }";
        let roots = ["A".to_owned()].into_iter().collect();
        let err = generate_all(&index(src), &roots, "old", "new").unwrap_err();
        assert_eq!(err.struct_name, "B");
    }

    #[test]
    fn pointer_to_unknown_struct_in_signature_is_unsupported() {
        let idx = index("pub struct T { pub v: i32 }");
        let err = signature_shapes(&idx, &sig("fn f(p: *mut FILE)")).unwrap_err();
        assert_eq!(err.field, "p");
        assert!(err.detail.contains("FILE"));
    }
}
