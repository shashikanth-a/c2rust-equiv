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
    /// A `*const c_char`: a bounded, NUL-terminated symbolic C string, built
    /// with `gen_cstr`, copied with `clone_cstr`, compared with `same_cstr`.
    /// Only `*const` (read-only): a `*mut c_char` may be an output buffer, which
    /// this doesn't model, so it stays unsupported rather than falsely equal.
    CStr,
    /// A `*mut T`/`*const T` to a single scalar: one heap cell, built with
    /// `gen_cell`, copied with `clone_cell`, compared (post-state) with
    /// `same_cell`.
    ScalarCell,
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

/// A struct or union the generator can read: its name and fields, in order,
/// and whether it is a union (at most one field is active at a time, so only a
/// single-field union can be built without knowing which).
struct StructDef {
    name: String,
    fields: Vec<(String, syn::Type)>,
    is_union: bool,
}

fn named_fields(fields: &syn::FieldsNamed) -> Vec<(String, syn::Type)> {
    fields
        .named
        .iter()
        .map(|f| (f.ident.as_ref().unwrap().to_string(), f.ty.clone()))
        .collect()
}

fn struct_def(item: &syn::Item) -> Option<StructDef> {
    match item {
        syn::Item::Struct(s) => {
            let fields = match &s.fields {
                syn::Fields::Named(named) => named_fields(named),
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
                is_union: false,
            })
        }
        syn::Item::Union(u) => Some(StructDef {
            name: u.ident.to_string(),
            fields: named_fields(&u.fields),
            is_union: true,
        }),
        _ => None,
    }
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

/// Crate-local type aliases (`type json_bool = c_int;`), by name. A name
/// defined twice is dropped, like structs, since the target is then ambiguous.
fn alias_table(index: &CrateIndex) -> BTreeMap<String, syn::Type> {
    let mut table: BTreeMap<String, syn::Type> = BTreeMap::new();
    let mut ambiguous: BTreeSet<String> = BTreeSet::new();
    for entry in &index.entries {
        if let Some(syn::Item::Type(t)) = &entry.item {
            let name = t.ident.to_string();
            if table.contains_key(&name) {
                ambiguous.insert(name.clone());
            }
            table.insert(name, (*t.ty).clone());
        }
    }
    for name in ambiguous {
        table.remove(&name);
    }
    table
}

/// Follow crate-local type aliases to the underlying type, so a typedef'd
/// scalar or pointer is classified by what it stands for. Bounded, so an alias
/// cycle terminates rather than looping.
fn resolve_alias(ty: &syn::Type, aliases: &BTreeMap<String, syn::Type>) -> syn::Type {
    let mut ty = ty.clone();
    for _ in 0..16 {
        let Some(name) = last_segment(&ty) else { break };
        // Only resolve a bare name; a pointer or array wraps a type we keep.
        if !matches!(ty, syn::Type::Path(_)) {
            break;
        }
        match aliases.get(&name) {
            Some(next) => ty = next.clone(),
            None => break,
        }
    }
    ty
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

/// Classify a field type, given the aggregates (structs and unions) we can see
/// and the crate-local type aliases. The type is first resolved through aliases
/// (`type json_bool = c_int` -> `c_int`), then classified; a pointer's pointee
/// is likewise resolved so a `*mut Alias` reaches the struct it names.
fn classify(
    ty: &syn::Type,
    table: &BTreeMap<String, StructDef>,
    aliases: &BTreeMap<String, syn::Type>,
) -> Result<Field, String> {
    let resolved = resolve_alias(ty, aliases);
    let ty = &resolved;
    // A scalar, by its last path segment.
    if let Some(name) = last_segment(ty) {
        if scalar::primitive(&name).is_some()
            || scalar::c_type(&name).is_some()
            || scalar::libc_typedef(&name).is_some()
        {
            return Ok(Field::Scalar(name));
        }
    }
    // A raw pointer to an aggregate we can build, or a `*const c_char` C string.
    if let syn::Type::Ptr(ptr) = ty {
        // Resolve the pointee through aliases, so `*mut Alias` reaches the
        // struct (or `c_char`) it ultimately names.
        let elem = resolve_alias(&ptr.elem, aliases);
        if let Some(name) = last_segment(&elem) {
            // A read-only C string: `*const c_char`, or `*const c_uchar`
            // (libxml2's `xmlChar`), both NUL-terminated by convention. `*mut`
            // is excluded: it may be an output buffer this doesn't compare, so
            // treating it as input-only could call a divergent rewrite
            // equivalent.
            if name == "c_char" || name == "c_uchar" {
                if ptr.mutability.is_some() {
                    return Err(format!("`*mut {name}` may be an output buffer"));
                }
                return Ok(Field::CStr);
            }
            match table.get(&name) {
                // A multi-field union needs a discriminant to say which variant
                // is live; building an arbitrary one would read a scalar as a
                // pointer. Only a single-field union is unambiguous.
                Some(def) if def.is_union && def.fields.len() != 1 => {
                    return Err(format!(
                        "pointer to union `{name}`, which needs a discriminant \
                         (only single-field unions are supported)"
                    ));
                }
                Some(_) => return Ok(Field::Pointer(name)),
                // A pointer to a scalar: one heap cell holding that scalar.
                None if scalar::primitive(&name).is_some()
                    || scalar::c_type(&name).is_some()
                    || scalar::libc_typedef(&name).is_some() =>
                {
                    return Ok(Field::ScalarCell)
                }
                None => return Err(format!("pointer to `{name}`, which is not a plain aggregate")),
            }
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
    let aliases = alias_table(index);
    let def = table.get(struct_name).ok_or_else(|| Unsupported {
        struct_name: struct_name.to_owned(),
        field: String::new(),
        detail: "not a plain struct in the crate".to_owned(),
    })?;
    // A union can only be built if exactly one field is ever active; with more,
    // the generator can't tell which to construct without a discriminant.
    if def.is_union && def.fields.len() != 1 {
        return Err(Unsupported {
            struct_name: struct_name.to_owned(),
            field: String::new(),
            detail: "multi-field union needs a discriminant".to_owned(),
        });
    }

    let mut referenced = BTreeSet::new();
    // A by-value multi-field union field, if any, is handled as a tagged union
    // (its discriminant inferred); its tag and union fields are then built
    // together rather than as independent fields.
    let tagged = tagged_union(index, def, &table, &aliases, &mut referenced)?;
    let skip: BTreeSet<&str> = match &tagged {
        Some(tu) => [tu.tag_field.as_str(), tu.union_field.as_str()]
            .into_iter()
            .collect(),
        None => BTreeSet::new(),
    };

    let mut fields = Vec::new();
    for (name, ty) in &def.fields {
        if skip.contains(name.as_str()) {
            continue;
        }
        match classify(ty, &table, &aliases) {
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

    let tu = tagged.as_ref();
    Ok(Generated {
        builder: builder(struct_name, old, &fields, tu),
        cloner: cloner(struct_name, old, new, &fields, tu),
        comparer: comparer(struct_name, old, new, &fields, tu),
        referenced,
    })
}

/// If `def` has a by-value field of a multi-field union, describe it as a
/// tagged union by inferring its discriminant from the crate's accessors and
/// classifying each live sub-field. Returns `Ok(None)` when there's no such
/// field, and `Err` when the discriminant can't be inferred or a variant's
/// field type isn't buildable, so the struct falls back to unsupported.
fn tagged_union(
    index: &CrateIndex,
    def: &StructDef,
    table: &BTreeMap<String, StructDef>,
    aliases: &BTreeMap<String, syn::Type>,
    referenced: &mut BTreeSet<String>,
) -> Result<Option<TaggedUnion>, Unsupported> {
    let unsupported = |field: &str, detail: String| Unsupported {
        struct_name: def.name.clone(),
        field: field.to_owned(),
        detail,
    };

    // Find the (single) by-value multi-field union field.
    let mut found: Option<(&String, &StructDef)> = None;
    for (name, ty) in &def.fields {
        let Some(u) = last_segment(&resolve_alias(ty, aliases)).and_then(|n| table.get(&n)) else {
            continue;
        };
        if u.is_union && u.fields.len() > 1 {
            if found.is_some() {
                return Err(unsupported(name, "more than one union field".to_owned()));
            }
            found = Some((name, u));
        }
    }
    let Some((union_field, udef)) = found else {
        return Ok(None);
    };

    let subnames: Vec<String> = udef.fields.iter().map(|(n, _)| n.clone()).collect();
    let map = crate::taggedunion::mine_accessors(index, union_field, &subnames)
        .ok_or_else(|| unsupported(union_field, "could not infer the union's discriminant".to_owned()))?;
    if !def.fields.iter().any(|(n, _)| n == &map.tag_field) {
        return Err(unsupported(
            union_field,
            format!("inferred tag `{}` is not a field of the struct", map.tag_field),
        ));
    }

    let mut variants = Vec::new();
    for (disc, sub) in &map.variants {
        let classified = match sub {
            None => None,
            Some(s) => {
                let ty = udef
                    .fields
                    .iter()
                    .find(|(n, _)| n == s)
                    .map(|(_, t)| t)
                    .expect("mined sub-field is a union field");
                let field = classify(ty, table, aliases).map_err(|d| unsupported(s, d))?;
                if let Field::Pointer(t) = &field {
                    referenced.insert(t.clone());
                }
                Some((s.clone(), field))
            }
        };
        variants.push((disc.clone(), classified));
    }

    Ok(Some(TaggedUnion {
        tag_field: map.tag_field,
        union_field: union_field.clone(),
        union_type: udef.name.clone(),
        variants,
    }))
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
    /// A `*const c_char` argument: a bounded, NUL-terminated symbolic C string,
    /// built with `gen_cstr` and cloned with `clone_cstr`. Read-only, so there
    /// is no post-state to compare.
    CStr,
    /// A `*mut T`/`*const T` argument to a single scalar: one heap cell, whose
    /// post-state is compared (a divergent write through `*mut T` is caught).
    ScalarCell,
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

impl SigShapes {
    /// Whether any argument or the return value is a pointer or C string the
    /// heap path must build, so the scalar path can't handle this function.
    pub fn needs_heap(&self) -> bool {
        std::iter::once(&self.ret)
            .chain(&self.args)
            .any(|s| !matches!(s, Shape::Scalar))
    }
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
    let aliases = alias_table(index);
    let mut structs = BTreeSet::new();

    let shape_of = |ty: &syn::Type, structs: &mut BTreeSet<String>| -> Result<Shape, String> {
        // An empty tuple return is unit: a scalar here, with nothing to compare.
        if let syn::Type::Tuple(t) = ty {
            if t.elems.is_empty() {
                return Ok(Shape::Scalar);
            }
        }
        match classify(ty, &table, &aliases)? {
            Field::Scalar(_) | Field::ScalarArray => Ok(Shape::Scalar),
            Field::CStr => Ok(Shape::CStr),
            Field::ScalarCell => Ok(Shape::ScalarCell),
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
            // A returned string or scalar pointer is compared after the call.
            // Its provenance is unknown, so a read may go out of bounds; that
            // surfaces as a Kani failure (hence "not proved"), never a false
            // counterexample, and a proof means no such read occurred.
            shape_of(ty, &mut structs).map_err(|detail| Unsupported {
                struct_name: String::new(),
                field: "<return>".to_owned(),
                detail,
            })?
        }
    };

    Ok(SigShapes { args, ret, structs })
}

/// A tagged union inside a struct: the union-typed field, the discriminant
/// field, and, per discriminant (as a path like `json_type::json_type_boolean`),
/// the live sub-field and its classification. A discriminant with no payload
/// (a null variant) carries `None`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct TaggedUnion {
    tag_field: String,
    union_field: String,
    union_type: String,
    variants: Vec<(String, Option<(String, Field)>)>,
}

impl TaggedUnion {
    /// A variant with a payload, used to fill the union for null discriminants
    /// (never read) and as the `_` fallback of exhaustive matches.
    fn filler(&self) -> &(String, Field) {
        self.variants
            .iter()
            .find_map(|(_, v)| v.as_ref())
            .expect("a tagged union has at least one payload variant")
    }
}

/// The expression that builds a symbolic value for one field.
fn build_value(field: &Field) -> String {
    match field {
        Field::Scalar(_) => "kani::any()".to_owned(),
        Field::ScalarArray => "core::array::from_fn(|_| kani::any())".to_owned(),
        // `gen_cstr` yields `*mut c_char`; `as _` casts it to the field's own
        // pointer type (e.g. `*const c_uchar` for xmlChar).
        Field::CStr => "gen_cstr() as _".to_owned(),
        Field::ScalarCell => "gen_cell()".to_owned(),
        Field::Pointer(target) => format!("gen_{target}(depth - 1)"),
    }
}

/// The expression that clones one field from source access `src` into `new`.
fn clone_value(field: &Field, src: &str) -> String {
    match field {
        Field::Scalar(_) | Field::ScalarArray => src.to_owned(),
        Field::CStr => format!("clone_cstr({src} as *const core::ffi::c_char) as _"),
        Field::ScalarCell => format!("clone_cell({src})"),
        Field::Pointer(target) => format!("clone_{target}({src}, map)"),
    }
}

/// A statement comparing one field across accesses `a` and `b`, returning
/// `false` on a difference.
fn compare_stmt(field: &Field, a: &str, b: &str) -> String {
    match field {
        Field::Scalar(_) | Field::ScalarArray => {
            format!("    if {a} != {b} {{ return false; }}\n")
        }
        Field::CStr => format!(
            "    if !same_cstr({a} as *const core::ffi::c_char, {b} as *const core::ffi::c_char) {{ return false; }}\n"
        ),
        Field::ScalarCell => format!("    if !same_cell({a}, {b}) {{ return false; }}\n"),
        Field::Pointer(target) => {
            format!("    if !same_{target}({a}, {b}, corr) {{ return false; }}\n")
        }
    }
}

/// `gen_<T>(depth) -> *mut old::T`: null below the bound or by a symbolic
/// choice, else a fresh object with symbolic scalars and recursively built
/// pointees. A tagged union field picks a symbolic discriminant and builds the
/// matching variant, so the tag and the live union field are consistent.
fn builder(struct_name: &str, old: &str, fields: &[(String, Field)], tu: Option<&TaggedUnion>) -> String {
    let mut inits = String::new();
    for (name, field) in fields {
        inits += &format!("            {name}: {},\n", build_value(field));
    }
    let mut pre = String::new();
    if let Some(tu) = tu {
        let n = tu.variants.len();
        let filler = tu.filler();
        let mut arms = String::new();
        for (i, (disc, variant)) in tu.variants.iter().enumerate() {
            let (sub, field) = variant.as_ref().unwrap_or(filler);
            arms += &format!(
                "        {i}usize => ({old}::{disc}, {old}::{} {{ {sub}: {} }}),\n",
                tu.union_type,
                build_value(field),
            );
        }
        // `__k` is bounded, so the fallback arm is unreachable; it reuses
        // variant 0 only to make the match exhaustive.
        let (fd, ff) = tu.variants[0].1.as_ref().unwrap_or(filler);
        arms += &format!(
            "        _ => ({old}::{}, {old}::{} {{ {fd}: {} }}),\n",
            tu.variants[0].0,
            tu.union_type,
            build_value(ff),
        );
        pre = format!(
            "    let __k: usize = kani::any();\n\
             \x20   kani::assume(__k < {n});\n\
             \x20   let (__tag, __uni) = match __k {{\n\
             {arms}\
             \x20   }};\n"
        );
        inits += &format!("            {}: __tag,\n", tu.tag_field);
        inits += &format!("            {}: __uni,\n", tu.union_field);
    }
    format!(
        "pub unsafe fn gen_{struct_name}(depth: usize) -> *mut {old}::{struct_name} {{\n\
         \x20   if depth == 0 || kani::any() {{\n\
         \x20       return core::ptr::null_mut();\n\
         \x20   }}\n\
         {pre}\
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
fn cloner(struct_name: &str, old: &str, new: &str, fields: &[(String, Field)], tu: Option<&TaggedUnion>) -> String {
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
            // A C string is copied whole; it can't form cycles, so no linking.
            Field::CStr => {
                inits += &format!("        {name}: {},\n", clone_value(field, &format!("(*src).{name}")));
            }
            // A scalar cell: copy the pointed-to value; no cycles.
            Field::ScalarCell => {
                inits += &format!("        {name}: clone_cell((*src).{name}),\n");
            }
            Field::Pointer(target) => {
                inits += &format!("        {name}: core::ptr::null_mut(),\n");
                links += &format!("    (*dst).{name} = clone_{target}((*src).{name}, map);\n");
            }
        }
    }
    if let Some(tu) = tu {
        // The discriminant maps old -> new directly. The union is zeroed in the
        // initializer and filled after registration, so a pointer variant that
        // cycles back resolves through the map like any other pointer field.
        let tf = &tu.tag_field;
        let uf = &tu.union_field;
        let mut tag_arms = String::new();
        let mut uni_arms = String::new();
        for (disc, variant) in &tu.variants {
            tag_arms += &format!("        {old}::{disc} => {new}::{disc},\n");
            if let Some((sub, field)) = variant {
                let src = format!("(*src).{uf}.{sub}");
                uni_arms += &format!(
                    "        {old}::{disc} => {new}::{} {{ {sub}: {} }},\n",
                    tu.union_type,
                    clone_value(field, &src),
                );
            }
        }
        let (fsub, ffield) = tu.filler();
        let fsrc = format!("(*src).{uf}.{fsub}");
        let fallback = format!(
            "{new}::{} {{ {fsub}: {} }}",
            tu.union_type,
            clone_value(ffield, &fsrc),
        );
        inits += &format!(
            "        {tf}: match (*src).{tf} {{\n{tag_arms}            _ => {new}::{},\n        }},\n",
            tu.variants[0].0,
        );
        inits += &format!("        {uf}: core::mem::zeroed(),\n");
        links += &format!(
            "    (*dst).{uf} = match (*src).{tf} {{\n{uni_arms}        _ => {fallback},\n    }};\n"
        );
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
fn comparer(struct_name: &str, old: &str, new: &str, fields: &[(String, Field)], tu: Option<&TaggedUnion>) -> String {
    let mut checks = String::new();
    for (name, field) in fields {
        checks += &compare_stmt(field, &format!("(*a).{name}"), &format!("(*b).{name}"));
    }
    if let Some(tu) = tu {
        // Compare the discriminants by variant index (the tag types differ
        // across the two crates), then compare the live variant's field.
        let tf = &tu.tag_field;
        let uf = &tu.union_field;
        let mut idx_a = String::new();
        let mut idx_b = String::new();
        let mut arms = String::new();
        for (i, (disc, variant)) in tu.variants.iter().enumerate() {
            idx_a += &format!("        {old}::{disc} => {i}usize,\n");
            idx_b += &format!("        {new}::{disc} => {i}usize,\n");
            if let Some((sub, field)) = variant {
                let stmt = compare_stmt(
                    field,
                    &format!("(*a).{uf}.{sub}"),
                    &format!("(*b).{uf}.{sub}"),
                );
                arms += &format!("        {old}::{disc} => {{\n    {stmt}        }}\n");
            }
        }
        checks += &format!(
            "    let __ia = match (*a).{tf} {{\n{idx_a}        _ => usize::MAX,\n    }};\n\
             \x20   let __ib = match (*b).{tf} {{\n{idx_b}        _ => usize::MAX,\n    }};\n\
             \x20   if __ia != __ib {{ return false; }}\n\
             \x20   match (*a).{tf} {{\n{arms}        _ => {{}}\n    }}\n"
        );
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
    fn crate_local_type_aliases_are_resolved() {
        // `json_bool` aliases `c_int`; a `*mut Handle` aliases a struct pointer.
        let src = "pub type json_bool = c_int;\n\
                   pub type NodePtr = *mut N;\n\
                   pub struct N { pub v: i32 }\n\
                   pub struct S { pub flag: json_bool, pub next: NodePtr }";
        let g = generate(&index(src), "S", "old", "new").unwrap();
        // The typedef'd scalar is built like any scalar.
        assert!(g.builder.contains("flag: kani::any(),"));
        // The typedef'd pointer reaches `N` and references it.
        assert!(g.referenced.contains("N"));
        assert!(g.builder.contains("next: gen_N(depth - 1),"));
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
    fn const_c_char_field_is_a_c_string() {
        let src = "pub struct S { pub name: *const c_char, pub n: i32 }";
        let g = generate(&index(src), "S", "old", "new").unwrap();
        assert!(g.referenced.is_empty());
        // Built/cloned/compared through `gen_cstr`/`clone_cstr`/`same_cstr`,
        // with casts to the field's own pointer type (c_char vs c_uchar).
        assert!(g.builder.contains("name: gen_cstr() as _,"));
        assert!(g.cloner.contains("name: clone_cstr((*src).name as *const core::ffi::c_char) as _,"));
        assert!(g.comparer.contains("same_cstr((*a).name as *const core::ffi::c_char"));
    }

    #[test]
    fn mut_c_char_field_is_unsupported() {
        // A `*mut c_char` may be an output buffer, which isn't modelled.
        let src = "pub struct S { pub buf: *mut c_char }";
        let err = generate(&index(src), "S", "old", "new").unwrap_err();
        assert_eq!(err.field, "buf");
        assert!(err.detail.contains("output buffer"));
    }

    #[test]
    fn const_c_char_argument_is_a_c_string_shape() {
        let idx = index("pub struct T { pub v: i32 }");
        let s = signature_shapes(&idx, &sig("fn f(s: *const c_char) -> size_t")).unwrap();
        assert_eq!(s.args, vec![Shape::CStr]);
        assert_eq!(s.ret, Shape::Scalar);
        assert!(s.structs.is_empty());
        assert!(s.needs_heap());
    }

    #[test]
    fn const_c_uchar_argument_is_a_c_string_shape() {
        // libxml2's `xmlChar` is `c_uchar`; a `*const c_uchar` is a C string.
        let idx = index("pub struct T { pub v: i32 }");
        let s = signature_shapes(&idx, &sig("fn f(s: *const c_uchar) -> c_int")).unwrap();
        assert_eq!(s.args, vec![Shape::CStr]);
    }

    #[test]
    fn pointer_to_scalar_is_a_cell_shape() {
        let idx = index("pub struct T { pub v: i32 }");
        // Both a mutable out-parameter and a read-only in-parameter are cells.
        let s = signature_shapes(&idx, &sig("fn f(out: *mut c_int, inp: *const i64)")).unwrap();
        assert_eq!(s.args, vec![Shape::ScalarCell, Shape::ScalarCell]);
        // A pointer-to-scalar field is a cell too.
        let g = generate(&index("pub struct S { pub p: *mut i32 }"), "S", "old", "new").unwrap();
        assert!(g.builder.contains("p: gen_cell(),"));
        assert!(g.cloner.contains("p: clone_cell((*src).p),"));
        assert!(g.comparer.contains("if !same_cell((*a).p, (*b).p)"));
    }

    #[test]
    fn returned_c_string_is_compared() {
        // A returned `*const c_char` is compared after the call (an OOB read on
        // an unexpected provenance surfaces as "not proved", never a false
        // counterexample).
        let idx = index("pub struct T { pub v: i32 }");
        let s = signature_shapes(&idx, &sig("fn f(s: *const c_char) -> *const c_char")).unwrap();
        assert_eq!(s.ret, Shape::CStr);
    }

    #[test]
    fn mut_c_char_argument_is_unsupported() {
        let idx = index("pub struct T { pub v: i32 }");
        let err = signature_shapes(&idx, &sig("fn f(s: *mut c_char)")).unwrap_err();
        assert!(err.detail.contains("output buffer"));
    }

    #[test]
    fn single_field_union_pointer_is_built_like_a_struct() {
        // A one-field union is unambiguous: only that field can be active.
        let src = "pub struct S { pub u: *mut U }\npub union U { pub only: i32 }";
        let g = generate(&index(src), "S", "old", "new").unwrap();
        assert_eq!(g.referenced, ["U".to_owned()].into_iter().collect());
        let gu = generate(&index(src), "U", "old", "new").unwrap();
        assert!(gu.builder.contains("gen_U(depth: usize) -> *mut old::U"));
        assert!(gu.builder.contains("only: kani::any(),"));
        assert!(gu.cloner.contains("only: (*src).only,"));
        assert!(gu
            .comparer
            .contains("if (*a).only != (*b).only { return false; }"));
    }

    #[test]
    fn tagged_union_struct_builds_tag_and_variant_consistently() {
        // A struct with a discriminant and a union, plus an accessor the
        // inference mines, as c2rust emits.
        let src = r#"
            pub struct Obj { pub t: Tag, pub d: U, pub extra: i32 }
            pub union U { pub a: i32, pub b: f64 }
            pub unsafe fn val(o: *const Obj) -> i64 {
                match (*o).t {
                    Tag::A => (*o).d.a as i64,
                    Tag::B => (*o).d.b as i64,
                    _ => -1,
                }
            }
        "#;
        let g = generate(&index(src), "Obj", "old", "new").unwrap();
        // The builder picks a symbolic discriminant and builds the matching
        // variant, keeping the tag and union consistent.
        assert!(g.builder.contains("kani::assume(__k <"));
        assert!(g.builder.contains("old::Tag::A, old::U { a:"));
        assert!(g.builder.contains("old::Tag::B, old::U { b:"));
        assert!(g.builder.contains("t: __tag,"));
        assert!(g.builder.contains("d: __uni,"));
        // The cloner maps the discriminant and fills the union after
        // registration (so a cyclic pointer variant would resolve).
        assert!(g.cloner.contains("old::Tag::A => new::Tag::A"));
        assert!(g.cloner.contains("d: core::mem::zeroed(),"));
        assert!(g.cloner.contains("(*dst).d = match (*src).t"));
        // The comparer checks the discriminant matches, then the live field.
        assert!(g.comparer.contains("if __ia != __ib { return false; }"));
        assert!(g.comparer.contains("(*a).d.a != (*b).d.a"));
        // The ordinary field is still compared.
        assert!(g.comparer.contains("(*a).extra != (*b).extra"));
    }

    #[test]
    fn tagged_union_without_inferable_discriminant_is_unsupported() {
        // No accessor matches on the tag, so the discriminant can't be inferred.
        let src = "pub struct Obj { pub t: Tag, pub d: U }\npub union U { pub a: i32, pub b: f64 }";
        let err = generate(&index(src), "Obj", "old", "new").unwrap_err();
        assert_eq!(err.field, "d");
        assert!(err.detail.contains("infer"), "got: {}", err.detail);
    }

    #[test]
    fn multi_field_union_pointer_needs_a_discriminant() {
        let src =
            "pub struct S { pub u: *mut U }\npub union U { pub i: i32, pub p: *mut S }";
        let err = generate(&index(src), "S", "old", "new").unwrap_err();
        assert_eq!(err.field, "u");
        assert!(err.detail.contains("discriminant"), "got: {}", err.detail);
    }

    #[test]
    fn generating_a_multi_field_union_directly_is_unsupported() {
        let src = "pub union U { pub i: i32, pub f: f64 }";
        let err = generate(&index(src), "U", "old", "new").unwrap_err();
        assert_eq!(err.struct_name, "U");
        assert!(err.detail.contains("discriminant"));
    }

    #[test]
    fn pointer_to_unknown_struct_in_signature_is_unsupported() {
        let idx = index("pub struct T { pub v: i32 }");
        let err = signature_shapes(&idx, &sig("fn f(p: *mut FILE)")).unwrap_err();
        assert_eq!(err.field, "p");
        assert!(err.detail.contains("FILE"));
    }
}
