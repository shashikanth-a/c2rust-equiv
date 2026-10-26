//! Scalar types: the only argument and return types checked in this version.

/// What kind of inputs to generate for a scalar type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarKind {
    Int,
    Float,
    Bool,
    Char,
    Unit,
}

/// The kind of a Rust primitive type, e.g. `i32`.
pub fn primitive(name: &str) -> Option<ScalarKind> {
    Some(match name {
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128"
        | "usize" => ScalarKind::Int,
        "f32" | "f64" => ScalarKind::Float,
        "bool" => ScalarKind::Bool,
        "char" => ScalarKind::Char,
        _ => return None,
    })
}

/// The kind of a C type from `core::ffi`, `std::ffi`, `std::os::raw` or `libc`, e.g. `c_int`.
pub fn c_type(name: &str) -> Option<ScalarKind> {
    Some(match name {
        "c_char" | "c_schar" | "c_uchar" | "c_short" | "c_ushort" | "c_int" | "c_uint"
        | "c_long" | "c_ulong" | "c_longlong" | "c_ulonglong" => ScalarKind::Int,
        "c_float" | "c_double" => ScalarKind::Float,
        _ => return None,
    })
}

/// The Rust primitive for a `libc` integer typedef with a fixed equivalent, e.g. `size_t`.
pub fn libc_typedef(name: &str) -> Option<&'static str> {
    Some(match name {
        "size_t" | "uintptr_t" => "usize",
        "ssize_t" | "intptr_t" | "ptrdiff_t" => "isize",
        "int8_t" => "i8",
        "int16_t" => "i16",
        "int32_t" => "i32",
        "int64_t" => "i64",
        "uint8_t" => "u8",
        "uint16_t" => "u16",
        "uint32_t" => "u32",
        "uint64_t" => "u64",
        _ => return None,
    })
}

/// Whether `segs` names a module that defines the C types in [`c_type`].
pub fn is_ffi_module(segs: &[String]) -> bool {
    match segs {
        [a, b] => (a == "core" || a == "std") && b == "ffi",
        [a, b, c] => a == "std" && b == "os" && c == "raw",
        _ => false,
    }
}

/// The identifiers of a path's segments, without generic arguments.
pub fn idents(path: &syn::Path) -> Vec<String> {
    path.segments.iter().map(|s| s.ident.to_string()).collect()
}
