//! End-to-end test of the live heap path: drive the public `check` API on a
//! function that takes a pointer to a struct, and confirm the tool builds a
//! symbolic heap, runs both versions under Kani and proves them equivalent --
//! and that it reports a genuine difference as "not proved", never as a proof.
//!
//! Ignored by default: it runs `cargo kani`, which is slow and not always
//! installed. Run with `cargo test --test heap_check -- --ignored`.

use std::time::Duration;

use c2rust_equiv::{check, FnUnit, Options, Status};

const NODE: &str = "pub struct Node { pub v: i32, pub next: *mut Node }";

// Sum the list values into an i64, bounded by following `next`.
const OLD: &str = r#"
pub unsafe fn sum(mut p: *mut Node) -> i64 {
    let mut total: i64 = 0;
    while !p.is_null() {
        total += (*p).v as i64;
        p = (*p).next;
    }
    total
}
"#;

// An idiomatic rewrite: same behaviour, different shape.
const NEW_OK: &str = r#"
pub unsafe fn sum(p: *mut Node) -> i64 {
    let mut total = 0i64;
    let mut cur = p;
    loop {
        if cur.is_null() { return total; }
        total += (*cur).v as i64;
        cur = (*cur).next;
    }
}
"#;

// A wrong rewrite: skips the first node, so results differ.
const NEW_BAD: &str = r#"
pub unsafe fn sum(p: *mut Node) -> i64 {
    if p.is_null() { return 0; }
    let mut total = 0i64;
    let mut cur = unsafe { (*p).next };
    while !cur.is_null() {
        total += unsafe { (*cur).v } as i64;
        cur = unsafe { (*cur).next };
    }
    total
}
"#;

fn opts() -> Options {
    opts_unwind(5)
}

fn opts_unwind(unwind: u32) -> Options {
    let dir = tempfile::tempdir().unwrap().keep();
    let mut o = Options::new(dir);
    o.unwind = unwind;
    o.kani_timeout = Duration::from_secs(120);
    o
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn heap_path_proves_equivalent_rewrite() {
    let old = FnUnit::parse(OLD, &[NODE]).unwrap();
    let new = FnUnit::parse(NEW_OK, &[NODE]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn heap_path_does_not_prove_a_wrong_rewrite() {
    let old = FnUnit::parse(OLD, &[NODE]).unwrap();
    let new = FnUnit::parse(NEW_BAD, &[NODE]).unwrap();
    let outcome = check(&old, &new, &opts());
    // Soundness: a real difference must never be reported as a proof. Without a
    // native heap runner the tool can't confirm the counterexample, so it skips
    // with a reason rather than proving.
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a wrong rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// A checksum over a `*const c_char`, read as a NUL-terminated C string. The
// argument exercises the C-string path (`gen_cstr`/`clone_cstr`): both versions
// get identical symbolic strings and the scalar result is compared.
const CKSUM_OLD: &str = r#"
pub unsafe fn cksum(s: *const core::ffi::c_char) -> i64 {
    if s.is_null() { return -1; }
    let mut total: i64 = 0;
    let mut p = s;
    while *p != 0 {
        total += *p as i64;
        p = p.add(1);
    }
    total
}
"#;

// An idiomatic rewrite: index instead of a moving pointer, same behaviour.
const CKSUM_OK: &str = r#"
pub unsafe fn cksum(s: *const core::ffi::c_char) -> i64 {
    if s.is_null() { return -1; }
    let mut total = 0i64;
    let mut i = 0isize;
    loop {
        let c = *s.offset(i);
        if c == 0 { return total; }
        total += c as i64;
        i += 1;
    }
}
"#;

// A wrong rewrite: skips the first byte, so non-empty strings differ.
const CKSUM_BAD: &str = r#"
pub unsafe fn cksum(s: *const core::ffi::c_char) -> i64 {
    if s.is_null() { return -1; }
    let mut total = 0i64;
    let mut p = s.add(1);
    while *p != 0 {
        total += *p as i64;
        p = p.add(1);
    }
    total
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn c_string_path_proves_equivalent_rewrite() {
    let old = FnUnit::parse(CKSUM_OLD, &[]).unwrap();
    let new = FnUnit::parse(CKSUM_OK, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn c_string_path_does_not_prove_a_wrong_rewrite() {
    let old = FnUnit::parse(CKSUM_OLD, &[]).unwrap();
    let new = FnUnit::parse(CKSUM_BAD, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a wrong rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// A tagged union, in the shape c2rust emits: a newtype discriminant, a union,
// a struct pairing them, and an accessor the inference mines for the map.
const TU_DEFS: &[&str] = &[
    "#[derive(Copy, Clone, PartialEq, Eq)] pub struct Tag(pub u32);",
    "impl Tag { pub const A: Self = Self(0); pub const B: Self = Self(1); }",
    "#[derive(Copy, Clone)] #[repr(C)] pub union U { pub a: i32, pub b: i64 }",
    "#[repr(C)] pub struct Obj { pub t: Tag, pub d: U }",
];

// The accessor reads the live union field per the discriminant; it is both the
// function under test and the evidence the tag-map inference mines.
const TU_OLD: &str = r#"
pub unsafe fn val(o: *const Obj) -> i64 {
    if o.is_null() { return -1; }
    match (*o).t {
        Tag::A => (*o).d.a as i64,
        Tag::B => (*o).d.b,
        _ => -2,
    }
}
"#;

// An equivalent rewrite that compares the tag instead of matching.
const TU_OK: &str = r#"
pub unsafe fn val(o: *const Obj) -> i64 {
    if o.is_null() { return -1; }
    let t = (*o).t;
    if t == Tag::A { (*o).d.a as i64 }
    else if t == Tag::B { (*o).d.b }
    else { -2 }
}
"#;

// A wrong rewrite: under tag A it adds one.
const TU_BAD: &str = r#"
pub unsafe fn val(o: *const Obj) -> i64 {
    if o.is_null() { return -1; }
    match (*o).t {
        Tag::A => (*o).d.a as i64 + 1,
        Tag::B => (*o).d.b,
        _ => -2,
    }
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn tagged_union_path_proves_equivalent_rewrite() {
    let old = FnUnit::parse(TU_OLD, TU_DEFS).unwrap();
    let new = FnUnit::parse(TU_OK, TU_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn tagged_union_path_does_not_prove_a_wrong_rewrite() {
    let old = FnUnit::parse(TU_OLD, TU_DEFS).unwrap();
    let new = FnUnit::parse(TU_BAD, TU_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a wrong rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// A `sprintf` into a destination buffer: the output is modelled as a shared
// symbolic string, and the format arguments are recorded.
const SPRINTF_DECL: &str =
    "extern \"C\" { fn sprintf(_: *mut core::ffi::c_char, _: *const core::ffi::c_char, ...) -> core::ffi::c_int; }";

const SP_OLD: &str = r#"
pub unsafe fn w(d: *mut core::ffi::c_char, p: *const i32) {
    if d.is_null() || p.is_null() { return; }
    sprintf(d, b"%d\0".as_ptr() as *const core::ffi::c_char, *p);
}
"#;

const SP_OK: &str = r#"
pub unsafe fn w(d: *mut core::ffi::c_char, p: *const i32) {
    if d.is_null() || p.is_null() { return; }
    let v = *p;
    sprintf(d, b"%d\0".as_ptr() as *const core::ffi::c_char, v);
}
"#;

const SP_BAD: &str = r#"
pub unsafe fn w(d: *mut core::ffi::c_char, p: *const i32) {
    if d.is_null() || p.is_null() { return; }
    sprintf(d, b"%d\0".as_ptr() as *const core::ffi::c_char, *p + 1);
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn sprintf_proves_equivalent_rewrite() {
    let old = FnUnit::parse(SP_OLD, &[SPRINTF_DECL]).unwrap();
    let new = FnUnit::parse(SP_OK, &[SPRINTF_DECL]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn sprintf_catches_different_argument() {
    let old = FnUnit::parse(SP_OLD, &[SPRINTF_DECL]).unwrap();
    let new = FnUnit::parse(SP_BAD, &[SPRINTF_DECL]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a different sprintf argument proved equivalent: {:?}",
        outcome.status
    );
}

// A variadic `printf` call, rewritten into observable trace events: both
// versions must print the same format with the same arguments.
const PRINTF_DECL: &str =
    "extern \"C\" { fn printf(_: *const core::ffi::c_char, ...) -> core::ffi::c_int; }";

const PF_OLD: &str = r#"
pub unsafe fn h(p: *const i32) -> i32 {
    if p.is_null() { return 0; }
    printf(b"%d\0".as_ptr() as *const core::ffi::c_char, *p);
    *p
}
"#;

const PF_OK: &str = r#"
pub unsafe fn h(p: *const i32) -> i32 {
    if p.is_null() { return 0; }
    let v = *p;
    printf(b"%d\0".as_ptr() as *const core::ffi::c_char, v);
    v
}
"#;

const PF_BAD: &str = r#"
pub unsafe fn h(p: *const i32) -> i32 {
    if p.is_null() { return 0; }
    printf(b"%d\0".as_ptr() as *const core::ffi::c_char, *p + 1);
    *p
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn variadic_printf_proves_equivalent_rewrite() {
    let old = FnUnit::parse(PF_OLD, &[PRINTF_DECL]).unwrap();
    let new = FnUnit::parse(PF_OK, &[PRINTF_DECL]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn variadic_printf_catches_different_argument() {
    let old = FnUnit::parse(PF_OLD, &[PRINTF_DECL]).unwrap();
    let new = FnUnit::parse(PF_BAD, &[PRINTF_DECL]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a different printf argument proved equivalent: {:?}",
        outcome.status
    );
}

// A string-argument external (`note`) traced by content: both versions must
// pass the same string bytes, not the same address.
const NOTE_DECL: &str = "extern \"C\" { fn note(_: *const core::ffi::c_char); }";

const NOTE_OLD: &str = r#"
pub unsafe fn g(s: *const core::ffi::c_char) {
    if s.is_null() { return; }
    note(s);
}
"#;

const NOTE_OK: &str = r#"
pub unsafe fn g(s: *const core::ffi::c_char) {
    if !s.is_null() { note(s); }
}
"#;

const NOTE_BAD: &str = r#"
pub unsafe fn g(s: *const core::ffi::c_char) {
    if s.is_null() || *s == 0 { return; }
    note(s.add(1));
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn string_arg_trace_proves_equivalent_rewrite() {
    let old = FnUnit::parse(NOTE_OLD, &[NOTE_DECL]).unwrap();
    let new = FnUnit::parse(NOTE_OK, &[NOTE_DECL]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn string_arg_trace_catches_different_content() {
    let old = FnUnit::parse(NOTE_OLD, &[NOTE_DECL]).unwrap();
    let new = FnUnit::parse(NOTE_BAD, &[NOTE_DECL]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "different string content proved equivalent: {:?}",
        outcome.status
    );
}

// A side-effecting external (`emit`) modelled as an observable trace call:
// both versions must make the same calls in the same order, catching a
// divergence that the return value alone would miss.
const EMIT_DECL: &str = "extern \"C\" { fn emit(_: i32); }";

const TRACE_OLD: &str = r#"
pub unsafe fn f(p: *const i32) -> i32 {
    if p.is_null() { return 0; }
    emit(*p);
    emit(*p + 1);
    *p
}
"#;

const TRACE_OK: &str = r#"
pub unsafe fn f(p: *const i32) -> i32 {
    if p.is_null() { return 0; }
    let v = *p;
    emit(v);
    emit(v + 1);
    v
}
"#;

// Same return, but the external calls are made in the opposite order.
const TRACE_BAD: &str = r#"
pub unsafe fn f(p: *const i32) -> i32 {
    if p.is_null() { return 0; }
    emit(*p + 1);
    emit(*p);
    *p
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn external_trace_proves_equivalent_rewrite() {
    let old = FnUnit::parse(TRACE_OLD, &[EMIT_DECL]).unwrap();
    let new = FnUnit::parse(TRACE_OK, &[EMIT_DECL]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(40));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn external_trace_catches_reordered_side_effects() {
    let old = FnUnit::parse(TRACE_OLD, &[EMIT_DECL]).unwrap();
    let new = FnUnit::parse(TRACE_BAD, &[EMIT_DECL]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(16));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "reordered side effects proved equivalent: {:?}",
        outcome.status
    );
}

// A pure external function (`fmod`) modelled as an argument-keyed oracle: both
// versions calling it with equal arguments get equal results.
const FMOD_DECL: &str = "extern \"C\" { fn fmod(_: f64, _: f64) -> f64; }";

const ORACLE_OLD: &str = r#"
pub unsafe fn m(p: *const f64) -> f64 {
    if p.is_null() { return 0.0; }
    fmod(*p, 2.0)
}
"#;

const ORACLE_OK: &str = r#"
pub unsafe fn m(p: *const f64) -> f64 {
    if p.is_null() { return 0.0; }
    let two = 2.0f64;
    fmod(*p, two)
}
"#;

const ORACLE_BAD: &str = r#"
pub unsafe fn m(p: *const f64) -> f64 {
    if p.is_null() { return 0.0; }
    fmod(*p, 3.0)
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn pure_oracle_proves_equivalent_rewrite() {
    let old = FnUnit::parse(ORACLE_OLD, &[FMOD_DECL]).unwrap();
    let new = FnUnit::parse(ORACLE_OK, &[FMOD_DECL]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn pure_oracle_catches_divergent_arguments() {
    let old = FnUnit::parse(ORACLE_OLD, &[FMOD_DECL]).unwrap();
    let new = FnUnit::parse(ORACLE_BAD, &[FMOD_DECL]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "divergent oracle arguments proved equivalent: {:?}",
        outcome.status
    );
}

// A scalar `static mut` global side effect: both versions start from the same
// initializer and the harness compares the final value, catching a divergent
// global write even when the return value matches.
const GLOBAL_DEF: &str = "static mut COUNTER: i32 = 0;";

const GLOB_OLD: &str = r#"
pub unsafe fn bump(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    COUNTER += *p;
    *p
}
"#;

const GLOB_OK: &str = r#"
pub unsafe fn bump(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    COUNTER = COUNTER.wrapping_add(*p);
    *p
}
"#;

const GLOB_BAD: &str = r#"
pub unsafe fn bump(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    COUNTER += *p + 1;
    *p
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn scalar_global_side_effect_proves_equivalent_rewrite() {
    let old = FnUnit::parse(GLOB_OLD, &[GLOBAL_DEF]).unwrap();
    let new = FnUnit::parse(GLOB_OK, &[GLOBAL_DEF]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn scalar_global_side_effect_catches_divergence() {
    // Same return value, but a divergent write to the global.
    let old = FnUnit::parse(GLOB_OLD, &[GLOBAL_DEF]).unwrap();
    let new = FnUnit::parse(GLOB_BAD, &[GLOBAL_DEF]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent global write was proved equivalent: {:?}",
        outcome.status
    );
}

// A `*mut c_char` output buffer: uppercase the first byte in place. The heap
// path compares the buffer's post-state, so a divergent write is caught.
const OUTBUF_OLD: &str = r#"
pub unsafe fn up1(s: *mut core::ffi::c_char) {
    if s.is_null() || *s == 0 { return; }
    let c = *s as u8;
    if c >= b'a' && c <= b'z' { *s = (c - 32) as core::ffi::c_char; }
}
"#;

const OUTBUF_OK: &str = r#"
pub unsafe fn up1(s: *mut core::ffi::c_char) {
    if s.is_null() { return; }
    let c = *s as u8;
    if c == 0 { return; }
    if c.is_ascii_lowercase() { *s = c.to_ascii_uppercase() as core::ffi::c_char; }
}
"#;

const OUTBUF_BAD: &str = r#"
pub unsafe fn up1(s: *mut core::ffi::c_char) {
    if s.is_null() || *s == 0 { return; }
    let c = *s as u8;
    if c >= b'a' && c <= b'z' { *s = (c - 31) as core::ffi::c_char; }
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn mut_c_string_post_state_proves_equivalent_rewrite() {
    let old = FnUnit::parse(OUTBUF_OLD, &[]).unwrap();
    let new = FnUnit::parse(OUTBUF_OK, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn mut_c_string_post_state_catches_a_divergent_write() {
    let old = FnUnit::parse(OUTBUF_OLD, &[]).unwrap();
    let new = FnUnit::parse(OUTBUF_BAD, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent write was proved equivalent: {:?}",
        outcome.status
    );
}

// A function returning a C string (a pointer into its input): the heap path
// compares the returned string's content after the call.
const RET_OLD: &str = r#"
pub unsafe fn tail(s: *const core::ffi::c_char) -> *const core::ffi::c_char {
    if s.is_null() { return s; }
    if *s == 0 { s } else { s.add(1) }
}
"#;

const RET_OK: &str = r#"
pub unsafe fn tail(s: *const core::ffi::c_char) -> *const core::ffi::c_char {
    if s.is_null() || *s == 0 { return s; }
    s.offset(1)
}
"#;

const RET_BAD: &str = r#"
pub unsafe fn tail(s: *const core::ffi::c_char) -> *const core::ffi::c_char {
    s
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn returned_c_string_path_proves_equivalent_rewrite() {
    let old = FnUnit::parse(RET_OLD, &[]).unwrap();
    let new = FnUnit::parse(RET_OK, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn returned_c_string_path_catches_a_difference() {
    let old = FnUnit::parse(RET_OLD, &[]).unwrap();
    let new = FnUnit::parse(RET_BAD, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a wrong rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// libxml2-style allocation through the `xmlMalloc` global: the heap path gives
// it a model calling Kani's `malloc`, with no extern declaration provided here
// (the model is injected). Allocate an int, store, return it.
const ALLOC_OLD: &str = r#"
pub unsafe fn mk(v: i32) -> *mut i32 {
    let p = xmlMalloc.expect("non-null function pointer")(core::mem::size_of::<i32>()) as *mut i32;
    if p.is_null() { return p; }
    *p = v;
    p
}
"#;

const ALLOC_OK: &str = r#"
pub unsafe fn mk(v: i32) -> *mut i32 {
    let p = xmlMalloc.expect("non-null function pointer")(core::mem::size_of::<i32>()) as *mut i32;
    if p.is_null() { return core::ptr::null_mut(); }
    *p = v;
    p
}
"#;

const ALLOC_BAD: &str = r#"
pub unsafe fn mk(v: i32) -> *mut i32 {
    let p = xmlMalloc.expect("non-null function pointer")(core::mem::size_of::<i32>()) as *mut i32;
    if p.is_null() { return p; }
    *p = v.wrapping_add(1);
    p
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn allocator_global_model_proves_equivalent_rewrite() {
    let old = FnUnit::parse(ALLOC_OLD, &[]).unwrap();
    let new = FnUnit::parse(ALLOC_OK, &[]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn allocator_global_model_catches_a_difference() {
    let old = FnUnit::parse(ALLOC_OLD, &[]).unwrap();
    let new = FnUnit::parse(ALLOC_BAD, &[]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a wrong rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// A scalar out-parameter (`*mut i32`): the heap path builds a single cell and
// compares its post-state, catching a divergent write.
const CELL_OLD: &str = r#"
pub unsafe fn dbl(p: *mut i32, k: i32) -> i32 {
    if p.is_null() { return -1; }
    *p = (*p).wrapping_mul(2);
    k
}
"#;

const CELL_OK: &str = r#"
pub unsafe fn dbl(p: *mut i32, k: i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    *p = v.wrapping_add(v);
    k
}
"#;

const CELL_BAD: &str = r#"
pub unsafe fn dbl(p: *mut i32, k: i32) -> i32 {
    if p.is_null() { return -1; }
    *p = (*p).wrapping_mul(2).wrapping_add(1);
    k
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn scalar_cell_path_proves_equivalent_rewrite() {
    let old = FnUnit::parse(CELL_OLD, &[]).unwrap();
    let new = FnUnit::parse(CELL_OK, &[]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn scalar_cell_path_catches_a_divergent_write() {
    let old = FnUnit::parse(CELL_OLD, &[]).unwrap();
    let new = FnUnit::parse(CELL_BAD, &[]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a wrong rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// A single-field union: unambiguous, so the heap path builds it like a struct.
const BOX1: &str = "#[derive(Copy, Clone)] #[repr(C)] pub union Box1 { pub v: i32 }";

const UGET_OLD: &str = r#"
pub unsafe fn uget(p: *mut Box1) -> i64 {
    if p.is_null() { return -1; }
    (*p).v as i64
}
"#;

const UGET_OK: &str = r#"
pub unsafe fn uget(p: *mut Box1) -> i64 {
    if p.is_null() { return -1; }
    let x = (*p).v;
    x as i64
}
"#;

const UGET_BAD: &str = r#"
pub unsafe fn uget(p: *mut Box1) -> i64 {
    if p.is_null() { return -1; }
    (*p).v as i64 + 1
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn single_field_union_path_proves_equivalent_rewrite() {
    let old = FnUnit::parse(UGET_OLD, &[BOX1]).unwrap();
    let new = FnUnit::parse(UGET_OK, &[BOX1]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn single_field_union_path_does_not_prove_a_wrong_rewrite() {
    let old = FnUnit::parse(UGET_OLD, &[BOX1]).unwrap();
    let new = FnUnit::parse(UGET_BAD, &[BOX1]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a wrong rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// A `strlen` extern declaration, as c2rust emits it.
const STRLEN_DECL: &str = "extern \"C\" { fn strlen(s: *const core::ffi::c_char) -> usize; }";

// The original calls libc `strlen`; the heap path must give it a Rust model so
// Kani resolves the call (it refuses `strlen` as a foreign symbol otherwise).
const SLEN_OLD: &str = r#"
pub unsafe fn slen(s: *const core::ffi::c_char) -> i64 {
    if s.is_null() { return -1; }
    strlen(s) as i64
}
"#;

// A rewrite that counts by hand. Proving it equals the `strlen`-based original
// shows the injected model matches a real length computation for every input.
const SLEN_OK: &str = r#"
pub unsafe fn slen(s: *const core::ffi::c_char) -> i64 {
    if s.is_null() { return -1; }
    let mut n = 0i64;
    let mut p = s;
    while *p != 0 { n += 1; p = p.add(1); }
    n
}
"#;

// A rewrite that is off by one, so it differs from `strlen`.
const SLEN_BAD: &str = r#"
pub unsafe fn slen(s: *const core::ffi::c_char) -> i64 {
    if s.is_null() { return -1; }
    let mut n = 1i64;
    let mut p = s;
    while *p != 0 { n += 1; p = p.add(1); }
    n
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn str_model_matches_a_hand_written_length_loop() {
    let old = FnUnit::parse(SLEN_OLD, &[STRLEN_DECL]).unwrap();
    let new = FnUnit::parse(SLEN_OK, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved (model == hand loop), got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn str_model_catches_a_wrong_length() {
    let old = FnUnit::parse(SLEN_OLD, &[STRLEN_DECL]).unwrap();
    let new = FnUnit::parse(SLEN_BAD, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a wrong rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// A read-only data global (a lookup table) read by both versions. Each version
// gets its own identical copy of the `static`, so reads agree -- the tool must
// prove equivalence, and must catch a rewrite that reads a different entry.
const TABLE: &str = "static mut TBL: [i64; 4] = [10i64, 20i64, 30i64, 40i64];";

const LOOKUP_OLD: &str = r#"
pub unsafe fn lookup(out: *mut i64, i: i32) {
    if out.is_null() { return; }
    let k = (i & 3) as usize;
    *out = TBL[k];
}
"#;

// Idiomatic rewrite: same mapping, different shape.
const LOOKUP_OK: &str = r#"
pub unsafe fn lookup(out: *mut i64, i: i32) {
    if out.is_null() { return; }
    let k = (i & 3) as usize;
    let v = TBL[k];
    *out = v;
}
"#;

// Wrong rewrite: reads the next entry (wraps), so results differ for some i.
const LOOKUP_BAD: &str = r#"
pub unsafe fn lookup(out: *mut i64, i: i32) {
    if out.is_null() { return; }
    let k = ((i + 1) & 3) as usize;
    *out = TBL[k];
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn read_only_global_proves_equivalent_rewrite() {
    let old = FnUnit::parse(LOOKUP_OLD, &[TABLE]).unwrap();
    let new = FnUnit::parse(LOOKUP_OK, &[TABLE]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn read_only_global_does_not_prove_a_wrong_rewrite() {
    let old = FnUnit::parse(LOOKUP_OLD, &[TABLE]).unwrap();
    let new = FnUnit::parse(LOOKUP_BAD, &[TABLE]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a wrong rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// A struct with a nullable function-pointer field (a callback), carried as
// opaque data. Both versions get the same symbolic pointer, so leaving it
// alone proves equivalent -- and a rewrite that clobbers the callback must be
// caught (the field is compared by identity in the post-state).
const CB_STRUCT: &str =
    "pub struct S { pub cb: Option<unsafe extern \"C\" fn(i32) -> i32>, pub n: i32 }";

const CB_OLD: &str = r#"
pub unsafe fn bump(s: *mut S) {
    if !s.is_null() { (*s).n += 1; }
}
"#;

const CB_OK: &str = r#"
pub unsafe fn bump(s: *mut S) {
    if !s.is_null() { (*s).n = (*s).n + 1; }
}
"#;

// A wrong rewrite: also clears the callback, changing observable heap state.
const CB_BAD: &str = r#"
pub unsafe fn bump(s: *mut S) {
    if !s.is_null() { (*s).n += 1; (*s).cb = None; }
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn fn_ptr_field_proves_equivalent_rewrite() {
    let old = FnUnit::parse(CB_OLD, &[CB_STRUCT]).unwrap();
    let new = FnUnit::parse(CB_OK, &[CB_STRUCT]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn fn_ptr_field_catches_a_clobbered_callback() {
    let old = FnUnit::parse(CB_OLD, &[CB_STRUCT]).unwrap();
    let new = FnUnit::parse(CB_BAD, &[CB_STRUCT]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a callback-clobbering rewrite was proved equivalent: {:?}",
        outcome.status
    );
}

// Subsystem B end-to-end: `check` proves an equivalent straight-line scalar
// rewrite algebraically (equality saturation), with no Kani run at all -- so
// this test needs no `cargo kani` and is not ignored.
#[test]
fn algebraic_backend_proves_without_kani() {
    let old = FnUnit::parse("pub fn g(x: i64, y: i64) -> i64 { x + y }", &[]).unwrap();
    let new = FnUnit::parse("pub fn g(x: i64, y: i64) -> i64 { y + x }", &[]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { bounded: false, unwind: 0 }),
        "expected an algebraic proof, got {:?}",
        outcome.status
    );
    // The algebraic pre-check short-circuits before any Kani invocation.
    assert_eq!(outcome.kani_ms, None);
}

// An indirect (function-pointer) call through a nullable callback field, as
// c2rust emits it (`field.expect("..")(args)`). The call is modelled as an
// observable/uninterpreted trace call keyed by the callback value, so both
// versions agree when they call the same callback with the same argument, and
// a changed argument is caught. The callback field type is a typedef'd bare fn
// (as c2rust emits), exercising alias resolution in the gate.
const IC_DEFS: &[&str] = &[
    "pub type cb_t = unsafe extern \"C\" fn(i64) -> i64;",
    "#[repr(C)] pub struct S { pub cb: Option<cb_t>, pub x: i64 }",
];

const IC_OLD: &str = r#"
pub unsafe fn run(s: *mut S) -> i64 {
    if s.is_null() { return 0; }
    (*s).cb.expect("non-null function pointer")((*s).x)
}
"#;

// Equivalent: the argument is bound to a local first, same value passed.
const IC_OK: &str = r#"
pub unsafe fn run(s: *mut S) -> i64 {
    if s.is_null() { return 0; }
    let v = (*s).x;
    (*s).cb.expect("non-null function pointer")(v)
}
"#;

// Wrong: the callback is passed a different argument, so for some heaps the
// (uninterpreted) callback returns a different value.
const IC_BAD: &str = r#"
pub unsafe fn run(s: *mut S) -> i64 {
    if s.is_null() { return 0; }
    (*s).cb.expect("non-null function pointer")((*s).x.wrapping_add(1))
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn indirect_call_proves_equivalent_rewrite() {
    let old = FnUnit::parse(IC_OLD, IC_DEFS).unwrap();
    let new = FnUnit::parse(IC_OK, IC_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn indirect_call_catches_different_argument() {
    let old = FnUnit::parse(IC_OLD, IC_DEFS).unwrap();
    let new = FnUnit::parse(IC_BAD, IC_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a different callback argument was proved equivalent: {:?}",
        outcome.status
    );
}

// A function-pointer *argument* (not a struct field): built as an opaque
// symbolic word and passed to both versions, then called via the modelled
// indirect call. Proves equivalent when both call it with the same argument;
// catches a changed argument. Exercises Shape::OpaqueArg + indirectmodel.
const FA_DEFS: &[&str] = &["pub type cb_t = unsafe extern \"C\" fn(i64) -> i64;"];

const FA_OLD: &str = r#"
pub unsafe fn apply(cb: Option<cb_t>, x: i64) -> i64 {
    cb.expect("non-null function pointer")(x)
}
"#;

const FA_OK: &str = r#"
pub unsafe fn apply(cb: Option<cb_t>, x: i64) -> i64 {
    let v = x;
    cb.expect("non-null function pointer")(v)
}
"#;

const FA_BAD: &str = r#"
pub unsafe fn apply(cb: Option<cb_t>, x: i64) -> i64 {
    cb.expect("non-null function pointer")(x.wrapping_add(1))
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn fn_ptr_arg_proves_equivalent_rewrite() {
    let old = FnUnit::parse(FA_OLD, FA_DEFS).unwrap();
    let new = FnUnit::parse(FA_OK, FA_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn fn_ptr_arg_catches_different_argument() {
    let old = FnUnit::parse(FA_OLD, FA_DEFS).unwrap();
    let new = FnUnit::parse(FA_BAD, FA_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a different argument to the callback was proved equivalent: {:?}",
        outcome.status
    );
}

// A `*mut c_void` opaque handle, carried in a struct field and returned. Built
// as a symbolic pointer-sized word, compared by identity. Proves equivalent
// when both versions carry it unchanged; catches a rewrite that returns a
// different value. (Wall 2 opaque-handle.)
const VP_DEFS: &[&str] =
    &["#[repr(C)] pub struct S { pub data: *mut ::core::ffi::c_void, pub n: i64 }"];

const VP_OLD: &str = r#"
pub unsafe fn get(s: *mut S) -> *mut ::core::ffi::c_void {
    if s.is_null() { return core::ptr::null_mut(); }
    (*s).data
}
"#;

const VP_OK: &str = r#"
pub unsafe fn get(s: *mut S) -> *mut ::core::ffi::c_void {
    if s.is_null() { return core::ptr::null_mut(); }
    let d = (*s).data;
    d
}
"#;

// Wrong: returns a handle derived from `n` instead of the carried one.
const VP_BAD: &str = r#"
pub unsafe fn get(s: *mut S) -> *mut ::core::ffi::c_void {
    if s.is_null() { return core::ptr::null_mut(); }
    (*s).n as *mut ::core::ffi::c_void
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn void_ptr_handle_proves_equivalent_rewrite() {
    let old = FnUnit::parse(VP_OLD, VP_DEFS).unwrap();
    let new = FnUnit::parse(VP_OK, VP_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn void_ptr_handle_catches_different_result() {
    let old = FnUnit::parse(VP_OLD, VP_DEFS).unwrap();
    let new = FnUnit::parse(VP_BAD, VP_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a different returned handle was proved equivalent: {:?}",
        outcome.status
    );
}
