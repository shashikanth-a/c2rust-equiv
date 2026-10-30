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

// A read-only struct-of-scalars data global, libxml2's `xmlChRangeGroup` shape:
// a `Group` of scalars plus a raw pointer to a `[Range; N]` table (a second
// static the group's initializer references by name -- so accepting the group
// requires pulling the table in too). Both versions get an identical const
// copy, so a divergent *use* of the table is caught while the data itself never
// differs. Exercises the struct-of-scalars `is_data_type` extension end to end.
const RANGE_DEF: &str = "#[repr(C)] #[derive(Copy, Clone)] pub struct Range { pub low: u32, pub high: u32 }";
const GROUP_DEF: &str = "#[repr(C)] #[derive(Copy, Clone)] pub struct Group { pub n: i32, pub ranges: *const Range }";
// `static mut` as c2rust emits these (a plain `static` with a raw-pointer field
// isn't `Sync`); the heap path treats a non-scalar `static mut` as a read-only
// data global regardless, since it emits no final-value comparison for it.
const TBL_DEF: &str =
    "static mut RANGES: [Range; 2] = [Range { low: 10, high: 20 }, Range { low: 30, high: 40 }];";
const GRP_DEF: &str =
    "static mut GRP: Group = Group { n: 2, ranges: &raw const RANGES as *const Range };";

// Classify the pointed-to value against the global range table.
const DATAG_OLD: &str = r#"
pub unsafe fn in_range(x: *const u32) -> i32 {
    if x.is_null() { return -1; }
    let v = *x;
    let n = (*(&raw const GRP)).n;
    let ranges = (*(&raw const GRP)).ranges;
    let mut i = 0i32;
    while i < n {
        let r = *ranges.offset(i as isize);
        if v >= r.low && v <= r.high { return 1; }
        i += 1;
    }
    0
}
"#;

const DATAG_OK: &str = r#"
pub unsafe fn in_range(x: *const u32) -> i32 {
    if x.is_null() { return -1; }
    let v = *x;
    let n = (*(&raw const GRP)).n;
    let ranges = (*(&raw const GRP)).ranges;
    let mut i = 0i32;
    while i < n {
        let r = *ranges.offset(i as isize);
        if r.low <= v && v <= r.high { return 1; }
        i += 1;
    }
    0
}
"#;

// Divergent use: a strict upper bound, so a value equal to `high` classifies
// differently -- same global data, different behaviour.
const DATAG_BAD: &str = r#"
pub unsafe fn in_range(x: *const u32) -> i32 {
    if x.is_null() { return -1; }
    let v = *x;
    let n = (*(&raw const GRP)).n;
    let ranges = (*(&raw const GRP)).ranges;
    let mut i = 0i32;
    while i < n {
        let r = *ranges.offset(i as isize);
        if v >= r.low && v < r.high { return 1; }
        i += 1;
    }
    0
}
"#;

#[test]
fn data_global_struct_of_scalars_is_in_heap_scope() {
    // No Kani: just that the struct-of-scalars read-only global (and the table
    // its initializer references) are accepted in heap scope rather than
    // rejected as an out-of-scope global.
    let items = [RANGE_DEF, GROUP_DEF, TBL_DEF, GRP_DEF];
    let unit = FnUnit::parse(DATAG_OLD, &items).unwrap();
    assert!(
        unit.heap_body_in_scope().is_ok(),
        "struct-of-scalars data global rejected: {:?}",
        unit.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn data_global_struct_of_scalars_proves_equivalent_rewrite() {
    let items = [RANGE_DEF, GROUP_DEF, TBL_DEF, GRP_DEF];
    let old = FnUnit::parse(DATAG_OLD, &items).unwrap();
    let new = FnUnit::parse(DATAG_OK, &items).unwrap();
    let outcome = check(&old, &new, &opts_unwind(4));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn data_global_struct_of_scalars_catches_divergence() {
    let items = [RANGE_DEF, GROUP_DEF, TBL_DEF, GRP_DEF];
    let old = FnUnit::parse(DATAG_OLD, &items).unwrap();
    let new = FnUnit::parse(DATAG_BAD, &items).unwrap();
    let outcome = check(&old, &new, &opts_unwind(4));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent use of the global table was proved equivalent: {:?}",
        outcome.status
    );
}

// Lock/unlock wrapper calls around real work: without the mutex model the call
// to `xmlMutexLock` (and its global argument) would put the function out of
// scope; with it, the calls are dropped as sequential no-ops and the actual
// work is proven. `GMUTEX` is a stand-in for the global mutex pointer.
const GMUTEX_DEF: &str = "static mut GMUTEX: *mut i32 = core::ptr::null_mut();";

const MUTEX_OLD: &str = r#"
pub unsafe fn locked_inc(p: *const i32) -> i32 {
    if p.is_null() { return 0; }
    xmlMutexLock(GMUTEX);
    let r = (*p).wrapping_add(1);
    xmlMutexUnlock(GMUTEX);
    r
}
"#;

const MUTEX_OK: &str = r#"
pub unsafe fn locked_inc(p: *const i32) -> i32 {
    if p.is_null() { return 0; }
    xmlRMutexLock(GMUTEX);
    let mut r = *p;
    r = r.wrapping_add(1);
    xmlRMutexUnlock(GMUTEX);
    r
}
"#;

// Same no-op locking, but a divergent result -- caught despite the dropped locks.
const MUTEX_BAD: &str = r#"
pub unsafe fn locked_inc(p: *const i32) -> i32 {
    if p.is_null() { return 0; }
    xmlMutexLock(GMUTEX);
    let r = (*p).wrapping_add(2);
    xmlMutexUnlock(GMUTEX);
    r
}
"#;

#[test]
fn mutex_wrapper_calls_are_in_heap_scope() {
    // No Kani: the lock/unlock calls and their global argument are admitted
    // rather than rejected as a foreign call / out-of-scope global.
    let unit = FnUnit::parse(MUTEX_OLD, &[GMUTEX_DEF]).unwrap();
    assert!(
        unit.heap_body_in_scope().is_ok(),
        "mutex wrapper call rejected: {:?}",
        unit.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn mutex_noop_proves_equivalent_rewrite() {
    let old = FnUnit::parse(MUTEX_OLD, &[GMUTEX_DEF]).unwrap();
    let new = FnUnit::parse(MUTEX_OK, &[GMUTEX_DEF]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn mutex_noop_catches_divergence() {
    let old = FnUnit::parse(MUTEX_OLD, &[GMUTEX_DEF]).unwrap();
    let new = FnUnit::parse(MUTEX_BAD, &[GMUTEX_DEF]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent result under no-op locks was proved equivalent: {:?}",
        outcome.status
    );
}

// A flexible array member typed through an alias (`data: [Ch; 0]`, `Ch = u8`),
// libxml2's `_xmlDictStrings.array: [xmlChar; 0]` shape. The element is resolved
// through aliases before the scalar check, so the struct builds (an empty array
// contributes nothing); without it the whole struct -- and every function that
// takes one -- was out of scope.
const FAM_ALIAS: &str = "pub type Ch = u8;";
const FAM_STRUCT: &str = "#[repr(C)] pub struct Strs { pub len: i32, pub data: [Ch; 0] }";

const FAM_OLD: &str = r#"
pub unsafe fn strs_len(s: *mut Strs) -> i32 {
    if s.is_null() { return -1; }
    (*s).len
}
"#;

const FAM_OK: &str = r#"
pub unsafe fn strs_len(s: *mut Strs) -> i32 {
    if s.is_null() { return -1; }
    let n = (*s).len;
    n
}
"#;

const FAM_BAD: &str = r#"
pub unsafe fn strs_len(s: *mut Strs) -> i32 {
    if s.is_null() { return -1; }
    (*s).len ^ 1
}
"#;

#[test]
fn flexible_array_member_is_in_heap_scope() {
    // No Kani: the struct with a `[Ch; 0]` flexible array member builds rather
    // than being rejected as an array of a non-scalar element.
    let unit = FnUnit::parse(FAM_OLD, &[FAM_ALIAS, FAM_STRUCT]).unwrap();
    assert!(
        c2rust_equiv::heap_diagnose(&unit).is_ok(),
        "flexible array member rejected: {:?}",
        c2rust_equiv::heap_diagnose(&unit)
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn flexible_array_member_proves_equivalent_rewrite() {
    let old = FnUnit::parse(FAM_OLD, &[FAM_ALIAS, FAM_STRUCT]).unwrap();
    let new = FnUnit::parse(FAM_OK, &[FAM_ALIAS, FAM_STRUCT]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn flexible_array_member_catches_divergence() {
    let old = FnUnit::parse(FAM_OLD, &[FAM_ALIAS, FAM_STRUCT]).unwrap();
    let new = FnUnit::parse(FAM_BAD, &[FAM_ALIAS, FAM_STRUCT]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent result was proved equivalent: {:?}",
        outcome.status
    );
}

// A pointer-to-pointer field (`T**`, c2rust's growable arrays, e.g.
// `xmlParserCtxt.inputTab`). It is carried as an opaque word (never
// dereferenced); the struct still builds, so a function reading its other
// fields is in scope. A divergent result is still caught.
const PP_STRUCT: &str = "#[repr(C)] pub struct Ctx { pub n: i32, pub tab: *mut *mut i32 }";

const PP_OLD: &str = r#"
pub unsafe fn ctx_n(c: *mut Ctx) -> i32 {
    if c.is_null() { return -1; }
    (*c).n
}
"#;

const PP_OK: &str = r#"
pub unsafe fn ctx_n(c: *mut Ctx) -> i32 {
    if c.is_null() { return -1; }
    let v = (*c).n;
    v
}
"#;

const PP_BAD: &str = r#"
pub unsafe fn ctx_n(c: *mut Ctx) -> i32 {
    if c.is_null() { return -1; }
    (*c).n ^ 1
}
"#;

#[test]
fn pointer_to_pointer_field_is_in_heap_scope() {
    let unit = FnUnit::parse(PP_OLD, &[PP_STRUCT]).unwrap();
    assert!(
        c2rust_equiv::heap_diagnose(&unit).is_ok(),
        "pointer-to-pointer field rejected: {:?}",
        c2rust_equiv::heap_diagnose(&unit)
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn pointer_to_pointer_field_proves_equivalent_rewrite() {
    let old = FnUnit::parse(PP_OLD, &[PP_STRUCT]).unwrap();
    let new = FnUnit::parse(PP_OK, &[PP_STRUCT]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn pointer_to_pointer_field_catches_divergence() {
    let old = FnUnit::parse(PP_OLD, &[PP_STRUCT]).unwrap();
    let new = FnUnit::parse(PP_BAD, &[PP_STRUCT]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent result was proved equivalent: {:?}",
        outcome.status
    );
}

// A multi-field struct held by value as a field (`inner: Inner`), libxml2's
// `xmlParserCtxt.lastError: xmlError` / `node_seq: xmlParserNodeInfoSeq` shape.
// The nested struct (scalars + a pointer) is built, cloned and compared inline
// via the value-returning `genval_`/`cloneval_`/`sameval_` companions.
const BV_INNER: &str = "#[repr(C)] pub struct Inner { pub a: i32, pub p: *mut i32 }";
const BV_OUTER: &str = "#[repr(C)] pub struct Outer { pub n: i32, pub inner: Inner }";

const BV_OLD: &str = r#"
pub unsafe fn outer_a(o: *mut Outer) -> i32 {
    if o.is_null() { return -1; }
    (*o).inner.a
}
"#;

const BV_OK: &str = r#"
pub unsafe fn outer_a(o: *mut Outer) -> i32 {
    if o.is_null() { return -1; }
    let i = &(*o).inner;
    (*i).a
}
"#;

const BV_BAD: &str = r#"
pub unsafe fn outer_a(o: *mut Outer) -> i32 {
    if o.is_null() { return -1; }
    (*o).inner.a ^ 1
}
"#;

#[test]
fn by_value_struct_field_is_in_heap_scope() {
    let unit = FnUnit::parse(BV_OLD, &[BV_INNER, BV_OUTER]).unwrap();
    assert!(
        c2rust_equiv::heap_diagnose(&unit).is_ok(),
        "by-value struct field rejected: {:?}",
        c2rust_equiv::heap_diagnose(&unit)
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn by_value_struct_field_proves_equivalent_rewrite() {
    let old = FnUnit::parse(BV_OLD, &[BV_INNER, BV_OUTER]).unwrap();
    let new = FnUnit::parse(BV_OK, &[BV_INNER, BV_OUTER]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn by_value_struct_field_catches_divergence() {
    let old = FnUnit::parse(BV_OLD, &[BV_INNER, BV_OUTER]).unwrap();
    let new = FnUnit::parse(BV_BAD, &[BV_INNER, BV_OUTER]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent result was proved equivalent: {:?}",
        outcome.status
    );
}

// A fixed-size array of a by-value struct element (`cells: [Cell; 3]`), lil's
// `_hashmap_t { cell: [hashcell_t; 256] }` shape. Each element is built,
// cloned, and compared element-wise via the `genval_`/`cloneval_`/`sameval_`
// companions -- the array generalisation of the by-value struct field.
const SA_CELL: &str = "#[repr(C)] #[derive(Copy, Clone)] pub struct Cell { pub a: i32, pub p: *mut i32 }";
const SA_OUTER: &str = "#[repr(C)] pub struct Grid { pub n: i32, pub cells: [Cell; 3] }";

const SA_OLD: &str = r#"
pub unsafe fn grid_a(g: *mut Grid) -> i32 {
    if g.is_null() { return -1; }
    (*g).cells[1].a
}
"#;

const SA_OK: &str = r#"
pub unsafe fn grid_a(g: *mut Grid) -> i32 {
    if g.is_null() { return -1; }
    let c = &(*g).cells[1];
    (*c).a
}
"#;

// Divergent: reads a different element, which differs since the elements are
// independent.
const SA_BAD: &str = r#"
pub unsafe fn grid_a(g: *mut Grid) -> i32 {
    if g.is_null() { return -1; }
    (*g).cells[2].a
}
"#;

#[test]
fn struct_array_field_is_in_heap_scope() {
    let unit = FnUnit::parse(SA_OLD, &[SA_CELL, SA_OUTER]).unwrap();
    assert!(
        c2rust_equiv::heap_diagnose(&unit).is_ok(),
        "struct-array field rejected: {:?}",
        c2rust_equiv::heap_diagnose(&unit)
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn struct_array_field_proves_equivalent_rewrite() {
    let old = FnUnit::parse(SA_OLD, &[SA_CELL, SA_OUTER]).unwrap();
    let new = FnUnit::parse(SA_OK, &[SA_CELL, SA_OUTER]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn struct_array_field_catches_divergence() {
    let old = FnUnit::parse(SA_OLD, &[SA_CELL, SA_OUTER]).unwrap();
    let new = FnUnit::parse(SA_BAD, &[SA_CELL, SA_OUTER]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent array element was proved equivalent: {:?}",
        outcome.status
    );
}

// A fixed-size array of opaque function pointers (`cbs: [Cb; 3]`), lil's
// `_lil_t { callback: [lil_callback_proc_t; 8] }` shape. Each element is a
// symbolic pointer-sized word, carried and compared by identity (never called).
const OA_DEFS: &[&str] = &[
    "pub type Cb = Option<unsafe extern \"C\" fn(i32) -> i32>;",
    "#[repr(C)] pub struct Holder { pub cbs: [Cb; 3], pub tag: i32 }",
];

const OA_OLD: &str = r#"
pub unsafe fn holder_tag(h: *mut Holder) -> i32 {
    if h.is_null() { return -1; }
    (*h).cbs[0] = None;
    (*h).tag
}
"#;

const OA_OK: &str = r#"
pub unsafe fn holder_tag(h: *mut Holder) -> i32 {
    if h.is_null() { return -1; }
    (*h).cbs[0] = None;
    let t = (*h).tag;
    t
}
"#;

// Divergent: nulls a different array element, so the compared post-state of the
// callback array differs whenever that element was non-null.
const OA_BAD: &str = r#"
pub unsafe fn holder_tag(h: *mut Holder) -> i32 {
    if h.is_null() { return -1; }
    (*h).cbs[1] = None;
    (*h).tag
}
"#;

#[test]
fn opaque_array_field_is_in_heap_scope() {
    let unit = FnUnit::parse(OA_OLD, OA_DEFS).unwrap();
    assert!(
        c2rust_equiv::heap_diagnose(&unit).is_ok(),
        "opaque-array field rejected: {:?}",
        c2rust_equiv::heap_diagnose(&unit)
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn opaque_array_field_proves_equivalent_rewrite() {
    let old = FnUnit::parse(OA_OLD, OA_DEFS).unwrap();
    let new = FnUnit::parse(OA_OK, OA_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn opaque_array_field_catches_divergence() {
    let old = FnUnit::parse(OA_OLD, OA_DEFS).unwrap();
    let new = FnUnit::parse(OA_BAD, OA_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent callback-array write was proved equivalent: {:?}",
        outcome.status
    );
}

// A by-value union of unknown discriminant (`v: U`), libxml2's
// `xmlSchemaVal.value` shape. Built as symbolic raw bytes, byte-identical
// across versions. A function reading a *scalar* variant consistently proves;
// a divergent read is caught; and -- crucially for soundness -- reading a
// pointer variant and dereferencing it is NOT falsely proved (it reads an
// arbitrary address). `tag` is an ordinary scalar; no discriminant is inferred.
const OU_UNION: &str = "#[repr(C)] #[derive(Copy, Clone)] pub union U { pub n: i32, pub p: *mut i32 }";
const OU_STRUCT: &str = "#[repr(C)] pub struct Val { pub tag: i32, pub v: U }";

// Reads the scalar variant `v.n` -- same bytes both sides, so equivalent.
const OU_OLD: &str = r#"
pub unsafe fn val_n(x: *mut Val) -> i32 {
    if x.is_null() { return -1; }
    (*x).v.n
}
"#;

const OU_OK: &str = r#"
pub unsafe fn val_n(x: *mut Val) -> i32 {
    if x.is_null() { return -1; }
    let u = (*x).v;
    u.n
}
"#;

// Divergent read of the same bytes -- caught despite no discriminant.
const OU_BAD: &str = r#"
pub unsafe fn val_n(x: *mut Val) -> i32 {
    if x.is_null() { return -1; }
    (*x).v.n ^ 1
}
"#;

// Dereferences the pointer variant of the symbolic-byte union: an arbitrary
// address, which must NOT prove equivalent (Kani flags the invalid access).
const OU_DEREF: &str = r#"
pub unsafe fn val_n(x: *mut Val) -> i32 {
    if x.is_null() { return -1; }
    *(*x).v.p
}
"#;

#[test]
fn opaque_union_is_in_heap_scope() {
    let unit = FnUnit::parse(OU_OLD, &[OU_UNION, OU_STRUCT]).unwrap();
    assert!(
        c2rust_equiv::heap_diagnose(&unit).is_ok(),
        "opaque union rejected: {:?}",
        c2rust_equiv::heap_diagnose(&unit)
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn opaque_union_scalar_variant_proves_equivalent() {
    let old = FnUnit::parse(OU_OLD, &[OU_UNION, OU_STRUCT]).unwrap();
    let new = FnUnit::parse(OU_OK, &[OU_UNION, OU_STRUCT]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(16));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn opaque_union_catches_divergence() {
    let old = FnUnit::parse(OU_OLD, &[OU_UNION, OU_STRUCT]).unwrap();
    let new = FnUnit::parse(OU_BAD, &[OU_UNION, OU_STRUCT]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent union read was proved equivalent: {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn opaque_union_pointer_variant_deref_is_not_falsely_proved() {
    // Both versions are identical but dereference a pointer read from the
    // symbolic-byte union -- an arbitrary address. This must NOT prove
    // (soundness: byte-wise unions never fabricate valid pointer provenance).
    let old = FnUnit::parse(OU_DEREF, &[OU_UNION, OU_STRUCT]).unwrap();
    let new = FnUnit::parse(OU_DEREF, &[OU_UNION, OU_STRUCT]).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "dereferencing an arbitrary union pointer was proved: {:?}",
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

// A C-enum newtype (`struct Kind(c_uint)`, as c2rust emits): built with a
// symbolic inner value, compared by it. As a struct field (NT_*) and as an
// argument (NA_*). (Wall: crate enum as scalar.)
const NT_DEFS: &[&str] = &[
    "#[derive(Copy, Clone)] #[repr(C)] pub struct Kind(pub ::core::ffi::c_uint);",
    "#[repr(C)] pub struct S { pub kind: Kind, pub n: i64 }",
];

const NT_OLD: &str = r#"
pub unsafe fn get(s: *mut S) -> i64 {
    if s.is_null() { return 0; }
    (*s).kind.0 as i64
}
"#;

const NT_OK: &str = r#"
pub unsafe fn get(s: *mut S) -> i64 {
    if s.is_null() { return 0; }
    let k = (*s).kind;
    k.0 as i64
}
"#;

const NT_BAD: &str = r#"
pub unsafe fn get(s: *mut S) -> i64 {
    if s.is_null() { return 0; }
    (*s).kind.0 as i64 + 1
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn newtype_enum_field_proves_equivalent_rewrite() {
    let old = FnUnit::parse(NT_OLD, NT_DEFS).unwrap();
    let new = FnUnit::parse(NT_OK, NT_DEFS).unwrap();
    assert!(
        matches!(check(&old, &new, &opts()).status, Status::Proved { .. }),
        "expected Proved"
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn newtype_enum_field_catches_divergence() {
    let old = FnUnit::parse(NT_OLD, NT_DEFS).unwrap();
    let new = FnUnit::parse(NT_BAD, NT_DEFS).unwrap();
    assert!(
        !matches!(check(&old, &new, &opts()).status, Status::Proved { .. }),
        "a +1 rewrite was proved equivalent"
    );
}

// A C-enum newtype as a by-value argument and return.
const NA_DEFS: &[&str] =
    &["#[derive(Copy, Clone)] #[repr(C)] pub struct Kind(pub ::core::ffi::c_uint);"];
const NA_OLD: &str = "pub unsafe fn id(k: Kind) -> Kind { k }";
const NA_OK: &str = "pub unsafe fn id(k: Kind) -> Kind { let v = k; v }";

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn newtype_enum_arg_proves_equivalent_rewrite() {
    let old = FnUnit::parse(NA_OLD, NA_DEFS).unwrap();
    let new = FnUnit::parse(NA_OK, NA_DEFS).unwrap();
    assert!(
        matches!(check(&old, &new, &opts()).status, Status::Proved { .. }),
        "expected Proved"
    );
}

// A call through libxml2's global allocator hooks (`xmlMalloc.expect("..")(n)`,
// `xmlFree.expect("..")(p)`). allocmodel gives each hook a concrete definition
// routing to Kani's modelled malloc/free, so the call works natively; the
// eligibility gate now admits it instead of rejecting it as an indirect call.
const AL_DEFS: &[&str] = &[
    "pub type size_t = usize;",
    "pub type xmlMallocFunc = Option<unsafe extern \"C\" fn(size_t) -> *mut ::core::ffi::c_void>;",
    "pub type xmlFreeFunc = Option<unsafe extern \"C\" fn(*mut ::core::ffi::c_void) -> ()>;",
    "extern \"C\" { static mut xmlMalloc: xmlMallocFunc; static mut xmlFree: xmlFreeFunc; }",
];

const AL_OLD: &str = r#"
pub unsafe fn f(_d: *mut ::core::ffi::c_void, n: ::core::ffi::c_int) -> ::core::ffi::c_int {
    let p = xmlMalloc.expect("non-null function pointer")(8 as size_t);
    if p.is_null() { return 0; }
    xmlFree.expect("non-null function pointer")(p);
    n
}
"#;

const AL_OK: &str = r#"
pub unsafe fn f(_d: *mut ::core::ffi::c_void, n: ::core::ffi::c_int) -> ::core::ffi::c_int {
    let sz: size_t = 8 as size_t;
    let p = xmlMalloc.expect("non-null function pointer")(sz);
    if p.is_null() { return 0; }
    xmlFree.expect("non-null function pointer")(p);
    let v = n;
    v
}
"#;

const AL_BAD: &str = r#"
pub unsafe fn f(_d: *mut ::core::ffi::c_void, n: ::core::ffi::c_int) -> ::core::ffi::c_int {
    let p = xmlMalloc.expect("non-null function pointer")(8 as size_t);
    if p.is_null() { return 0; }
    xmlFree.expect("non-null function pointer")(p);
    n + 1
}
"#;

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn alloc_hook_proves_equivalent_rewrite() {
    let old = FnUnit::parse(AL_OLD, AL_DEFS).unwrap();
    let new = FnUnit::parse(AL_OK, AL_DEFS).unwrap();
    assert!(
        matches!(check(&old, &new, &opts()).status, Status::Proved { .. }),
        "expected Proved"
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn alloc_hook_catches_divergence() {
    let old = FnUnit::parse(AL_OLD, AL_DEFS).unwrap();
    let new = FnUnit::parse(AL_BAD, AL_DEFS).unwrap();
    assert!(
        !matches!(check(&old, &new, &opts()).status, Status::Proved { .. }),
        "a +1 rewrite was proved equivalent"
    );
}


// ---------------------------------------------------------------------------
// A written struct `static mut` global modelled as observable output. libxml2's
// error path writes `static mut xmlLastError: xmlError { code, line, message*,
// .. }`; such a global is pulled into the unit (both versions keep their own
// copy, started from the shared initializer) and the harness compares the final
// state field-by-field with `sameval_`. Writing it is therefore in scope, and a
// divergent write to the error state is caught. `ERRST` stands in for xmlError:
// scalar fields plus a message pointer (left null here, so comparable).
const ERRST_DEF: &str =
    "pub struct ErrSt { pub code: i32, pub line: i32, pub msg: *mut i8 }";
const LASTERR_DEF: &str =
    "pub static mut LASTERR: ErrSt = ErrSt { code: 0, line: 0, msg: core::ptr::null_mut() };";

// Record an error: write the scalar fields of the global error state. Takes a
// pointer so the function is on the heap path.
const ERRG_OLD: &str = r#"
pub unsafe fn record(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    (*(&raw mut LASTERR)).code = v;
    (*(&raw mut LASTERR)).line = v.wrapping_add(1);
    v
}
"#;

// Equivalent rewrite: same final error state, written in a different order.
const ERRG_OK: &str = r#"
pub unsafe fn record(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    (*(&raw mut LASTERR)).line = v.wrapping_add(1);
    (*(&raw mut LASTERR)).code = v;
    v
}
"#;

// Divergent rewrite: records a different error code (v+1), so the observable
// error state differs even though the return value is identical.
const ERRG_BAD: &str = r#"
pub unsafe fn record(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    (*(&raw mut LASTERR)).code = v.wrapping_add(1);
    (*(&raw mut LASTERR)).line = v.wrapping_add(1);
    v
}
"#;

#[test]
fn written_struct_global_is_in_heap_scope() {
    // No Kani: a function that writes the struct `static mut` global is in heap
    // scope (the write-guard does not reject it; it is compared instead).
    let items = [ERRST_DEF, LASTERR_DEF];
    let unit = FnUnit::parse(ERRG_OLD, &items).unwrap();
    assert!(
        unit.heap_body_in_scope().is_ok(),
        "writing a modelled struct global rejected: {:?}",
        unit.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn written_struct_global_proves_equivalent_rewrite() {
    let items = [ERRST_DEF, LASTERR_DEF];
    let old = FnUnit::parse(ERRG_OLD, &items).unwrap();
    let new = FnUnit::parse(ERRG_OK, &items).unwrap();
    let outcome = check(&old, &new, &opts_unwind(4));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn written_struct_global_catches_divergent_error_state() {
    let items = [ERRST_DEF, LASTERR_DEF];
    let old = FnUnit::parse(ERRG_OLD, &items).unwrap();
    let new = FnUnit::parse(ERRG_BAD, &items).unwrap();
    let outcome = check(&old, &new, &opts_unwind(4));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent write to the global error state was proved equivalent: {:?}",
        outcome.status
    );
}

// ---------------------------------------------------------------------------
// __xmlRaiseError modelled as an observable trace call. libxml2's central error
// primitive is variadic; each call site is rewritten into trace events, so both
// versions are equivalent exactly when they report the same errors. The leading
// handler/context pointers are compared by correspondence, the `level` newtype
// by its inner scalar, the rest (and the format args) by content/value. Sound
// as stateless because nothing in scope reads the error state it writes (the
// `__xmlLastError()` accessor stays out of scope).
const RAISE_DEFS: &[&str] = &[
    "pub struct xmlErrorLevel(pub u32);",
    "pub type xmlStructuredErrorFunc = Option<unsafe extern \"C\" fn()>;",
    "pub type xmlGenericErrorFunc = Option<unsafe extern \"C\" fn()>;",
    "extern \"C\" { pub fn __xmlRaiseError(\
        schannel: xmlStructuredErrorFunc, channel: xmlGenericErrorFunc, \
        data: *mut core::ffi::c_void, ctx: *mut core::ffi::c_void, \
        node: *mut core::ffi::c_void, domain: core::ffi::c_int, \
        code: core::ffi::c_int, level: xmlErrorLevel, \
        file: *const core::ffi::c_char, line: core::ffi::c_int, \
        str1: *const core::ffi::c_char, str2: *const core::ffi::c_char, \
        str3: *const core::ffi::c_char, int1: core::ffi::c_int, \
        col: core::ffi::c_int, msg: *const core::ffi::c_char, ...); }",
];

const RAISE_OLD: &str = r#"
pub unsafe fn report(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    __xmlRaiseError(None, None, core::ptr::null_mut(), core::ptr::null_mut(),
        core::ptr::null_mut(), 1 as core::ffi::c_int, 100 as core::ffi::c_int,
        xmlErrorLevel(2), core::ptr::null::<core::ffi::c_char>(), 0 as core::ffi::c_int,
        core::ptr::null::<core::ffi::c_char>(), core::ptr::null::<core::ffi::c_char>(), core::ptr::null::<core::ffi::c_char>(),
        0 as core::ffi::c_int, 0 as core::ffi::c_int,
        b"e\0".as_ptr() as *const core::ffi::c_char);
    v
}
"#;

// Equivalent rewrite: a harmless extra binding; same error reported, same return.
const RAISE_OK: &str = r#"
pub unsafe fn report(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    let _scratch = v.wrapping_mul(2);
    __xmlRaiseError(None, None, core::ptr::null_mut(), core::ptr::null_mut(),
        core::ptr::null_mut(), 1 as core::ffi::c_int, 100 as core::ffi::c_int,
        xmlErrorLevel(2), core::ptr::null::<core::ffi::c_char>(), 0 as core::ffi::c_int,
        core::ptr::null::<core::ffi::c_char>(), core::ptr::null::<core::ffi::c_char>(), core::ptr::null::<core::ffi::c_char>(),
        0 as core::ffi::c_int, 0 as core::ffi::c_int,
        b"e\0".as_ptr() as *const core::ffi::c_char);
    v
}
"#;

// Divergent rewrite: reports a different error code (101 vs 100) -- an
// observably different error, which the trace must catch.
const RAISE_BAD: &str = r#"
pub unsafe fn report(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    __xmlRaiseError(None, None, core::ptr::null_mut(), core::ptr::null_mut(),
        core::ptr::null_mut(), 1 as core::ffi::c_int, 101 as core::ffi::c_int,
        xmlErrorLevel(2), core::ptr::null::<core::ffi::c_char>(), 0 as core::ffi::c_int,
        core::ptr::null::<core::ffi::c_char>(), core::ptr::null::<core::ffi::c_char>(), core::ptr::null::<core::ffi::c_char>(),
        0 as core::ffi::c_int, 0 as core::ffi::c_int,
        b"e\0".as_ptr() as *const core::ffi::c_char);
    v
}
"#;

#[test]
fn raise_error_is_in_heap_scope() {
    let old = FnUnit::parse(RAISE_OLD, RAISE_DEFS).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "a __xmlRaiseError call rejected: {:?}",
        old.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn raise_error_proves_equivalent_rewrite() {
    let old = FnUnit::parse(RAISE_OLD, RAISE_DEFS).unwrap();
    let new = FnUnit::parse(RAISE_OK, RAISE_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn raise_error_catches_divergent_error_report() {
    let old = FnUnit::parse(RAISE_OLD, RAISE_DEFS).unwrap();
    let new = FnUnit::parse(RAISE_BAD, RAISE_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent error report was proved equivalent: {:?}",
        outcome.status
    );
}

// ---------------------------------------------------------------------------
// A ctx+format diagnostic printer `(ctx: *mut c_void, msg, ...)` -- the shape
// of xmlParserError / xmlParserWarning / xmlGenericErrorDefaultFunc. Modelled
// by the same errormodel spec (a one-pointer prefix, no level): the context
// pointer by correspondence, the message by content.
const PERR_DEFS: &[&str] = &[
    "extern \"C\" { pub fn xmlParserError(ctx: *mut core::ffi::c_void, \
        msg: *const core::ffi::c_char, ...); }",
];

const PERR_OLD: &str = r#"
pub unsafe fn warn(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    xmlParserError(core::ptr::null_mut(), b"a\0".as_ptr() as *const core::ffi::c_char);
    v
}
"#;

const PERR_OK: &str = r#"
pub unsafe fn warn(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    let _s = v;
    xmlParserError(core::ptr::null_mut(), b"a\0".as_ptr() as *const core::ffi::c_char);
    v
}
"#;

// Divergent: reports a different message, which the trace must catch.
const PERR_BAD: &str = r#"
pub unsafe fn warn(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    xmlParserError(core::ptr::null_mut(), b"b\0".as_ptr() as *const core::ffi::c_char);
    v
}
"#;

#[test]
fn ctx_printer_is_in_heap_scope() {
    let old = FnUnit::parse(PERR_OLD, PERR_DEFS).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "an xmlParserError call rejected: {:?}",
        old.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn ctx_printer_proves_equivalent_rewrite() {
    let old = FnUnit::parse(PERR_OLD, PERR_DEFS).unwrap();
    let new = FnUnit::parse(PERR_OK, PERR_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn ctx_printer_catches_divergent_message() {
    let old = FnUnit::parse(PERR_OLD, PERR_DEFS).unwrap();
    let new = FnUnit::parse(PERR_BAD, PERR_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent diagnostic message was proved equivalent: {:?}",
        outcome.status
    );
}

// ---------------------------------------------------------------------------
// A bare variadic error printer with no pointer prefix (`fmt, ...`), json-c's
// `_json_c_set_last_err`. Modelled as an observable trace over its format and
// arguments (errormodel spec with ptr_end 0); a different reported message is a
// divergence and is caught.
const JSONERR_DEFS: &[&str] = &[
    "extern \"C\" { pub fn _json_c_set_last_err(fmt: *const core::ffi::c_char, ...); }",
];

const JSONERR_OLD: &str = r#"
pub unsafe fn fail(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    _json_c_set_last_err(b"bad %d\0".as_ptr() as *const core::ffi::c_char, v);
    v
}
"#;

const JSONERR_OK: &str = r#"
pub unsafe fn fail(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    let _w = v;
    _json_c_set_last_err(b"bad %d\0".as_ptr() as *const core::ffi::c_char, v);
    v
}
"#;

const JSONERR_BAD: &str = r#"
pub unsafe fn fail(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    _json_c_set_last_err(b"bad %d\0".as_ptr() as *const core::ffi::c_char, v.wrapping_add(1));
    v
}
"#;

#[test]
fn json_set_last_err_is_in_heap_scope() {
    let old = FnUnit::parse(JSONERR_OLD, JSONERR_DEFS).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "a _json_c_set_last_err call rejected: {:?}",
        old.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn json_set_last_err_proves_equivalent_rewrite() {
    let old = FnUnit::parse(JSONERR_OLD, JSONERR_DEFS).unwrap();
    let new = FnUnit::parse(JSONERR_OK, JSONERR_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn json_set_last_err_catches_divergent_message() {
    let old = FnUnit::parse(JSONERR_OLD, JSONERR_DEFS).unwrap();
    let new = FnUnit::parse(JSONERR_BAD, JSONERR_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent error message was proved equivalent: {:?}",
        outcome.status
    );
}

// ---------------------------------------------------------------------------
// The string-duplication allocator hook `xmlMemStrdup.expect("..")(s)`, modelled
// by a native allocate-and-copy shim (allocmodel). Both versions duplicate the
// same NUL-terminated input into a fresh buffer with identical content, so they
// prove equivalent; duplicating a different input is a divergent result that is
// caught by the returned-string comparison.
const STRDUP_OLD: &str = r#"
pub unsafe fn dup(s: *const core::ffi::c_char) -> *mut core::ffi::c_char {
    if s.is_null() { return core::ptr::null_mut(); }
    xmlMemStrdup.expect("non-null function pointer")(s)
}
"#;

const STRDUP_OK: &str = r#"
pub unsafe fn dup(s: *const core::ffi::c_char) -> *mut core::ffi::c_char {
    if s.is_null() { return core::ptr::null_mut(); }
    let _k = s;
    xmlMemStrdup.expect("non-null function pointer")(s)
}
"#;

// Divergent: duplicates the second argument instead of the first, so the
// returned string differs whenever the two inputs differ.
const STRDUP2_OLD: &str = r#"
pub unsafe fn dup2(s: *const core::ffi::c_char, t: *const core::ffi::c_char) -> *mut core::ffi::c_char {
    if s.is_null() || t.is_null() { return core::ptr::null_mut(); }
    xmlMemStrdup.expect("non-null function pointer")(s)
}
"#;

const STRDUP2_BAD: &str = r#"
pub unsafe fn dup2(s: *const core::ffi::c_char, t: *const core::ffi::c_char) -> *mut core::ffi::c_char {
    if s.is_null() || t.is_null() { return core::ptr::null_mut(); }
    xmlMemStrdup.expect("non-null function pointer")(t)
}
"#;

#[test]
fn strdup_hook_is_in_heap_scope() {
    let old = FnUnit::parse(STRDUP_OLD, &[]).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "a strdup hook call was rejected: {:?}",
        old.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn strdup_hook_proves_equivalent_rewrite() {
    let old = FnUnit::parse(STRDUP_OLD, &[]).unwrap();
    let new = FnUnit::parse(STRDUP_OK, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn strdup_hook_catches_divergent_result() {
    let old = FnUnit::parse(STRDUP2_OLD, &[]).unwrap();
    let new = FnUnit::parse(STRDUP2_BAD, &[]).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent strdup result was proved equivalent: {:?}",
        outcome.status
    );
}

// ---------------------------------------------------------------------------
// A c2rust registered-handler dispatch through a thread-local accessor:
// `(*__xmlGenericError()).expect("..")(ctx, fmt, args)`. The accessor returns a
// function-pointer global we never build; the dispatch is modelled as an
// observable trace call keyed by the handler name (errormodel), and the
// accessor + its fn-ptr global drop out of the unit entirely. The context
// pointer is compared by correspondence, the format tail by content, so a
// different reported value is a divergent error report and is caught.
const HDISP_DEFS: &[&str] = &[];

const HDISP_OLD: &str = r#"
pub unsafe fn report(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let x = *p;
    (*__xmlGenericError()).expect("non-null function pointer")(
        core::ptr::null_mut(),
        b"%d\0".as_ptr() as *const core::ffi::c_char,
        x,
    );
    x
}
"#;

// Equivalent: an inert local binding, same reported value and return.
const HDISP_OK: &str = r#"
pub unsafe fn report(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let x = *p;
    let _t = x;
    (*__xmlGenericError()).expect("non-null function pointer")(
        core::ptr::null_mut(),
        b"%d\0".as_ptr() as *const core::ffi::c_char,
        x,
    );
    x
}
"#;

// Divergent: reports `x + 1` through the handler though it still returns `x`,
// so only the observable trace distinguishes the two.
const HDISP_BAD: &str = r#"
pub unsafe fn report(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let x = *p;
    (*__xmlGenericError()).expect("non-null function pointer")(
        core::ptr::null_mut(),
        b"%d\0".as_ptr() as *const core::ffi::c_char,
        x + 1,
    );
    x
}
"#;

#[test]
fn handler_dispatch_is_in_heap_scope() {
    let old = FnUnit::parse(HDISP_OLD, HDISP_DEFS).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "a handler dispatch was rejected: {:?}",
        old.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn handler_dispatch_proves_equivalent_rewrite() {
    let old = FnUnit::parse(HDISP_OLD, HDISP_DEFS).unwrap();
    let new = FnUnit::parse(HDISP_OK, HDISP_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn handler_dispatch_catches_divergent_report() {
    let old = FnUnit::parse(HDISP_OLD, HDISP_DEFS).unwrap();
    let new = FnUnit::parse(HDISP_BAD, HDISP_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent handler report was proved equivalent: {:?}",
        outcome.status
    );
}

// The guarded register-node hook c2rust emits in every node constructor:
// `if __xmlRegisterCallbacks != 0 && (*__X()).is_some() { (*__X()).expect(..)(node); }`.
// The accessor is erased and the `.is_some()` guard folds to `true`, while the
// default-zero `__xmlRegisterCallbacks` keeps the branch dead -- so both
// versions skip the callback identically and the node constructor proves. The
// node-pointer argument (not a `*mut c_void`) must still compile in the dead
// branch, exercising the handle-pointer cast.
const REGHOOK_DEFS: &[&str] = &["static mut __xmlRegisterCallbacks: i32 = 0;"];

const REGHOOK_OLD: &str = r#"
pub unsafe fn mk(p: *mut core::ffi::c_void) -> i32 {
    if p.is_null() { return -1; }
    let node = p;
    if __xmlRegisterCallbacks != 0 && (*__xmlRegisterNodeDefaultValue()).is_some() {
        (*__xmlRegisterNodeDefaultValue()).expect("non-null function pointer")(node);
    }
    0
}
"#;

const REGHOOK_OK: &str = r#"
pub unsafe fn mk(p: *mut core::ffi::c_void) -> i32 {
    if p.is_null() { return -1; }
    let node = p;
    let _n = node;
    if __xmlRegisterCallbacks != 0 && (*__xmlRegisterNodeDefaultValue()).is_some() {
        (*__xmlRegisterNodeDefaultValue()).expect("non-null function pointer")(node);
    }
    0
}
"#;

#[test]
fn register_hook_is_in_heap_scope() {
    let old = FnUnit::parse(REGHOOK_OLD, REGHOOK_DEFS).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "a register-node hook was rejected: {:?}",
        old.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn register_hook_proves_equivalent_rewrite() {
    let old = FnUnit::parse(REGHOOK_OLD, REGHOOK_DEFS).unwrap();
    let new = FnUnit::parse(REGHOOK_OK, REGHOOK_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(8));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

// ---------------------------------------------------------------------------
// A c2rust thread-local global accessor `__X() -> *mut T` modelled as its
// main-thread branch `&raw mut X`. A function reads/writes the global through
// the accessor; after the rewrite the accessor's per-thread indirection is
// gone and `X` is an ordinary modelled global, compared by final state.
const ACC_DEFS: &[&str] = &[
    "static mut CFG: i32 = 0;",
    "pub unsafe extern \"C\" fn xmlIsMainThread() -> i32 { 1 }",
    "pub unsafe extern \"C\" fn __CFG() -> *mut i32 { \
        if xmlIsMainThread() != 0 { return &raw mut CFG; } else { return &raw mut CFG; } }",
];

const ACC_OLD: &str = r#"
pub unsafe fn setcfg(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let g = __CFG();
    *g = *p;
    *g
}
"#;

// Equivalent rewrite: same final global state, via a harmless temporary.
const ACC_OK: &str = r#"
pub unsafe fn setcfg(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let v = *p;
    let g = __CFG();
    *g = v;
    *g
}
"#;

// Divergent rewrite: writes a different value to the global.
const ACC_BAD: &str = r#"
pub unsafe fn setcfg(p: *const i32) -> i32 {
    if p.is_null() { return -1; }
    let g = __CFG();
    *g = (*p).wrapping_add(1);
    *g
}
"#;

#[test]
fn accessor_global_is_in_heap_scope() {
    let old = FnUnit::parse(ACC_OLD, ACC_DEFS).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "a thread-local accessor use rejected: {:?}",
        old.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn accessor_global_proves_equivalent_rewrite() {
    let old = FnUnit::parse(ACC_OLD, ACC_DEFS).unwrap();
    let new = FnUnit::parse(ACC_OK, ACC_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(4));
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn accessor_global_catches_divergent_write() {
    let old = FnUnit::parse(ACC_OLD, ACC_DEFS).unwrap();
    let new = FnUnit::parse(ACC_BAD, ACC_DEFS).unwrap();
    let outcome = check(&old, &new, &opts_unwind(4));
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a divergent global write was proved equivalent: {:?}",
        outcome.status
    );
}

// A many-argument indirect call (>3 args), as wide SAX callbacks are
// (startElementNs takes eight). Each argument is its own trace event, so arity
// is unbounded: both versions agree when they call the same callback with the
// same arguments, and any changed argument is caught.
const IC5_DEFS: &[&str] = &[
    "pub type cb5_t = unsafe extern \"C\" fn(i64, i64, i64, i64, i64) -> i64;",
    "#[repr(C)] pub struct S5 { pub cb: Option<cb5_t>, pub x: i64 }",
];

const IC5_OLD: &str = r#"
pub unsafe fn run5(s: *mut S5) -> i64 {
    if s.is_null() { return 0; }
    (*s).cb.expect("non-null")((*s).x, 1, 2, 3, 4)
}
"#;

const IC5_OK: &str = r#"
pub unsafe fn run5(s: *mut S5) -> i64 {
    if s.is_null() { return 0; }
    let v = (*s).x;
    (*s).cb.expect("non-null")(v, 1, 2, 3, 4)
}
"#;

const IC5_BAD: &str = r#"
pub unsafe fn run5(s: *mut S5) -> i64 {
    if s.is_null() { return 0; }
    (*s).cb.expect("non-null")((*s).x, 1, 2, 3, 5)
}
"#;

#[test]
fn many_arg_indirect_call_is_in_heap_scope() {
    let old = FnUnit::parse(IC5_OLD, IC5_DEFS).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "a 5-argument indirect call rejected: {:?}",
        old.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn many_arg_indirect_call_proves_equivalent_rewrite() {
    let old = FnUnit::parse(IC5_OLD, IC5_DEFS).unwrap();
    let new = FnUnit::parse(IC5_OK, IC5_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn many_arg_indirect_call_catches_different_argument() {
    let old = FnUnit::parse(IC5_OLD, IC5_DEFS).unwrap();
    let new = FnUnit::parse(IC5_BAD, IC5_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a changed callback argument was proved equivalent: {:?}",
        outcome.status
    );
}

// An indirect call reached through ALIASED pointer types and a nested struct,
// as c2rust emits SAX dispatch: `(*(*ctxt).sax).cb.expect(..)(args)` where ctxt
// is a `CtxPtr` typedef and sax an `InnerPtr` typedef. Exercises alias
// resolution in the indirect-call type walk.
const ACHAIN_DEFS: &[&str] = &[
    "pub type CtxPtr = *mut Ctx;",
    "pub type InnerPtr = *mut Inner;",
    "pub type cb_t = unsafe extern \"C\" fn(i64) -> i64;",
    "#[repr(C)] pub struct Inner { pub cb: Option<cb_t>, pub pad: i64 }",
    "#[repr(C)] pub struct Ctx { pub inner: InnerPtr, pub x: i64 }",
];

const ACHAIN_OLD: &str = r#"
pub unsafe fn run(c: CtxPtr) -> i64 {
    if c.is_null() || (*c).inner.is_null() { return 0; }
    (*(*c).inner).cb.expect("non-null function pointer")((*c).x)
}
"#;

const ACHAIN_OK: &str = r#"
pub unsafe fn run(c: CtxPtr) -> i64 {
    if c.is_null() || (*c).inner.is_null() { return 0; }
    let v = (*c).x;
    (*(*c).inner).cb.expect("non-null function pointer")(v)
}
"#;

const ACHAIN_BAD: &str = r#"
pub unsafe fn run(c: CtxPtr) -> i64 {
    if c.is_null() || (*c).inner.is_null() { return 0; }
    (*(*c).inner).cb.expect("non-null function pointer")((*c).x.wrapping_add(1))
}
"#;

#[test]
fn aliased_chain_indirect_call_is_in_heap_scope() {
    let old = FnUnit::parse(ACHAIN_OLD, ACHAIN_DEFS).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "an aliased-chain indirect call rejected: {:?}",
        old.heap_body_in_scope()
    );
}

// A callback dispatched through a NESTED-`let`-bound function pointer with
// ALIAS-typed pointer arguments and an alias-typed pointer return -- lil's
// command-callback shape: `if guard { let proc: CbT = ..; proc.expect(..)(ctx,
// n, v) }`, where `Ctx`/`Val` are pointer typedefs and `CbT` the callback
// typedef. Exercises both nested-local typing (the receiver `proc` is bound
// inside the guard) and argument/return alias resolution.
const NLCB_DEFS: &[&str] = &[
    "pub type Ctx = *mut core::ffi::c_void;",
    "pub type Val = *mut core::ffi::c_void;",
    "pub type CbT = Option<unsafe extern \"C\" fn(Ctx, usize, Val) -> Val>;",
    "#[repr(C)] pub struct Cmd { pub cb: CbT, pub pad: i64 }",
];

const NLCB_OLD: &str = r#"
pub unsafe fn run(c: *mut Cmd, ctx: Ctx, n: usize, v: Val) -> Val {
    if c.is_null() { return core::ptr::null_mut(); }
    if (*c).cb.is_some() {
        let mut proc: CbT = (*c).cb;
        return proc.expect("non-null function pointer")(ctx, n, v);
    }
    core::ptr::null_mut()
}
"#;

const NLCB_OK: &str = r#"
pub unsafe fn run(c: *mut Cmd, ctx: Ctx, n: usize, v: Val) -> Val {
    if c.is_null() { return core::ptr::null_mut(); }
    if (*c).cb.is_some() {
        let mut proc: CbT = (*c).cb;
        let m = n;
        return proc.expect("non-null function pointer")(ctx, m, v);
    }
    core::ptr::null_mut()
}
"#;

// Divergent: passes a different count argument to the callback.
const NLCB_BAD: &str = r#"
pub unsafe fn run(c: *mut Cmd, ctx: Ctx, n: usize, v: Val) -> Val {
    if c.is_null() { return core::ptr::null_mut(); }
    if (*c).cb.is_some() {
        let mut proc: CbT = (*c).cb;
        return proc.expect("non-null function pointer")(ctx, n.wrapping_add(1), v);
    }
    core::ptr::null_mut()
}
"#;

#[test]
fn nested_local_callback_is_in_heap_scope() {
    let old = FnUnit::parse(NLCB_OLD, NLCB_DEFS).unwrap();
    assert!(
        old.heap_body_in_scope().is_ok(),
        "a nested-local aliased callback was rejected: {:?}",
        old.heap_body_in_scope()
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn nested_local_callback_proves_equivalent_rewrite() {
    let old = FnUnit::parse(NLCB_OLD, NLCB_DEFS).unwrap();
    let new = FnUnit::parse(NLCB_OK, NLCB_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn nested_local_callback_catches_different_argument() {
    let old = FnUnit::parse(NLCB_OLD, NLCB_DEFS).unwrap();
    let new = FnUnit::parse(NLCB_BAD, NLCB_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a changed callback argument was proved equivalent: {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn aliased_chain_indirect_call_proves_equivalent_rewrite() {
    let old = FnUnit::parse(ACHAIN_OLD, ACHAIN_DEFS).unwrap();
    let new = FnUnit::parse(ACHAIN_OK, ACHAIN_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        matches!(outcome.status, Status::Proved { .. }),
        "expected Proved, got {:?}",
        outcome.status
    );
}

#[test]
#[ignore = "requires `cargo kani` on PATH; slow"]
fn aliased_chain_indirect_call_catches_different_argument() {
    let old = FnUnit::parse(ACHAIN_OLD, ACHAIN_DEFS).unwrap();
    let new = FnUnit::parse(ACHAIN_BAD, ACHAIN_DEFS).unwrap();
    let outcome = check(&old, &new, &opts());
    assert!(
        !matches!(outcome.status, Status::Proved { .. }),
        "a changed callback argument was proved equivalent: {:?}",
        outcome.status
    );
}
