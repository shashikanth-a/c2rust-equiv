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
