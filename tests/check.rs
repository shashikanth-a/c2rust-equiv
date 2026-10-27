//! The core check on hand-written pairs of functions.
//!
//! Tests that need Kani print a message and pass when it isn't installed.

use c2rust_equiv::{check, kani, FnUnit, Method, Options, Status};

/// Equivalent.
const MAX_OLD: &str = "fn f(a: i32, b: i32) -> i32 { if a > b { a } else { b } }";
const MAX_NEW: &str = "fn f(a: i32, b: i32) -> i32 { a.max(b) }";

/// Off by one at 100 only, which random inputs are unlikely to hit.
const RANGE_OLD: &str = "fn f(x: i32) -> bool { x >= 0 && x < 100 }";
const RANGE_NEW: &str = "fn f(x: i32) -> bool { x >= 0 && x <= 100 }";

/// Sign handling: `/` rounds toward zero, `>>` toward negative infinity.
const HALF_OLD: &str = "fn f(x: i32) -> i32 { x / 2 }";
const HALF_NEW: &str = "fn f(x: i32) -> i32 { x >> 1 }";

/// NaN handling: the old version returns NaN for NaN, the new one 0.0.
const CLAMP_OLD: &str = "fn f(x: f64) -> f64 { if x < 0.0 { 0.0 } else { x } }";
const CLAMP_NEW: &str = "fn f(x: f64) -> f64 { if x >= 0.0 { x } else { 0.0 } }";

/// Both panic on the same inputs (division by zero, and `MIN / -1`), with
/// different messages. Kani is slow on division, so `kani_identical_panics_are_not_flagged`
/// uses `INDEX_*` instead.
const DIV_OLD: &str = "fn f(a: i16, b: i16) -> i16 { a / b }";
const DIV_NEW: &str = r#"fn f(a: i16, b: i16) -> i16 {
    if b == 0 { panic!("division by zero") }
    if a == i16::MIN && b == -1 { panic!("overflow") }
    a / b
}"#;

/// Both panic for `i >= 3`: one on an out-of-bounds index, the other explicitly.
const INDEX_OLD: &str = "fn f(i: usize) -> u8 { [10u8, 20, 30][i] }";
const INDEX_NEW: &str = r#"fn f(i: usize) -> u8 {
    match i { 0 => 10, 1 => 20, 2 => 30, _ => panic!("no such entry") }
}"#;

/// Both panic below 1000, and they differ at one rare input only. Kani may
/// print a panicking input for both harnesses; the difference must still be
/// reported, through a rerun on only the unexplained check.
const MASKED_OLD: &str = "fn f(x: u32) -> u32 { if x < 1000 { panic!() } x }";
const MASKED_NEW: &str =
    "fn f(x: u32) -> u32 { if x < 1000 { panic!() } if x == 123456789 { 0 } else { x } }";

/// For `i >= 3` the old version panics on an out-of-bounds index, and the
/// rewrite reads out of bounds with no check: undefined behaviour, not a panic.
const UNCHECKED_OLD: &str = "fn f(i: usize) -> u8 { [10u8, 20, 30][i] }";
const UNCHECKED_NEW: &str = "fn f(i: usize) -> u8 { unsafe { *[10u8, 20, 30].get_unchecked(i) } }";

/// Equivalent, but the loop runs up to 255 times, beyond Kani's unwinding bound.
const SUM_OLD: &str = r#"fn f(n: u8) -> u32 {
    let mut s = 0u32;
    let mut i = 0u8;
    while i < n { s += i as u32; i += 1; }
    s
}"#;
const SUM_NEW: &str =
    "fn f(n: u8) -> u32 { let n = n as u32; if n == 0 { 0 } else { n * (n - 1) / 2 } }";

/// Out of scope: raw pointers.
const PTR: &str = "fn f(x: i32) -> i32 { let p = &x as *const i32; unsafe { *p } }";

fn unit(src: &str) -> FnUnit {
    FnUnit::parse(src, &[]).unwrap()
}

fn run(old: &str, new: &str, kani: bool) -> Status {
    let dir = tempfile::tempdir().unwrap();
    let mut opts = Options::new(dir.path());
    opts.kani = kani;
    opts.cases = 2000;
    check(&unit(old), &unit(new), &opts).status
}

fn have_kani() -> bool {
    let available = kani::available();
    if !available {
        eprintln!("skipping: Kani is not installed (cargo install --locked kani-verifier && cargo kani setup)");
    }
    available
}

fn found_by(status: &Status) -> Option<Method> {
    match status {
        Status::Counterexample { found_by, .. } => Some(*found_by),
        _ => None,
    }
}

#[test]
fn testing_equivalent() {
    let status = run(MAX_OLD, MAX_NEW, false);
    assert!(matches!(status, Status::Tested { .. }), "{status}");
}

#[test]
fn testing_misses_rare_off_by_one() {
    // A limitation of testing, which Kani covers: see `kani_off_by_one`.
    let status = run(RANGE_OLD, RANGE_NEW, false);
    assert!(matches!(status, Status::Tested { .. }), "{status}");
}

#[test]
fn testing_sign_handling() {
    let status = run(HALF_OLD, HALF_NEW, false);
    assert_eq!(found_by(&status), Some(Method::Testing), "{status}");
}

#[test]
fn testing_nan_handling() {
    let status = run(CLAMP_OLD, CLAMP_NEW, false);
    assert_eq!(found_by(&status), Some(Method::Testing), "{status}");
    let Status::Counterexample { inputs, .. } = status else {
        unreachable!()
    };
    assert!(inputs.contains("NaN"), "{inputs}");
}

#[test]
fn testing_identical_panics() {
    let status = run(DIV_OLD, DIV_NEW, false);
    assert!(matches!(status, Status::Tested { .. }), "{status}");
}

#[test]
fn no_arguments_and_unit_return() {
    let status = run("fn f() -> i32 { 1 + 1 }", "fn f() -> i32 { 2 }", false);
    assert!(matches!(status, Status::Tested { .. }), "{status}");
    let status = run(
        "fn f(x: u8) { let _ = x; }",
        "fn f(x: u8) { assert!(x != 7); }",
        false,
    );
    assert_eq!(found_by(&status), Some(Method::Testing), "{status}");
}

#[test]
fn panics_in_extern_c_functions_are_caught() {
    let status = run(
        r#"pub unsafe extern "C" fn f(x: i32) -> i32 { x.wrapping_add(1) }"#,
        r#"pub unsafe extern "C" fn f(x: i32) -> i32 { x + 1 }"#,
        false,
    );
    let Status::Counterexample { new_out, .. } = &status else {
        panic!("{status}")
    };
    assert!(new_out.contains("overflow"), "{new_out}");
}

#[test]
fn extern_c_function_pointers_still_compile() {
    let src = r#"pub unsafe extern "C" fn f(x: u8) -> u8 {
        let g: unsafe extern "C" fn(u8) -> u8 = f;
        if x > 0 { g(x - 1) } else { 0 }
    }"#;
    let status = run(src, src, false);
    assert!(matches!(status, Status::Tested { .. }), "{status}");
}

#[test]
fn skipped_raw_pointer() {
    let status = run(PTR, PTR, false);
    let Status::Skipped { category, .. } = status else {
        panic!("{status}")
    };
    assert_eq!(category, "raw pointer");
}

#[test]
fn skipped_non_scalar_argument() {
    let status = run(
        "fn f(s: &str) -> usize { s.len() }",
        "fn f(s: &str) -> usize { s.len() }",
        false,
    );
    let Status::Skipped { category, .. } = status else {
        panic!("{status}")
    };
    assert_eq!(category, "signature");
}

#[test]
fn signature_change_is_skipped() {
    let status = run(
        "fn f(x: i32) -> i32 { x }",
        "fn f(x: i64) -> i64 { x }",
        false,
    );
    assert!(
        matches!(status, Status::Skipped { .. }) || matches!(status, Status::Error { .. }),
        "{status}"
    );
}

#[test]
fn kani_equivalent() {
    if !have_kani() {
        return;
    }
    let status = run(MAX_OLD, MAX_NEW, true);
    assert_eq!(
        status,
        Status::Proved {
            bounded: true,
            unwind: 8
        }
    );
}

#[test]
fn kani_off_by_one() {
    if !have_kani() {
        return;
    }
    let status = run(RANGE_OLD, RANGE_NEW, true);
    assert_eq!(found_by(&status), Some(Method::Kani), "{status}");
    let Status::Counterexample {
        inputs,
        old_out,
        new_out,
        ..
    } = status
    else {
        unreachable!()
    };
    assert_eq!(inputs, "(100)");
    assert_eq!(old_out, "returned false");
    assert_eq!(new_out, "returned true");
}

#[test]
fn kani_difference_behind_identical_panics() {
    if !have_kani() {
        return;
    }
    let status = run(MASKED_OLD, MASKED_NEW, true);
    assert_eq!(found_by(&status), Some(Method::Kani), "{status}");
    let Status::Counterexample { inputs, .. } = status else {
        unreachable!()
    };
    assert_eq!(inputs, "(123456789)");
}

#[test]
fn kani_undefined_behaviour_in_new_is_not_proved() {
    if !have_kani() {
        return;
    }
    let status = run(UNCHECKED_OLD, UNCHECKED_NEW, true);
    // Natively, the old version panics and the rewrite returns a value.
    assert_eq!(found_by(&status), Some(Method::Kani), "{status}");
    let Status::Counterexample { old_out, .. } = status else {
        unreachable!()
    };
    assert!(old_out.starts_with("panicked"), "{old_out}");
}

#[test]
fn kani_sign_handling() {
    if !have_kani() {
        return;
    }
    let status = run(HALF_OLD, HALF_NEW, true);
    assert_eq!(found_by(&status), Some(Method::Kani), "{status}");
}

#[test]
fn kani_nan_handling() {
    if !have_kani() {
        return;
    }
    let status = run(CLAMP_OLD, CLAMP_NEW, true);
    assert!(found_by(&status).is_some(), "{status}");
}

#[test]
fn kani_identical_panics_are_not_flagged() {
    if !have_kani() {
        return;
    }
    let status = run(INDEX_OLD, INDEX_NEW, true);
    assert_eq!(
        status,
        Status::Proved {
            bounded: true,
            unwind: 8
        }
    );
}

#[test]
fn kani_panic_only_in_new_is_flagged() {
    if !have_kani() {
        return;
    }
    let status = run(
        MAX_OLD,
        "fn f(a: i32, b: i32) -> i32 { if a == 3 { panic!() } a.max(b) }",
        true,
    );
    let Status::Counterexample {
        found_by, new_out, ..
    } = status
    else {
        panic!("{status}")
    };
    assert_eq!(found_by, Method::Kani);
    assert!(new_out.starts_with("panicked"), "{new_out}");
}

#[test]
fn kani_loop_bound_falls_back_to_testing() {
    if !have_kani() {
        return;
    }
    let status = run(SUM_OLD, SUM_NEW, true);
    let Status::Tested {
        kani_fallback: Some(reason),
        ..
    } = &status
    else {
        panic!("{status}")
    };
    assert!(reason.contains("unwind=8"), "{reason}");
}

#[test]
fn kani_callees_are_checked() {
    if !have_kani() {
        return;
    }
    let old = FnUnit::parse(
        "fn f(x: u8) -> u8 { g(x) }",
        &["fn g(x: u8) -> u8 { x.wrapping_add(1) }"],
    )
    .unwrap();
    let new = FnUnit::parse(
        "fn f(x: u8) -> u8 { g(x) }",
        &["fn g(x: u8) -> u8 { x + 1 }"],
    )
    .unwrap();
    let dir = tempfile::tempdir().unwrap();
    let status = check(&old, &new, &Options::new(dir.path())).status;
    let Status::Counterexample {
        inputs, new_out, ..
    } = status
    else {
        panic!("{status}")
    };
    assert_eq!(inputs, "(255)");
    assert!(new_out.contains("overflow"), "{new_out}");
}
