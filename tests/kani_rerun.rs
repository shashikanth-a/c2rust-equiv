//! Rerunning Kani on selected properties only.
//!
//! Skipped (passes) when Kani isn't installed.

use std::fs;
use std::time::Duration;

use c2rust_equiv::kani;

const CRATE: &str = r#"[package]
name = "rerun"
version = "0.0.0"
edition = "2021"

[workspace]

[lints.rust]
unexpected_cfgs = { level = "allow", check-cfg = ["cfg(kani)"] }
"#;

/// Both panic at 0 and differ at 5, so the harness fails two checks.
const LIB: &str = r#"
pub fn old(x: u8) -> u8 { if x == 0 { panic!("zero") } x }
pub fn new(x: u8) -> u8 { if x == 0 { panic!("zero") } if x == 5 { 6 } else { x } }
#[cfg(kani)]
mod proofs {
    #[kani::proof]
    fn old_then_new() {
        let x: u8 = kani::any();
        let o = super::old(x);
        let n = super::new(x);
        assert!(o == n, "results differ");
    }
}
"#;

#[test]
fn rerun_reports_only_the_selected_property() {
    if !kani::available() {
        eprintln!("kani is not installed; skipping");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    fs::create_dir_all(dir.path().join("src")).unwrap();
    fs::write(dir.path().join("Cargo.toml"), CRATE).unwrap();
    fs::write(dir.path().join("src/lib.rs"), LIB).unwrap();
    let target = dir.path().join("target");
    let timeout = Duration::from_secs(300);

    let kani::Run::Done(all) = kani::run(dir.path(), &target, timeout).unwrap() else {
        panic!("kani did not run");
    };
    let failed: Vec<&str> = all[0]
        .checks
        .iter()
        .filter(|c| c.failed())
        .map(|c| c.name.as_str())
        .collect();
    assert_eq!(failed.len(), 2, "{failed:?}");
    let assertion = all[0]
        .checks
        .iter()
        .find(|c| c.description == "results differ")
        .unwrap();

    let kani::Run::Done(rerun) = kani::run_properties(
        dir.path(),
        &target,
        timeout,
        "proofs::old_then_new",
        &[assertion.name.as_str()],
    )
    .unwrap() else {
        panic!("kani did not rerun");
    };
    assert_eq!(rerun.len(), 1);
    let failed: Vec<&str> = rerun[0]
        .checks
        .iter()
        .filter(|c| c.failed())
        .map(|c| c.name.as_str())
        .collect();
    assert_eq!(failed, [assertion.name.as_str()]);
    // The only input printed is the real difference, not the shared panic.
    assert_eq!(rerun[0].playbacks, vec![vec![vec![5u8]]]);
}
