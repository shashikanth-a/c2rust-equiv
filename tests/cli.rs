//! The command-line interface, on the crates in `tests/fixtures`.

use std::path::Path;
use std::process::Command;

fn run(args: &[&str]) -> (i32, serde_json::Value) {
    let dir = tempfile::tempdir().unwrap();
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let report = dir.path().join("report.json");
    let status = Command::new(env!("CARGO_BIN_EXE_c2rust-equiv"))
        .arg("--old")
        .arg(fixtures.join("old"))
        .arg("--new")
        .arg(fixtures.join("new"))
        .arg("--report")
        .arg(&report)
        .arg("--work-dir")
        .arg(dir.path().join("work"))
        .args(["--no-kani", "--cases", "500"])
        .args(args)
        .status()
        .unwrap();
    assert!(report.with_extension("md").exists());
    let json = serde_json::from_str(&std::fs::read_to_string(&report).unwrap()).unwrap();
    (status.code().unwrap(), json)
}

fn statuses(report: &serde_json::Value) -> Vec<(String, String)> {
    report["functions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|f| {
            (
                f["id"].as_str().unwrap().to_owned(),
                f["status"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

#[test]
fn checks_changed_functions() {
    let (code, report) = run(&[]);
    assert_eq!(code, 1);
    assert_eq!(
        statuses(&report),
        [
            ("src/math.rs::half".to_owned(), "counterexample".to_owned()),
            ("src/math.rs::larger".to_owned(), "tested".to_owned()),
            ("src/math.rs::read".to_owned(), "skipped".to_owned()),
        ]
    );
    assert_eq!(report["summary"]["total_functions"], 4);
    assert_eq!(report["summary"]["eligible_functions"], 3);
}

#[test]
fn exit_code_is_zero_without_counterexamples() {
    let (code, report) = run(&["--function", "larger"]);
    assert_eq!(code, 0);
    assert_eq!(statuses(&report).len(), 1);
}

#[test]
fn unknown_function_is_an_error() {
    let (code, _) = run(&["--function", "missing"]);
    assert_eq!(code, 2);
}

#[test]
fn cache_hits_on_rerun() {
    let dir = tempfile::tempdir().unwrap();
    let cache = dir.path().join("cache.json");
    let cache = cache.to_str().unwrap();
    let (_, first) = run(&["--cache", cache]);
    assert_eq!(first["summary"]["cache_hits"], 0);
    let (_, second) = run(&["--cache", cache]);
    // `read` is skipped before the cache is consulted.
    assert_eq!(second["summary"]["cache_hits"], 2);
}

#[test]
fn eligibility_lists_every_function() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("eligibility.jsonl");
    run(&["--eligibility", path.to_str().unwrap()]);
    let rows: Vec<serde_json::Value> = std::fs::read_to_string(&path)
        .unwrap()
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    assert_eq!(rows.len(), 4);
    let read = rows
        .iter()
        .find(|r| r["id"] == "src/math.rs::read")
        .unwrap();
    assert_eq!(read["eligible"], false);
    assert_eq!(read["category"], "raw pointer");
}

#[test]
fn relative_work_dir() {
    let dir = tempfile::tempdir().unwrap();
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let status = Command::new(env!("CARGO_BIN_EXE_c2rust-equiv"))
        .current_dir(dir.path())
        .arg("--old")
        .arg(fixtures.join("old"))
        .arg("--new")
        .arg(fixtures.join("new"))
        .args(["--report", "report.json", "--work-dir", "work", "--no-kani"])
        .args(["--function", "larger"])
        .status()
        .unwrap();
    assert_eq!(status.code(), Some(0));
}
