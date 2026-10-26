//! Running Kani on a scratch crate and parsing its output.

use std::path::Path;
use std::process::Command;
use std::time::Duration;

use crate::process;

#[derive(Debug, Default)]
pub struct Harness {
    pub name: String,
    pub checks: Vec<Check>,
    /// Inputs from concrete playback, one per failed check: one byte string per
    /// `kani::any()` value, little-endian.
    pub playbacks: Vec<Vec<Vec<u8>>>,
}

#[derive(Debug, Default)]
pub struct Check {
    pub name: String,
    pub status: String,
    pub description: String,
    /// The file part of the location, e.g. `src/old.rs`.
    pub file: Option<String>,
}

impl Check {
    pub fn failed(&self) -> bool {
        self.status == "FAILURE"
    }
}

pub enum Run {
    Done(Vec<Harness>),
    /// The crate didn't compile under Kani.
    BuildFailed(String),
    TimedOut,
}

/// Whether `cargo kani` works.
pub fn available() -> bool {
    Command::new("cargo")
        .args(["kani", "--version"])
        .output()
        .is_ok_and(|o| o.status.success())
}

pub fn run(dir: &Path, target_dir: &Path, timeout: Duration) -> std::io::Result<Run> {
    let mut cmd = Command::new("cargo");
    cmd.args([
        "kani",
        "-Z",
        "concrete-playback",
        "--concrete-playback=print",
        "--output-format",
        "regular",
    ])
    .current_dir(dir)
    .env("CARGO_TARGET_DIR", target_dir);
    let done = process::run(cmd, None, timeout, &dir.join("kani.log"))?;
    if done.status.is_none() {
        return Ok(Run::TimedOut);
    }
    if !done.output.contains("VERIFICATION:") {
        return Ok(Run::BuildFailed(first_error(&done.output)));
    }
    Ok(Run::Done(parse(&done.output)))
}

/// The first `error` line and a few after it.
pub fn first_error(output: &str) -> String {
    let lines: Vec<&str> = output.lines().collect();
    match lines.iter().position(|l| l.starts_with("error")) {
        Some(i) => lines[i..lines.len().min(i + 6)].join("\n"),
        None => lines[lines.len().saturating_sub(6)..].join("\n"),
    }
}

pub fn parse(output: &str) -> Vec<Harness> {
    let mut harnesses: Vec<Harness> = Vec::new();
    let mut playback_for: Option<String> = None;
    let mut playback: Option<Vec<Vec<u8>>> = None;
    for line in output.lines() {
        let trimmed = line.trim();
        if let Some(rest) = line.strip_prefix("Checking harness ") {
            harnesses.push(Harness {
                name: rest.trim_end_matches("...").to_owned(),
                ..Default::default()
            });
        } else if let Some(rest) = line.strip_prefix("Check ") {
            if let (Some(h), Some((_, name))) = (harnesses.last_mut(), rest.split_once(": ")) {
                h.checks.push(Check {
                    name: name.to_owned(),
                    ..Default::default()
                });
            }
        } else if let Some(rest) = trimmed.strip_prefix("- Status: ") {
            if let Some(c) = harnesses.last_mut().and_then(|h| h.checks.last_mut()) {
                c.status = rest.to_owned();
            }
        } else if let Some(rest) = trimmed.strip_prefix("- Description: ") {
            if let Some(c) = harnesses.last_mut().and_then(|h| h.checks.last_mut()) {
                c.description = rest.trim_matches('"').to_owned();
            }
        } else if let Some(rest) = trimmed.strip_prefix("- Location: ") {
            if let Some(c) = harnesses.last_mut().and_then(|h| h.checks.last_mut()) {
                c.file = rest.split(':').next().map(str::to_owned);
            }
        } else if let Some(rest) = line.strip_prefix("Concrete playback unit test for `") {
            playback_for = rest.split('`').next().map(str::to_owned);
        } else if trimmed.starts_with("let concrete_vals") {
            playback = Some(Vec::new());
        } else if let (Some(vals), Some(inner)) = (
            playback.as_mut(),
            trimmed
                .strip_prefix("vec![")
                .and_then(|s| s.trim_end_matches(',').strip_suffix(']')),
        ) {
            vals.push(
                inner
                    .split(',')
                    .filter_map(|b| b.trim().parse::<u8>().ok())
                    .collect(),
            );
        } else if trimmed == "];" {
            if let Some(vals) = playback.take() {
                let name = playback_for.clone().unwrap_or_default();
                if let Some(h) = harnesses.iter_mut().rev().find(|h| h.name == name) {
                    h.playbacks.push(vals);
                }
            }
        }
    }
    harnesses
}
