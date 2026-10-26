//! The core check: does a rewritten function behave the same as the original?

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use crate::kani;
use crate::process;
use crate::scratch;
use crate::unit::FnUnit;

#[derive(Clone, Debug)]
pub struct Options {
    /// Scratch crates and build output go here.
    pub work_dir: PathBuf,
    /// Try Kani before differential testing.
    pub kani: bool,
    /// Loop unwinding bound for Kani.
    pub unwind: u32,
    pub kani_timeout: Duration,
    /// Kani timeout for functions that use floating point, whose proofs are often slow.
    pub float_kani_timeout: Duration,
    pub test_timeout: Duration,
    /// Random inputs for differential testing, after the edge cases.
    pub cases: u64,
    /// Maximum combinations of per-argument edge cases.
    pub edge_limit: usize,
    pub seed: u64,
    /// Rust edition of the scratch crate.
    pub edition: String,
}

impl Options {
    pub fn new(work_dir: impl Into<PathBuf>) -> Self {
        Self {
            work_dir: work_dir.into(),
            kani: true,
            unwind: 8,
            kani_timeout: Duration::from_secs(60),
            float_kani_timeout: Duration::from_secs(20),
            test_timeout: Duration::from_secs(60),
            cases: 10_000,
            edge_limit: 4096,
            seed: 0,
            edition: "2021".to_owned(),
        }
    }

    /// The options that can change a result, for cache keys.
    pub fn fingerprint(&self) -> String {
        format!(
            "kani={} unwind={} kani_timeout={:?} float_kani_timeout={:?} test_timeout={:?} cases={} edge_limit={} seed={} edition={}",
            self.kani,
            self.unwind,
            self.kani_timeout,
            self.float_kani_timeout,
            self.test_timeout,
            self.cases,
            self.edge_limit,
            self.seed,
            self.edition
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Method {
    Kani,
    Testing,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum Status {
    /// Kani proved equivalence for executions within the unwinding bound.
    /// Its unwinding checks passed, so no loop needed more iterations.
    Proved {
        bounded: bool,
        unwind: u32,
    },
    /// An input on which the two versions behave differently, confirmed by
    /// running both natively.
    Counterexample {
        found_by: Method,
        inputs: String,
        old_out: String,
        new_out: String,
    },
    /// No difference found on `n_cases` inputs. This is not a proof.
    Tested {
        n_cases: u64,
        seed: u64,
        /// Why Kani didn't decide, if it was tried.
        kani_fallback: Option<String>,
    },
    Skipped {
        category: String,
        reason: String,
    },
    Error {
        reason: String,
    },
}

impl Status {
    /// A one-line summary, e.g. `proved(bounded, unwind=8)`.
    pub fn label(&self) -> String {
        match self {
            Status::Proved { unwind, .. } => format!("proved(bounded, unwind={unwind})"),
            Status::Counterexample {
                inputs,
                old_out,
                new_out,
                ..
            } => format!("counterexample(inputs={inputs}, old: {old_out}, new: {new_out})"),
            Status::Tested { n_cases, seed, .. } => {
                format!("tested(n_cases={n_cases}, seed={seed})")
            }
            Status::Skipped { category, reason } => format!("skipped({category}: {reason})"),
            Status::Error { reason } => format!("error({reason})"),
        }
    }
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.label())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Outcome {
    #[serde(flatten)]
    pub status: Status,
    pub kani_ms: Option<u64>,
    pub test_ms: Option<u64>,
    pub total_ms: u64,
}

/// Check whether `new` behaves the same as `old`: for every input, both return
/// the same value (floats compared by bits) or both panic.
///
/// Arithmetic overflow counts as a panic, as in a build with overflow checks,
/// because Kani always checks for it.
pub fn check(old: &FnUnit, new: &FnUnit, opts: &Options) -> Outcome {
    let start = Instant::now();
    let mut kani_ms = None;
    let mut test_ms = None;
    let status =
        run_check(old, new, opts, &mut kani_ms, &mut test_ms).unwrap_or_else(|e| Status::Error {
            reason: e.to_string(),
        });
    Outcome {
        status,
        kani_ms,
        test_ms,
        total_ms: start.elapsed().as_millis() as u64,
    }
}

fn run_check(
    old: &FnUnit,
    new: &FnUnit,
    opts: &Options,
    kani_ms: &mut Option<u64>,
    test_ms: &mut Option<u64>,
) -> io::Result<Status> {
    let old_sig = match old.validate() {
        Ok(sig) => sig,
        Err(skip) => return Ok(skipped(skip.category, skip.detail)),
    };
    let new_sig = match new.validate() {
        Ok(sig) => sig,
        Err(skip) => {
            return Ok(skipped(
                skip.category,
                format!("rewritten version: {}", skip.detail),
            ))
        }
    };
    if old_sig != new_sig {
        return Ok(skipped("signature".into(), "the signature changed".into()));
    }

    let dir = opts.work_dir.join("scratch").join(old.name());
    if dir.exists() {
        fs::remove_dir_all(&dir)?;
    }
    scratch::write(&dir, old, new, &opts.edition, opts.unwind)?;
    let runner = match build_runner(&dir, &opts.work_dir.join("target-native"))? {
        Ok(runner) => runner,
        Err(error) => {
            return Ok(Status::Error {
                reason: format!("scratch crate does not compile: {error}"),
            })
        }
    };

    let mut fallback = None;
    if opts.kani {
        let timeout = if old_sig.uses_floats() || old.uses_floats() || new.uses_floats() {
            opts.float_kani_timeout
        } else {
            opts.kani_timeout
        };
        let start = Instant::now();
        let decision = kani_decision(&dir, &runner, opts, timeout)?;
        *kani_ms = Some(start.elapsed().as_millis() as u64);
        match decision {
            Decision::Proved => {
                // A cheap native check that Kani's model agrees with the real code.
                let start = Instant::now();
                let tested = differential(&dir, &runner, opts, 0)?;
                *test_ms = Some(start.elapsed().as_millis() as u64);
                return Ok(match tested {
                    Status::Tested { .. } => Status::Proved {
                        bounded: true,
                        unwind: opts.unwind,
                    },
                    other => other,
                });
            }
            Decision::Counterexample(status) => return Ok(status),
            Decision::Fallback(reason) => fallback = Some(reason),
        }
    }
    let start = Instant::now();
    let mut status = differential(&dir, &runner, opts, opts.cases)?;
    *test_ms = Some(start.elapsed().as_millis() as u64);
    if let Status::Tested { kani_fallback, .. } = &mut status {
        *kani_fallback = fallback;
    }
    Ok(status)
}

fn skipped(category: String, reason: String) -> Status {
    Status::Skipped { category, reason }
}

/// Build the native runner; `Ok(Err(..))` if the crate doesn't compile.
fn build_runner(dir: &Path, target_dir: &Path) -> io::Result<Result<PathBuf, String>> {
    let mut cmd = Command::new("cargo");
    cmd.args(["build", "--release", "--offline", "--quiet"])
        .current_dir(dir)
        .env("CARGO_TARGET_DIR", target_dir);
    let done = process::run(cmd, None, Duration::from_secs(600), &dir.join("build.log"))?;
    if !done.success() {
        return Ok(Err(kani::first_error(&done.output)));
    }
    Ok(Ok(target_dir.join("release").join(format!(
        "{}{}",
        scratch::PACKAGE,
        std::env::consts::EXE_SUFFIX
    ))))
}

enum Decision {
    Proved,
    Counterexample(Status),
    Fallback(String),
}

fn kani_decision(
    dir: &Path,
    runner: &Path,
    opts: &Options,
    timeout: Duration,
) -> io::Result<Decision> {
    if !kani::available() {
        return Ok(Decision::Fallback("kani is not installed".into()));
    }
    let harnesses = match kani::run(dir, &opts.work_dir.join("target-kani"), timeout)? {
        kani::Run::Done(h) => h,
        kani::Run::TimedOut => {
            return Ok(Decision::Fallback(format!(
                "kani timed out after {}s",
                timeout.as_secs()
            )))
        }
        kani::Run::BuildFailed(e) => {
            return Ok(Decision::Fallback(format!("kani could not build: {e}")))
        }
    };
    let names: Vec<&str> = harnesses.iter().map(|h| h.name.as_str()).collect();
    if names != [scratch::NEW_FIRST, scratch::OLD_FIRST]
        && names != [scratch::OLD_FIRST, scratch::NEW_FIRST]
    {
        return Ok(Decision::Fallback(format!(
            "unexpected kani harnesses: {names:?}"
        )));
    }

    // Every failure Kani found, replayed natively. A difference there is real.
    let inputs: Vec<&Vec<Vec<u8>>> = harnesses.iter().flat_map(|h| &h.playbacks).collect();
    if !inputs.is_empty() {
        for line in replay(dir, runner, opts, &inputs)? {
            if let Some(status) = mismatch(&line, "DIFF", Method::Kani) {
                return Ok(Decision::Counterexample(status));
            }
        }
    }

    let checks = || {
        harnesses
            .iter()
            .flat_map(|h| h.checks.iter().map(move |c| (h, c)))
    };
    if let Some((_, c)) = checks().find(|(_, c)| {
        c.name.contains("unsupported_construct")
            || c.description.contains("not currently supported")
    }) {
        return Ok(Decision::Fallback(format!(
            "kani does not support: {}",
            c.description
        )));
    }
    if checks().any(|(_, c)| c.failed() && c.name.contains(".unwind.")) {
        return Ok(Decision::Fallback(format!(
            "a loop needs more than unwind={} iterations",
            opts.unwind
        )));
    }
    if let Some((_, c)) = checks().find(|(_, c)| c.status == "UNDETERMINED") {
        return Ok(Decision::Fallback(format!(
            "kani could not decide `{}`",
            c.description
        )));
    }
    // A failure inside the version a harness calls first is a panic of that
    // version, which cuts the path before the other runs: the other harness
    // covers that input. CBMC's own floating-point NaN checks aren't Rust
    // behaviour. Anything else that didn't reproduce natively is unexplained.
    let unexplained = checks().find(|(h, c)| {
        let first = if h.name == scratch::OLD_FIRST {
            scratch::OLD_FILE
        } else {
            scratch::NEW_FILE
        };
        c.failed() && c.file.as_deref() != Some(first) && !c.description.starts_with("NaN on ")
    });
    if let Some((_, c)) = unexplained {
        return Ok(Decision::Fallback(format!(
            "kani reported `{}` at {}, which did not reproduce natively",
            c.description,
            c.file.as_deref().unwrap_or("an unknown location")
        )));
    }
    Ok(Decision::Proved)
}

fn replay(
    dir: &Path,
    runner: &Path,
    opts: &Options,
    inputs: &[&Vec<Vec<u8>>],
) -> io::Result<Vec<String>> {
    let stdin: String = inputs
        .iter()
        .map(|fields| {
            let hex: Vec<String> = fields
                .iter()
                .map(|f| f.iter().map(|b| format!("{b:02x}")).collect())
                .collect();
            hex.join(",") + "\n"
        })
        .collect();
    let mut cmd = Command::new(runner);
    cmd.arg("replay");
    let done = process::run(
        cmd,
        Some(&stdin),
        opts.test_timeout,
        &dir.join("replay.log"),
    )?;
    if !done.success() {
        return Err(io::Error::other(format!(
            "replaying kani's inputs failed: {}",
            kani::first_error(&done.output)
        )));
    }
    Ok(done.output.lines().map(str::to_owned).collect())
}

/// Parse a runner line `TAG\tinputs\told\tnew` into a counterexample.
fn mismatch(line: &str, tag: &str, found_by: Method) -> Option<Status> {
    let mut fields = line.split('\t');
    if fields.next() != Some(tag) {
        return None;
    }
    Some(Status::Counterexample {
        found_by,
        inputs: fields.next()?.to_owned(),
        old_out: fields.next()?.to_owned(),
        new_out: fields.next()?.to_owned(),
    })
}

fn differential(dir: &Path, runner: &Path, opts: &Options, cases: u64) -> io::Result<Status> {
    let mut cmd = Command::new(runner);
    cmd.args([
        "test".to_owned(),
        opts.seed.to_string(),
        cases.to_string(),
        opts.edge_limit.to_string(),
    ]);
    let done = process::run(cmd, None, opts.test_timeout, &dir.join("test.log"))?;
    if done.status.is_none() {
        return Ok(Status::Error {
            reason: format!(
                "differential testing timed out after {}s",
                opts.test_timeout.as_secs()
            ),
        });
    }
    for line in done.output.lines() {
        if let Some(status) = mismatch(line, "MISMATCH", Method::Testing) {
            return Ok(status);
        }
        if let Some(n) = line.strip_prefix("OK\t") {
            return Ok(Status::Tested {
                n_cases: n.trim().parse().unwrap_or(0),
                seed: opts.seed,
                kani_fallback: None,
            });
        }
    }
    Ok(Status::Error {
        reason: format!(
            "the native runner failed ({}): {}",
            done.status.map_or("killed".into(), |s| s.to_string()),
            kani::first_error(&done.output)
        ),
    })
}
