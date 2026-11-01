//! The core check: does a rewritten function behave the same as the original?

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use crate::crate_index::CrateIndex;
use crate::heapgen::{self, SigShapes};
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
            // An algebraic equality-saturation proof is unbounded
            // and holds for all inputs; a Kani proof is bounded by the unwind.
            Status::Proved {
                bounded: false,
                unwind: 0,
            } => "proved(algebraic)".to_owned(),
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

/// Whether two signatures have the same argument types (ignoring names) and the
/// same return type. Used to gate the algebraic proof, which compares bodies
/// structurally and so is only sound when the interfaces match.
fn same_param_and_return_types(a: &syn::Signature, b: &syn::Signature) -> bool {
    use quote::ToTokens;
    let arg_types = |s: &syn::Signature| -> Vec<String> {
        s.inputs
            .iter()
            .map(|arg| match arg {
                syn::FnArg::Typed(pt) => pt.ty.to_token_stream().to_string(),
                syn::FnArg::Receiver(r) => r.to_token_stream().to_string(),
            })
            .collect()
    };
    let ret_type = |s: &syn::Signature| -> String {
        match &s.output {
            syn::ReturnType::Default => String::new(),
            syn::ReturnType::Type(_, t) => t.to_token_stream().to_string(),
        }
    };
    arg_types(a) == arg_types(b) && ret_type(a) == ret_type(b)
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
    // Try an environment-independent algebraic proof by equality
    // saturation first (no Kani, no environment model, and unbounded -- it holds
    // for all inputs, not only within an unwinding bound). It is sound: a
    // `Some(true)` is a real proof; anything else falls through to the Kani /
    // differential path below. Only attempt it when both functions take and
    // return exactly the same types: structural equality of two bodies implies
    // behavioural equivalence only then, so a signature change (identity on
    // `i32` vs on `i64`) is left to the checks below, which skip it rather than
    // proving it. Argument *names* may differ -- a pure rename is a valid
    // equivalent rewrite -- so compare the types, not the whole signature.
    let sigs_match = same_param_and_return_types(&old.function.sig, &new.function.sig);
    if sigs_match && crate::peg::equivalent(&old.function, &new.function) == Some(true) {
        return Outcome {
            status: Status::Proved {
                bounded: false,
                unwind: 0,
            },
            kani_ms: None,
            test_ms: None,
            total_ms: start.elapsed().as_millis() as u64,
        };
    }
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
    // Functions that pass pointers to structs the generator supports take the
    // heap path; everything else takes the scalar path below.
    if let Some((shapes, code)) = heap_plan(old, new) {
        return run_heap_check(old, new, opts, &shapes, &code, kani_ms);
    }

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

    // Cargo resolves a relative `CARGO_TARGET_DIR` against the scratch crate.
    let opts = &Options {
        work_dir: std::env::current_dir()?.join(&opts.work_dir),
        ..opts.clone()
    };
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

/// Whether the heap path can take this function: its signature passes or
/// returns a pointer to a struct the generator supports, its body is in scope
/// for the heap path, and every reachable struct generates. This is the scope
/// test for one version (the live path additionally requires both versions to
/// share the same shape).
pub fn heap_eligible(unit: &FnUnit) -> bool {
    heap_diagnose(unit).is_ok()
}

/// Like [`heap_eligible`], but naming the stage that puts the function out of
/// the heap path's scope, so a scan can see where effort would pay off:
/// `"signature"` (an argument/return the generator can't shape), `"not-heap"`
/// (all scalars -- the scalar path handles it), `"body"` (IO, a global, or a
/// foreign or crate call), or `"generate:<reason>"` (a struct field it can't
/// build). `Ok(())` means in scope.
pub fn heap_diagnose(unit: &FnUnit) -> Result<(), String> {
    let index = index_of(unit).ok_or("index")?;
    let shapes = heapgen::signature_shapes(&index, &unit.function.sig)
        .map_err(|u| format!("signature: {}", u.detail))?;
    // A pointer-free ("not-heap") signature is allowed through here: this is
    // reached only after the scalar path has already rejected the function (the
    // eligibility pass and `check` both try scalar first), so routing it through
    // the heap path gives it the heap path's modelling (globals, foreign-call
    // traces, mutex no-ops) with a trivial empty heap. The body and generate
    // checks below still gate it.
    unit.heap_body_in_scope()
        .map_err(|s| format!("body: {} ({})", s.detail, s.category))?;
    let mut roots = shapes.structs.clone();
    roots.extend(struct_global_roots(unit));
    heapgen::generate_all(&index, &roots, &unit.union_tags, "old", "new").map_err(|u| {
        format!(
            "generate: {} field `{}`: {}",
            u.struct_name, u.field, u.detail
        )
    })?;
    Ok(())
}

/// The struct types of a unit's modelled `static mut` globals, which must be
/// built and compared (`sameval_<T>`) alongside the signature's structs.
fn struct_global_roots(unit: &FnUnit) -> std::collections::BTreeSet<String> {
    let items = unit.items();
    let structs = heapgen::data_struct_fields_from_items(&items);
    let aliases = heapgen::alias_table_from_items(&items);
    items
        .iter()
        .filter_map(|it| match it {
            syn::Item::Static(s) => crate::unit::modelled_struct_mut_static(s, &structs, &aliases),
            _ => None,
        })
        .collect()
}

/// A crate index over a unit's own items, so the generator can see its structs.
fn index_of(unit: &FnUnit) -> Option<CrateIndex> {
    let file = syn::File {
        shebang: None,
        attrs: vec![],
        items: unit.items(),
    };
    let mut index = CrateIndex::default();
    index
        .add_source("unit.rs", &prettyplease::unparse(&file))
        .ok()?;
    Some(index)
}

/// If both versions take or return pointers to structs the generator supports
/// (and their bodies are in scope for the heap path), the shared shapes and the
/// generated builder/cloner/comparer code. `None` falls through to the scalar
/// path, which reports why the function is out of scope.
fn heap_plan(old: &FnUnit, new: &FnUnit) -> Option<(SigShapes, String)> {
    let index = index_of(old)?;
    let shapes = heapgen::signature_shapes(&index, &old.function.sig).ok()?;
    if !shapes.needs_heap() {
        // A pointer-free signature: let the scalar path (native testing) own it
        // unless the scalar path rejects it -- a global, foreign call, IO or
        // mutex the heap path can model. Only then route it through the heap
        // harness (symbolic scalar args, compare the return and any modelled
        // global's final state), a superset of the scalar check.
        if old.validate().is_ok() {
            return None;
        }
    }
    // The rewrite must have the same shape, or it isn't a drop-in replacement.
    let new_shapes = heapgen::signature_shapes(&index_of(new)?, &new.function.sig).ok()?;
    if new_shapes.args != shapes.args || new_shapes.ret != shapes.ret {
        return None;
    }
    // Pointers are allowed on this path, but IO, globals and foreign calls still
    // put the function out of scope; the scalar path then reports the reason.
    old.heap_body_in_scope().ok()?;
    new.heap_body_in_scope().ok()?;
    let mut roots = shapes.structs.clone();
    roots.extend(struct_global_roots(old));
    let code = heapgen::generate_all(&index, &roots, &old.union_tags, "old", "new").ok()?;
    Some((shapes, code))
}

fn run_heap_check(
    old: &FnUnit,
    new: &FnUnit,
    opts: &Options,
    shapes: &SigShapes,
    code: &str,
    kani_ms: &mut Option<u64>,
) -> io::Result<Status> {
    if !opts.kani {
        return Ok(skipped(
            "heap".into(),
            "the heap path needs Kani (there is no native heap runner yet)".into(),
        ));
    }
    let opts = &Options {
        work_dir: std::env::current_dir()?.join(&opts.work_dir),
        ..opts.clone()
    };
    let dir = opts.work_dir.join("scratch").join(old.name());
    if dir.exists() {
        fs::remove_dir_all(&dir)?;
    }
    scratch::write_heap(&dir, old, new, &opts.edition, opts.unwind, shapes, code)?;
    let timeout = if old.uses_floats() || new.uses_floats() {
        opts.float_kani_timeout
    } else {
        opts.kani_timeout
    };
    let start = Instant::now();
    let status = heap_decision(&dir, opts, timeout)?;
    *kani_ms = Some(start.elapsed().as_millis() as u64);
    Ok(status)
}

/// The heap path's verdict. It only ever proves or skips: without a native
/// heap runner it can't confirm a difference, and the spec requires every
/// reported counterexample to be real (specs/Verdict.tla), so an unconfirmed
/// Kani failure is reported as a skip with its reason, never as a proof.
fn heap_decision(dir: &Path, opts: &Options, timeout: Duration) -> io::Result<Status> {
    if !kani::available() {
        return Ok(skipped("heap".into(), "kani is not installed".into()));
    }
    let harnesses = match kani::run(dir, &opts.work_dir.join("target-kani"), timeout)? {
        kani::Run::Done(h) => h,
        kani::Run::TimedOut => {
            return Ok(skipped(
                "heap".into(),
                format!("kani timed out after {}s", timeout.as_secs()),
            ))
        }
        kani::Run::BuildFailed(e) => {
            return Ok(Status::Error {
                reason: format!("heap scratch crate did not build under kani: {e}"),
            })
        }
    };
    let names: Vec<&str> = harnesses.iter().map(|h| h.name.as_str()).collect();
    if names != [scratch::NEW_FIRST, scratch::OLD_FIRST]
        && names != [scratch::OLD_FIRST, scratch::NEW_FIRST]
    {
        return Ok(skipped(
            "heap".into(),
            format!("unexpected kani harnesses: {names:?}"),
        ));
    }
    let checks = || harnesses.iter().flat_map(|h| h.checks.iter());
    // Allocation pulls in constructs Kani can't model (the alloc-error handler,
    // caller_location); Kani proves them unreachable and marks them SUCCESS.
    // Only a *failed* unsupported-construct check (a reachable one) disqualifies.
    if let Some(c) = checks().find(|c| {
        c.failed()
            && (c.name.contains("unsupported_construct")
                || c.description.contains("not currently supported"))
    }) {
        return Ok(skipped(
            "heap".into(),
            format!("kani does not support: {}", c.description),
        ));
    }
    if checks().any(|c| c.failed() && c.name.contains(".unwind.")) {
        return Ok(skipped(
            "heap".into(),
            format!("a loop needs more than unwind={} iterations", opts.unwind),
        ));
    }
    if let Some(c) = checks().find(|c| c.status == "UNDETERMINED") {
        return Ok(skipped(
            "heap".into(),
            format!("kani could not decide `{}`", c.description),
        ));
    }
    if let Some(c) = harnesses
        .iter()
        .find_map(|h| unexplained(h).first().copied())
    {
        return Ok(skipped(
            "heap".into(),
            format!(
                "kani reported `{}`, a possible difference the heap path can't yet confirm natively",
                c.description
            ),
        ));
    }
    if let Some(h) = harnesses.iter().find(|h| {
        h.checks.is_empty() || h.verified != Some(!h.checks.iter().any(kani::Check::failed))
    }) {
        return Ok(skipped(
            "heap".into(),
            format!("kani's output for {} could not be parsed", h.name),
        ));
    }
    Ok(Status::Proved {
        bounded: true,
        unwind: opts.unwind,
    })
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
    if let Some(c) = harnesses
        .iter()
        .find_map(|h| unexplained(h).first().copied())
    {
        // Kani prints one input per failing harness, which may be a harmless
        // panic. Rerunning on only the unexplained properties makes it print
        // an input that violates one of them (specs/Verdict.tla).
        for h in &harnesses {
            let properties: Vec<&str> = unexplained(h).iter().map(|c| c.name.as_str()).collect();
            if properties.is_empty() {
                continue;
            }
            let target = opts.work_dir.join("target-kani");
            if let kani::Run::Done(rerun) =
                kani::run_properties(dir, &target, timeout, &h.name, &properties)?
            {
                let inputs: Vec<&Vec<Vec<u8>>> = rerun.iter().flat_map(|h| &h.playbacks).collect();
                if !inputs.is_empty() {
                    for line in replay(dir, runner, opts, &inputs)? {
                        if let Some(status) = mismatch(&line, "DIFF", Method::Kani) {
                            return Ok(Decision::Counterexample(status));
                        }
                    }
                }
            }
        }
        return Ok(Decision::Fallback(format!(
            "kani reported `{}` at {}, which did not reproduce natively",
            c.description,
            c.file.as_deref().unwrap_or("an unknown location")
        )));
    }
    // A verdict that disagrees with the checks means the output wasn't parsed
    // as expected, and a missed failure would otherwise read as a proof.
    if let Some(h) = harnesses.iter().find(|h| {
        h.checks.is_empty() || h.verified != Some(!h.checks.iter().any(kani::Check::failed))
    }) {
        return Ok(Decision::Fallback(format!(
            "kani's output for {} could not be parsed",
            h.name
        )));
    }

    Ok(Decision::Proved)
}

/// Failed checks that aren't a panic of the version the harness calls first.
///
/// A panic ends the path before the other version runs, and the other
/// harness covers the input. Nothing else is ignored: undefined behaviour
/// doesn't end the path in Kani, and it may be reported in a standard library
/// file rather than the version's own (specs/Verdict.tla). CBMC's own
/// floating-point NaN checks aren't Rust behaviour.
fn unexplained(h: &kani::Harness) -> Vec<&kani::Check> {
    let first = if h.name == scratch::OLD_FIRST {
        scratch::OLD_FILE
    } else {
        scratch::NEW_FILE
    };
    h.checks
        .iter()
        .filter(|c| {
            let first_panicked = c.file.as_deref() == Some(first) && c.class() == "assertion";
            c.failed() && !first_panicked && !c.description.starts_with("NaN on ")
        })
        .collect()
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
