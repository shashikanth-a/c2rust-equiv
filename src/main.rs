use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use c2rust_equiv::report::{FunctionReport, Report};
use c2rust_equiv::{cache, check, extract, CrateIndex, Options, Outcome, Status};
use clap::Parser;
use quote::ToTokens;

/// Check that functions in a rewritten crate behave the same as in the original.
///
/// Exit codes: 0 if every checked function was proved or tested (or skipped),
/// 1 if any function has a counterexample, 2 on a tool error.
#[derive(Parser)]
#[command(version)]
struct Cli {
    /// The original crate's source directory (or a single `.rs` file).
    #[arg(long)]
    old: PathBuf,
    /// The rewritten crate's source directory (or a single `.rs` file).
    #[arg(long)]
    new: PathBuf,
    /// Where to write the JSON report.
    #[arg(long)]
    report: PathBuf,
    /// Where to write the Markdown summary [default: the report path with `.md`].
    #[arg(long)]
    markdown: Option<PathBuf>,
    /// Check this function: an ID like `src/a.rs::f`, or a bare name.
    /// Repeatable. [default: every function whose code differs, or that the
    /// rewrite lacks]
    #[arg(long = "function")]
    functions: Vec<String>,
    /// A file with one function ID or name per line, as for `--function`.
    #[arg(long)]
    functions_file: Option<PathBuf>,
    /// Directory for scratch crates and build output [default: a directory under the system temp dir].
    #[arg(long)]
    work_dir: Option<PathBuf>,
    /// A JSON file to cache results in, across runs.
    #[arg(long)]
    cache: Option<PathBuf>,
    /// Don't try Kani; only run differential tests.
    #[arg(long)]
    no_kani: bool,
    /// Kani's loop unwinding bound.
    #[arg(long, default_value_t = 8)]
    unwind: u32,
    /// Kani timeout per function, in seconds.
    #[arg(long, default_value_t = 60)]
    kani_timeout: u64,
    /// Kani timeout per function that uses floating point, in seconds.
    #[arg(long, default_value_t = 20)]
    float_kani_timeout: u64,
    /// Differential testing timeout per function, in seconds.
    #[arg(long, default_value_t = 60)]
    test_timeout: u64,
    /// Random inputs per function, after the edge cases.
    #[arg(long, default_value_t = 10_000)]
    cases: u64,
    /// Maximum combinations of per-argument edge cases.
    #[arg(long, default_value_t = 4096)]
    edge_limit: usize,
    /// Seed for random inputs.
    #[arg(long, default_value_t = 0)]
    seed: u64,
    /// Rust edition for the scratch crates.
    #[arg(long, default_value = "2021")]
    edition: String,
    /// Write whether each function in the original crate is in scope, and why
    /// not, as JSON lines.
    #[arg(long)]
    eligibility: Option<PathBuf>,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    // A panic is a tool error too, so it exits with 2 rather than 101.
    match std::panic::catch_unwind(|| run(&cli)) {
        Ok(Ok(code)) => ExitCode::from(code),
        Ok(Err(e)) => {
            eprintln!("error: {e}");
            ExitCode::from(2)
        }
        Err(_) => ExitCode::from(2),
    }
}

fn run(cli: &Cli) -> Result<u8, Box<dyn std::error::Error>> {
    let old = CrateIndex::load(&cli.old)?;
    let new = CrateIndex::load(&cli.new)?;
    // Silently missing functions would make a broken rewrite look fine.
    for (side, index) in [("original", &old), ("rewritten", &new)] {
        if let Some((file, error)) = index.parse_errors.first() {
            return Err(format!("{side} crate: {file} doesn't parse: {error}").into());
        }
    }

    let work_dir = cli
        .work_dir
        .clone()
        .unwrap_or_else(|| std::env::temp_dir().join("c2rust-equiv"));
    let opts = Options {
        work_dir,
        kani: !cli.no_kani,
        unwind: cli.unwind,
        kani_timeout: Duration::from_secs(cli.kani_timeout),
        float_kani_timeout: Duration::from_secs(cli.float_kani_timeout),
        test_timeout: Duration::from_secs(cli.test_timeout),
        cases: cli.cases,
        edge_limit: cli.edge_limit,
        seed: cli.seed,
        edition: cli.edition.clone(),
    };
    let mut cache = cli.cache.as_deref().map(cache::Cache::open).transpose()?;

    let mut queries = cli.functions.clone();
    if let Some(path) = &cli.functions_file {
        let text = fs::read_to_string(path)?;
        queries.extend(
            text.lines()
                .map(str::trim)
                .filter(|l| !l.is_empty() && !l.starts_with('#'))
                .map(str::to_owned),
        );
    }

    // Unchanged, summarisable callees within `old` may be replaced by a shim
    // instead of inlined, which lifts functions blocked only by an out-of-scope
    // callee into heap scope (Subsystem A). Eligibility uses old-vs-old: a
    // callee identical to itself is trivially equivalent, so its shim is sound.
    let elig_summaries = c2rust_equiv::compose::summary_catalog(&old, &old);
    let total_functions = old.functions().count();
    let mut eligible_functions = 0;
    let mut heap_eligible_functions = 0;
    let mut eligibility = String::new();
    for e in old.functions() {
        let line = match extract(&old, e) {
            Ok(_) => {
                eligible_functions += 1;
                serde_json::json!({ "id": old.id(e), "eligible": true, "path": "scalar" })
            }
            Err(skip) => {
                // A scalar-ineligible function may still be in scope for the
                // heap path (it passes or returns a pointer to a struct the
                // generator supports).
                let diag = c2rust_equiv::extract_heap_composed(&old, e, &elig_summaries)
                    .map_err(|s| format!("extract:{} ({})", s.category, s.detail))
                    .and_then(|u| c2rust_equiv::heap_diagnose(&u));
                let heap = diag.is_ok();
                if heap {
                    heap_eligible_functions += 1;
                }
                serde_json::json!({
                    "id": old.id(e),
                    "eligible": heap,
                    "path": if heap { "heap" } else { "none" },
                    "category": skip.category,
                    "reason": skip.detail,
                    // Why the heap path can't take it: the failing stage, so a
                    // scan can see where effort would pay off.
                    "heap_stage": diag.err(),
                })
            }
        };
        eligibility += &format!("{line}\n");
    }
    eprintln!(
        "eligibility: {eligible_functions} scalar + {heap_eligible_functions} heap = {} of {total_functions} functions",
        eligible_functions + heap_eligible_functions
    );
    if let Some(path) = &cli.eligibility {
        fs::write(path, eligibility)?;
    }

    // For the real checks, a callee may be summarised when it is unchanged
    // between old and new (token-identical, in the base catalog) or has itself
    // been proven equivalent. Subsystem A phase A4 realises the latter with a
    // bottom-up fixpoint: after each pass, every function newly proved
    // equivalent is added to the catalog as a summary shim, so a caller blocked
    // only by that (changed) callee can be re-checked with it summarised
    // instead of inlined. Soundness holds for any order -- `proven` only ever
    // grows with functions actually proved; the passes add completeness.
    let selected = select(&old, &new, &queries);
    let mut catalog = c2rust_equiv::compose::summary_catalog(&old, &new);
    let mut proven: std::collections::BTreeSet<String> = catalog.keys().cloned().collect();
    let mut results_map: std::collections::BTreeMap<String, (c2rust_equiv::Outcome, bool)> =
        std::collections::BTreeMap::new();
    const MAX_PASSES: usize = 3;
    for pass in 0..MAX_PASSES {
        let mut added = false;
        for (i, id) in selected.iter().enumerate() {
            // Keep a function once it has been proved; only retry the rest with
            // the (possibly grown) catalog.
            if matches!(results_map.get(id), Some((o, _)) if matches!(o.status, c2rust_equiv::Status::Proved { .. })) {
                continue;
            }
            let (outcome, cached) = check_one(&old, &new, id, &opts, &catalog, cache.as_mut());
            let is_proved = matches!(outcome.status, c2rust_equiv::Status::Proved { .. });
            eprintln!(
                "[pass {}][{}/{}] {id}: {}{}",
                pass + 1,
                i + 1,
                selected.len(),
                outcome.status.label(),
                if cached { " (cached)".to_owned() } else { format!(" ({} ms)", outcome.total_ms) }
            );
            results_map.insert(id.clone(), (outcome, cached));
            if is_proved {
                let short = id.rsplit("::").next().unwrap_or(id).to_owned();
                if proven.insert(short.clone()) {
                    if let Some(shim) = c2rust_equiv::compose::proven_shim(&old, &short) {
                        catalog.insert(short, shim);
                        added = true;
                    }
                }
            }
        }
        // A fixpoint: stop once a pass proves nothing new to summarise.
        if !added {
            break;
        }
    }
    let results: Vec<FunctionReport> = selected
        .iter()
        .map(|id| {
            let (outcome, cached) = results_map.remove(id).expect("every selected id was checked");
            FunctionReport { id: id.clone(), label: outcome.status.label(), cached, outcome }
        })
        .collect();
    if let Some(cache) = &cache {
        cache.save()?;
    }

    let report = Report::new(
        opts.fingerprint(),
        total_functions,
        eligible_functions,
        results,
    );
    fs::write(&cli.report, serde_json::to_string_pretty(&report)?)?;
    let markdown = cli
        .markdown
        .clone()
        .unwrap_or_else(|| cli.report.with_extension("md"));
    fs::write(markdown, report.markdown())?;
    Ok(report.exit_code())
}

/// Function IDs to check: those matching `queries`, or by default every
/// function in the original crate whose code differs in the rewrite, or that
/// the rewrite lacks.
fn select(old: &CrateIndex, new: &CrateIndex, queries: &[String]) -> Vec<String> {
    let mut ids = BTreeSet::new();
    if queries.is_empty() {
        for e in old.functions() {
            let id = old.id(e);
            match new.find_functions(&id).as_slice() {
                [n] if code(old, e) == code(new, *n) => {}
                // Missing from the rewrite: reported as an error by `check_one`.
                _ => {
                    ids.insert(id);
                }
            }
        }
    } else {
        for q in queries {
            let found: Vec<usize> = old.find_functions(q);
            if found.is_empty() {
                // Reported as an error by `check_one`.
                ids.insert(q.clone());
            }
            ids.extend(found.into_iter().map(|e| old.id(e)));
        }
    }
    ids.into_iter().collect()
}

/// A function's code, ignoring formatting, comments and doc comments.
fn code(index: &CrateIndex, entry: usize) -> String {
    let Some(syn::Item::Fn(f)) = &index.entries[entry].item else {
        return String::new();
    };
    let mut f = f.clone();
    f.attrs.retain(|a| !a.path().is_ident("doc"));
    f.to_token_stream().to_string()
}

fn check_one(
    old: &CrateIndex,
    new: &CrateIndex,
    id: &str,
    opts: &Options,
    summaries: &std::collections::BTreeMap<String, syn::ItemFn>,
    cache: Option<&mut cache::Cache>,
) -> (Outcome, bool) {
    let immediate = |status| {
        (
            Outcome {
                status,
                kani_ms: None,
                test_ms: None,
                total_ms: 0,
            },
            false,
        )
    };
    let (Some(&o), Some(&n)) = (
        old.find_functions(id).first(),
        new.find_functions(id).first(),
    ) else {
        return immediate(Status::Error {
            reason: format!("`{id}` is not in both crates"),
        });
    };
    // Prefer the scalar extraction; if it rejects the function (typically for
    // raw pointers), fall back to heap extraction, which keeps pointers and
    // pulls in the structs they point to. `check` then routes to the heap path
    // or, if that isn't viable, skips with the scalar reason.
    let extract_either = |idx: &CrateIndex, e: usize| match extract(idx, e) {
        Ok(u) => Ok(u),
        Err(scalar_skip) => {
            c2rust_equiv::extract_heap_composed(idx, e, summaries).map_err(|_| scalar_skip)
        }
    };
    let old_unit = match extract_either(old, o) {
        Ok(u) => u,
        Err(skip) => {
            return immediate(Status::Skipped {
                category: skip.category,
                reason: skip.detail,
            })
        }
    };
    let new_unit = match extract_either(new, n) {
        Ok(u) => u,
        Err(skip) => {
            return immediate(Status::Skipped {
                category: skip.category,
                reason: format!("rewritten version: {}", skip.detail),
            })
        }
    };
    let key = cache::key(&old_unit, &new_unit, opts);
    if let Some(hit) = cache.as_ref().and_then(|c| c.get(&key)) {
        return (hit.clone(), true);
    }
    let outcome = check(&old_unit, &new_unit, opts);
    if let Some(cache) = cache {
        cache.insert(key, &outcome);
    }
    (outcome, false)
}
