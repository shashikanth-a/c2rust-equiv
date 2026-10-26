//! JSON and Markdown reports.

use std::collections::BTreeMap;
use std::fmt::Write;

use serde::{Deserialize, Serialize};

use crate::check::{Method, Outcome, Status};

#[derive(Debug, Serialize, Deserialize)]
pub struct Report {
    pub tool_version: String,
    pub options: String,
    pub summary: Summary,
    pub functions: Vec<FunctionReport>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct FunctionReport {
    pub id: String,
    pub label: String,
    pub cached: bool,
    #[serde(flatten)]
    pub outcome: Outcome,
}

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct Summary {
    /// Functions in the original crate.
    pub total_functions: usize,
    /// Of those, how many are in scope for this version.
    pub eligible_functions: usize,
    pub checked: usize,
    pub proved: usize,
    pub counterexamples: usize,
    pub counterexamples_by_kani: usize,
    pub tested: usize,
    pub skipped: usize,
    pub skipped_by_category: BTreeMap<String, usize>,
    pub errors: usize,
    pub cache_hits: usize,
    /// Per-function times, excluding cache hits.
    pub median_ms: Option<u64>,
    pub p95_ms: Option<u64>,
}

impl Report {
    pub fn new(
        options: String,
        total_functions: usize,
        eligible_functions: usize,
        functions: Vec<FunctionReport>,
    ) -> Self {
        let mut s = Summary {
            total_functions,
            eligible_functions,
            checked: functions.len(),
            ..Default::default()
        };
        let mut times = Vec::new();
        for f in &functions {
            if f.cached {
                s.cache_hits += 1;
            } else if !matches!(f.outcome.status, Status::Skipped { .. }) {
                times.push(f.outcome.total_ms);
            }
            match &f.outcome.status {
                Status::Proved { .. } => s.proved += 1,
                Status::Counterexample { found_by, .. } => {
                    s.counterexamples += 1;
                    if *found_by == Method::Kani {
                        s.counterexamples_by_kani += 1;
                    }
                }
                Status::Tested { .. } => s.tested += 1,
                Status::Skipped { category, .. } => {
                    s.skipped += 1;
                    *s.skipped_by_category.entry(category.clone()).or_default() += 1;
                }
                Status::Error { .. } => s.errors += 1,
            }
        }
        times.sort_unstable();
        let percentile = |p: f64| {
            (!times.is_empty()).then(|| times[((times.len() - 1) as f64 * p).round() as usize])
        };
        s.median_ms = percentile(0.5);
        s.p95_ms = percentile(0.95);
        Self {
            tool_version: env!("CARGO_PKG_VERSION").to_owned(),
            options,
            summary: s,
            functions,
        }
    }

    /// 0 if every checked function was proved or tested (or skipped), 1 if any
    /// has a counterexample, 2 if any check failed to run.
    pub fn exit_code(&self) -> u8 {
        if self.summary.counterexamples > 0 {
            1
        } else if self.summary.errors > 0 {
            2
        } else {
            0
        }
    }

    pub fn markdown(&self) -> String {
        let s = &self.summary;
        let mut out = String::new();
        let pct = |n: usize| {
            if s.total_functions == 0 {
                0.0
            } else {
                100.0 * n as f64 / s.total_functions as f64
            }
        };
        let ms = |t: Option<u64>| t.map_or("-".to_owned(), |t| format!("{t} ms"));
        let _ = writeln!(out, "# Equivalence report\n");
        let _ = writeln!(
            out,
            "Eligible: {} of {} functions ({:.1}%). Checked: {}.\n",
            s.eligible_functions,
            s.total_functions,
            pct(s.eligible_functions),
            s.checked
        );
        let _ = writeln!(out, "| Result | Count |\n|---|---|");
        let _ = writeln!(out, "| proved (bounded) | {} |", s.proved);
        let _ = writeln!(
            out,
            "| counterexample | {} ({} found by Kani) |",
            s.counterexamples, s.counterexamples_by_kani
        );
        let _ = writeln!(
            out,
            "| tested only (no difference found; not a proof) | {} |",
            s.tested
        );
        let _ = writeln!(out, "| skipped | {} |", s.skipped);
        let _ = writeln!(out, "| error | {} |", s.errors);
        let _ = writeln!(
            out,
            "\nTime per function: median {}, p95 {}. Cache hits: {}.",
            ms(s.median_ms),
            ms(s.p95_ms),
            s.cache_hits
        );
        if !s.skipped_by_category.is_empty() {
            let _ = writeln!(
                out,
                "\n## Skipped, by reason\n\n| Reason | Count |\n|---|---|"
            );
            for (category, n) in &s.skipped_by_category {
                let _ = writeln!(out, "| {category} | {n} |");
            }
        }
        let _ = writeln!(
            out,
            "\n## Functions\n\n| Function | Result | Time |\n|---|---|---|"
        );
        for f in &self.functions {
            let time = if f.cached {
                "cached".to_owned()
            } else {
                format!("{} ms", f.outcome.total_ms)
            };
            let _ = writeln!(
                out,
                "| `{}` | {} | {} |",
                f.id,
                f.label.replace('|', "\\|"),
                time
            );
        }
        out
    }
}
