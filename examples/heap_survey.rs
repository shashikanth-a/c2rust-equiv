//! Survey the heap-path eligibility of every function in a crate, bucketing the
//! precise reason each out-of-scope function is rejected (from
//! `check::heap_diagnose`). Self-checks the crate against itself, since
//! eligibility depends only on structure, not on any rewrite difference.
//!
//! Usage: `cargo run --example heap_survey -- <crate-dir>`

use std::collections::BTreeMap;

use c2rust_equiv::check::heap_diagnose;
use c2rust_equiv::{extract_heap_composed, CrateIndex};

fn bucket(reason: &str) -> String {
    // Collapse a detailed reason into a coarse-then-fine key:
    //   "signature: ..." / "not-heap" / "body: .. (cat)" / "generate: .. field .. : .."
    if let Some(rest) = reason.strip_prefix("generate:") {
        // Keep up to the ": <detail>" so field shapes group together.
        let detail = rest.rsplit(':').next().unwrap_or(rest).trim();
        return format!("generate: {detail}");
    }
    if let Some(rest) = reason.strip_prefix("body:") {
        // The "(category)" suffix is the useful grouping key.
        if let Some(open) = rest.rfind('(') {
            return format!("body: {}", rest[open..].trim_matches(['(', ')', ' ']));
        }
        return "body".to_owned();
    }
    if reason.starts_with("signature:") {
        return "signature".to_owned();
    }
    reason.to_owned()
}

fn main() {
    let root = std::env::args()
        .nth(1)
        .expect("usage: heap_survey <crate-dir> [i/n]");
    // Optional shard `i/n`: process only every n-th function starting at i, so
    // a project's survey can be split across n parallel worker processes and
    // their counts summed. The crate is still loaded whole (needed for the
    // catalog and cross-references); only the per-function work is partitioned.
    let (shard_i, shard_n) = match std::env::args().nth(2) {
        Some(s) => {
            let (i, n) = s.split_once('/').expect("shard must be i/n");
            (i.parse::<usize>().unwrap(), n.parse::<usize>().unwrap())
        }
        None => (0, 1),
    };
    let index = CrateIndex::load(std::path::Path::new(&root)).expect("load crate");
    // Compose against itself: the summary catalog of unchanged callees.
    let catalog = c2rust_equiv::compose::summary_catalog(&index, &index);

    let mut eligible = 0usize;
    let mut total = 0usize;
    let mut buckets: BTreeMap<String, usize> = BTreeMap::new();
    let mut examples: BTreeMap<String, Vec<String>> = BTreeMap::new();

    for (idx, e) in index.functions().enumerate() {
        if idx % shard_n != shard_i {
            continue; // handled by another shard
        }
        total += 1;
        let short = index.id(e).rsplit("::").next().unwrap_or("").to_owned();
        let reason = match extract_heap_composed(&index, e, &catalog) {
            Err(skip) if std::env::var("DETAIL").is_ok() => {
                format!("extract: {} :: {}", skip.category, skip.detail)
            }
            Err(skip) => format!("extract: {}", skip.category),
            Ok(unit) => match heap_diagnose(&unit) {
                Ok(()) => {
                    eligible += 1;
                    continue;
                }
                Err(r) => r,
            },
        };
        let key = bucket(&reason);
        *buckets.entry(key.clone()).or_default() += 1;
        let ex = examples.entry(key).or_default();
        if ex.len() < 3 {
            ex.push(short);
        }
    }

    eprintln!("eligible {eligible}/{total}");
    let mut sorted: Vec<_> = buckets.into_iter().collect();
    sorted.sort_by_key(|x| std::cmp::Reverse(x.1));
    for (k, n) in sorted {
        let ex = examples.get(&k).map(|v| v.join(", ")).unwrap_or_default();
        // Tab-delimited (count, key, examples) so a shard runner can sum counts
        // per key cleanly; a plain run is still readable.
        eprintln!("{n}\t{k}\t{ex}");
    }
}
