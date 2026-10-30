//! THROWAWAY blocker-set / wall-combination analysis (remove before commit).
//!
//! For every function, collect the FULL set of walls blocking it (not just the
//! first), so we can target the wall whose removal flips the most functions.
//! Key output: for each wall class, how many functions have it as their SOLE
//! blocker (= direct flips if that one wall is cleared), vs how many merely
//! touch it (first-blocker surveys conflate these).
//!
//! Usage: cargo run --example dag -- <crate-dir> [i/n]   (machine lines; merge shards)

use std::collections::{BTreeMap, BTreeSet};

use c2rust_equiv::check::heap_diagnose;
use c2rust_equiv::{all_blockers, extract_heap_composed, CrateIndex};

fn main() {
    let root = std::env::args()
        .nth(1)
        .expect("usage: dag <crate-dir> [i/n]");
    let (si, sn) = match std::env::args().nth(2) {
        Some(s) => {
            let (i, n) = s.split_once('/').unwrap();
            (i.parse::<usize>().unwrap(), n.parse::<usize>().unwrap())
        }
        None => (0, 1),
    };
    let index = CrateIndex::load(std::path::Path::new(&root)).unwrap();
    let catalog = c2rust_equiv::compose::summary_catalog(&index, &index);

    let mut touch: BTreeMap<String, usize> = BTreeMap::new();
    let mut single: BTreeMap<String, usize> = BTreeMap::new();
    let mut sets: BTreeMap<String, usize> = BTreeMap::new();
    let (mut elig, mut total) = (0usize, 0usize);

    for (idx, e) in index.functions().enumerate() {
        if idx % sn != si {
            continue;
        }
        total += 1;
        let blockers = all_blockers(&index, e, &catalog);
        let mut cats: BTreeSet<String> = blockers.into_iter().map(|(c, _)| c).collect();
        if cats.is_empty() {
            // No extraction blocker: eligible unless a generate-phase wall remains.
            match extract_heap_composed(&index, e, &catalog) {
                Ok(unit) => match heap_diagnose(&unit) {
                    Ok(()) => {
                        elig += 1;
                        continue;
                    }
                    Err(_) => {
                        cats.insert("generate".to_owned());
                    }
                },
                Err(s) => {
                    cats.insert(s.category);
                }
            }
        }
        for c in &cats {
            *touch.entry(c.clone()).or_default() += 1;
        }
        if cats.len() == 1 {
            *single
                .entry(cats.iter().next().unwrap().clone())
                .or_default() += 1;
        }
        *sets
            .entry(cats.into_iter().collect::<Vec<_>>().join("+"))
            .or_default() += 1;
    }

    println!("ELIG\t{elig}\t{total}");
    for (c, n) in &touch {
        println!("TOUCH\t{c}\t{n}");
    }
    for (c, n) in &single {
        println!("SINGLE\t{c}\t{n}");
    }
    for (k, n) in &sets {
        println!("SET\t{k}\t{n}");
    }
}
