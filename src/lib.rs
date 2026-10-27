//! Check that rewritten Rust functions behave the same as the originals.
//!
//! [`check`] compares two versions of one function, each with its callee
//! closure ([`FnUnit`]). It first tries to prove equivalence with Kani, and
//! falls back to differential testing when Kani can't decide. [`extract`] and
//! [`CrateIndex`] build those units from a crate's source files.

mod allocmodel;
pub mod cache;
pub mod check;
pub mod crate_index;
pub mod extract;
pub mod heapgen;
pub mod kani;
mod process;
pub mod report;
mod scalar;
mod scratch;
mod strmodel;
pub mod taggedunion;
mod varmodel;
pub mod unit;

pub use check::{check, heap_diagnose, heap_eligible, Method, Options, Outcome, Status};
pub use crate_index::CrateIndex;
pub use extract::{extract, extract_heap, extract_unvalidated};
pub use unit::{FnUnit, Skip};
