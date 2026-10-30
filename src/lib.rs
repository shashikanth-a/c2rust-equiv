//! Check that rewritten Rust functions behave the same as the originals.
//!
//! [`check`] compares two versions of one function, each with its callee
//! closure ([`FnUnit`]). It first tries to prove equivalence with Kani, and
//! falls back to differential testing when Kani can't decide. [`extract`] and
//! [`CrateIndex`] build those units from a crate's source files.

mod allocmodel;
pub mod cache;
pub mod check;
pub mod compose;
pub mod crate_index;
mod errormodel;
pub mod extract;
mod globalaccessmodel;
pub mod heapgen;
mod indirectmodel;
pub mod kani;
mod modref;
mod mutexmodel;
pub mod peg;
mod process;
pub mod report;
mod scalar;
mod scratch;
mod strmodel;
mod summary;
pub mod taggedunion;
pub mod unit;
mod varmodel;

pub use check::{check, heap_diagnose, heap_eligible, Method, Options, Outcome, Status};
pub use crate_index::CrateIndex;
pub use extract::{
    all_blockers, extract, extract_heap, extract_heap_composed, extract_unvalidated,
};
pub use unit::{FnUnit, Skip};
