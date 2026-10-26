//! Check that rewritten Rust functions behave the same as the originals.
//!
//! [`check`] compares two versions of one function, each with its callee
//! closure ([`FnUnit`]). It first tries to prove equivalence with Kani, and
//! falls back to differential testing when Kani can't decide. [`extract`] and
//! [`CrateIndex`] build those units from a crate's source files.

pub mod cache;
pub mod check;
pub mod crate_index;
pub mod extract;
pub mod kani;
mod process;
pub mod report;
mod scalar;
mod scratch;
pub mod unit;

pub use check::{check, Method, Options, Outcome, Status};
pub use crate_index::CrateIndex;
pub use extract::extract;
pub use unit::{FnUnit, Skip};
