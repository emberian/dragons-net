//! Host-side scaffolding, tested but not connected to the Lean proofs.
//!
//! No protocol decisions belong here. Native kernel linkage and OS reactors
//! are separate adapters; the current crate provides bounded ownership tools.

mod limit;
mod output;
mod slab;

pub use limit::{ConnectionLimit, Permit};
pub use output::{OutputCursor, OverCompletion};
pub use slab::{Slab, Token};
