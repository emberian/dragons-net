//! Atomics, switched between `std` and `loom`.
//!
//! Under `--cfg loom` the atomics are the loom-instrumented ones, so the model
//! checker explores every interleaving and every C11-permitted read. Normal
//! builds resolve the same names to `std`.

#[cfg(loom)]
pub(crate) use loom::sync::atomic::{AtomicU32, Ordering};

#[cfg(not(loom))]
pub(crate) use std::sync::atomic::{AtomicU32, Ordering};
