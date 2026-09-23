// SPDX-License-Identifier: AGPL-3.0-or-later
//! Executable model of the io_uring provided-buffer **borrow↔recycle
//! cross-thread handoff**: a worker reads a slice the kernel lent to a
//! connection, the shard hands that buffer back, and the kernel immediately
//! re-lends it to another connection. Reading the slice after the hand-back is
//! a cross-connection disclosure.
//!
//! The lease lives here so that it can be mutated and re-checked; the schedules
//! live in `tests/loom.rs`, exercised under `--cfg loom`. The historical
//! reactor this models is `migration/dataplane/host/src/uring.rs`.
#![deny(unsafe_op_in_unsafe_fn)]

mod sync;

use sync::{AtomicU32, Ordering};

/// The per-connection buffer lease: a buffer id, or nothing once it has been
/// handed back. `0` is the empty lease, matching the reactor's `Option<u16>`.
#[derive(Debug)]
pub struct Lease(AtomicU32);

impl Lease {
    /// A lease holding buffer `bid` (which must not be `0`).
    #[must_use]
    pub fn held(bid: u32) -> Lease {
        debug_assert_ne!(bid, 0, "0 is the empty lease");
        Lease(AtomicU32::new(bid))
    }

    /// Hand the buffer back, returning its id to the caller that won the race.
    ///
    /// Two paths can reach the hand-back for one connection — staging the
    /// response and tearing the connection down — so this has to be the point
    /// where exactly one of them takes the buffer.
    pub fn take(&self) -> Option<u32> {
        match self.0.swap(0, Ordering::AcqRel) {
            0 => None,
            bid => Some(bid),
        }
    }

    /// `true` while the buffer is still borrowed.
    #[must_use]
    pub fn is_held(&self) -> bool {
        self.0.load(Ordering::Acquire) != 0
    }
}
