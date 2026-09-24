// SPDX-License-Identifier: AGPL-3.0-or-later
//! Twin (executable model) of the io_uring zero-copy **SplitSend
//! writev↔recycle** handoff — the new `DRORB_SPAN=15` reactor path
//! (`stage_split_response` / `split_send_sqe` / `on_split_send` in
//! `migration/dataplane/host/src/uring.rs`).
//!
//! The zero-copy body is NEVER copied into an output buffer: the response is a
//! `writev` gather of the small head plus the borrowed request body, sliced
//! straight from the still-held buf_ring lease slot (`br.slice(body_bid, ...)`).
//! The lease is held across the send (and across every short-write re-arm) and
//! recycled EXACTLY ONCE, only once the writev has fully settled. Recycle the
//! slot while a writev is still gathering it and the kernel re-lends the slot to
//! another connection and overwrites the bytes mid-send — a cross-connection
//! data disclosure, the same class as the gap-F borrow↔recycle corner.
//!
//! The model itself lives in `tests/loom.rs`, exercised under `--cfg loom` for
//! schedule exploration. This crate stands alone
//! and separate from `dataplane`: the dataplane package's `build.rs` links the
//! Lean runtime (`libleanshared`) into every target, and that runtime breaks
//! loom's unwind-based panic capture inside its stackful coroutines — the same
//! reason `ring-twin`, `wake-twin`, and `borrow-recycle-twin` are their own
//! crates.
//!
//! See `tests/loom.rs` for the model, the real-handoff correspondence, and the
//! explicit statement of what it covers versus the deployed `uring.rs`.
#![deny(unsafe_op_in_unsafe_fn)]
