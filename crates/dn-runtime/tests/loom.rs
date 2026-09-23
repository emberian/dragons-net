// SPDX-License-Identifier: AGPL-3.0-or-later
//! Schedule exploration of the shipped admission gate under loom.
//!
//! Run with:
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p dn-runtime --test loom
//! ```
//!
//! Unlike the models in `models/`, these tests drive `dn_runtime` itself: the
//! atomics inside [`ConnectionLimit`] are the loom-instrumented ones under this
//! cfg, so what is explored is the code the host links, not a transcription of
//! it. The verdicts come from a counter outside the gate — how many holders are
//! live at once — rather than from the gate's own bookkeeping.

#![cfg(loom)]

use dn_runtime::ConnectionLimit;
use loom::sync::Arc;
use loom::sync::atomic::{AtomicUsize, Ordering};
use loom::thread;

/// The bound holds under every interleaving: with a limit of one and two
/// threads contending, the two holders are never live at the same time.
#[test]
fn limit_of_one_is_never_exceeded() {
    loom::model(|| {
        let gate = Arc::new(ConnectionLimit::new(1));
        // Live holders, counted outside the gate. The gate's own `used()` is
        // what we are testing, so it cannot be the witness.
        let live = Arc::new(AtomicUsize::new(0));
        let peak = Arc::new(AtomicUsize::new(0));

        let contender = {
            let gate = gate.clone();
            let live = live.clone();
            let peak = peak.clone();
            thread::spawn(move || {
                if let Some(permit) = gate.try_acquire() {
                    let now = live.fetch_add(1, Ordering::AcqRel) + 1;
                    peak.fetch_max(now, Ordering::AcqRel);
                    live.fetch_sub(1, Ordering::AcqRel);
                    drop(permit);
                }
            })
        };

        if let Some(permit) = gate.try_acquire() {
            let now = live.fetch_add(1, Ordering::AcqRel) + 1;
            peak.fetch_max(now, Ordering::AcqRel);
            live.fetch_sub(1, Ordering::AcqRel);
            drop(permit);
        }
        contender.join().unwrap();

        assert!(
            peak.load(Ordering::Acquire) <= 1,
            "two holders were live at once under a limit of one"
        );
        assert_eq!(gate.used(), 0, "every permit released its slot");
    });
}

/// **A released slot carries the previous holder's writes.** The two values
/// below are written only while holding the permit, with relaxed accesses of
/// their own: the ordering has to come from the gate. The holder that sees
/// itself as the second one must therefore see what the first holder left. With
/// the gate's `Acquire`/`Release` pair it does; with both sides relaxed loom
/// finds the execution where it reads the stale value.
#[test]
fn a_released_slot_carries_the_previous_holders_writes() {
    loom::model(|| {
        let gate = Arc::new(ConnectionLimit::new(1));
        // Guarded by the permit, so relaxed is all these need — if the gate
        // orders the holders at all.
        let holders = Arc::new(AtomicUsize::new(0));
        let payload = Arc::new(AtomicUsize::new(0));

        let hold = |gate: &Arc<ConnectionLimit>,
                    holders: &Arc<AtomicUsize>,
                    payload: &Arc<AtomicUsize>,
                    id: usize| {
            if let Some(permit) = gate.try_acquire() {
                let before = holders.load(Ordering::Relaxed);
                holders.store(before + 1, Ordering::Relaxed);
                let seen = payload.load(Ordering::Relaxed);
                payload.store(id, Ordering::Relaxed);
                drop(permit);
                if before == 1 {
                    assert_ne!(
                        seen, 0,
                        "the second holder did not see the first holder's write"
                    );
                }
            }
        };

        let contender = {
            let gate = gate.clone();
            let holders = holders.clone();
            let payload = payload.clone();
            thread::spawn(move || hold(&gate, &holders, &payload, 1))
        };
        hold(&gate, &holders, &payload, 2);
        contender.join().unwrap();

        assert_eq!(gate.used(), 0, "every permit released its slot");
    });
}

/// Every slot comes back: after a full round of acquires and releases the gate
/// admits as many holders as it started with.
#[test]
fn slots_are_returned_after_contention() {
    loom::model(|| {
        let gate = Arc::new(ConnectionLimit::new(2));
        let contender = {
            let gate = gate.clone();
            thread::spawn(move || {
                let permit = gate.try_acquire();
                drop(permit);
            })
        };
        let permit = gate.try_acquire();
        drop(permit);
        contender.join().unwrap();

        assert_eq!(gate.used(), 0);
        let a = gate.try_acquire();
        let b = gate.try_acquire();
        assert!(a.is_some() && b.is_some(), "both slots are available again");
        assert!(gate.try_acquire().is_none(), "and no third one is");
    });
}
