// SPDX-License-Identifier: AGPL-3.0-or-later
//! Sequential behaviour of the ring against a queue everyone already trusts.
//!
//! Loom explores how two threads interleave over a fixed short program, and the stress tests
//! push a hundred thousand items through in one order. What neither asks is whether a long
//! sequence of pushes, pops and a close, in an order nobody chose by hand, leaves the ring
//! behaving like a bounded `VecDeque` — and whether every value put in is destroyed exactly
//! once, including the values still inside when the ring is dropped.
//!
//! What this cannot reach: a close that lands between a producer writing a slot and publishing
//! it. That branch needs two threads, and loom owns it.
//!
//! A counterexample is written to `properties.proptest-regressions` beside this file; commit it,
//! so the case keeps running after the generator has moved on.
// Not under Miri: proptest keeps its counterexamples in a file beside the test, and Miri runs
// with the filesystem isolated; interpreting hundreds of generated cases would also cost more
// than it tells. Miri's job here is the unsafe code under a few schedules, not case coverage.
#![cfg(all(not(loom), not(miri)))]

use dn_ring_model::{PushError, channel};
use proptest::prelude::*;
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

/// A payload that records its own destruction: a slot destroyed twice, or never, shows up as a
/// difference between what went into the ring and what was destroyed.
#[derive(Debug)]
struct Counted {
    value: u32,
    dropped: Arc<Mutex<Vec<u32>>>,
}

impl Drop for Counted {
    fn drop(&mut self) {
        self.dropped
            .lock()
            .expect("the lock is never poisoned")
            .push(self.value);
    }
}

#[derive(Clone, Copy, Debug)]
enum Op {
    Push(u32),
    Pop,
    Close,
}

proptest! {
    /// The ring is a bounded queue that can be closed: it returns what was put in, in order,
    /// refuses a push exactly when it is full, refuses every push once it is closed and hands
    /// the value back, and destroys everything exactly once.
    #[test]
    fn the_ring_behaves_like_a_bounded_queue(
        // Small capacities: the wrap-around and the full-queue branch are unreachable within a
        // bounded sequence when the capacity is large.
        capacity in prop::sample::select(vec![1usize, 2, 4, 8]),
        drain in any::<bool>(),
        script in prop::collection::vec(
            prop_oneof![
                6 => any::<u32>().prop_map(Op::Push),
                3 => Just(Op::Pop),
                1 => Just(Op::Close),
            ],
            0..400)) {
        let dropped = Arc::new(Mutex::new(Vec::new()));
        // Every payload that is constructed, accepted or refused: whoever ends up owning it,
        // it has to be destroyed exactly once.
        let mut created: Vec<u32> = Vec::new();
        let (sender, mut receiver) = channel::<Counted>(capacity);
        let mut model: VecDeque<u32> = VecDeque::new();
        let mut closed = false;
        {
            // What was taken out lives here, so that what the ring destroyed and what this test
            // destroyed are not counted together.
            let mut taken: Vec<Counted> = Vec::new();
            for op in script {
                match op {
                    Op::Push(value) => {
                        let item = Counted { value, dropped: Arc::clone(&dropped) };
                        created.push(value);
                        match sender.try_push(item) {
                            Ok(()) => {
                                prop_assert!(!closed, "accepted a push after close");
                                prop_assert!(model.len() < capacity, "accepted a push into a full ring");
                                model.push_back(value);
                            }
                            Err(PushError::Full(returned)) => {
                                prop_assert!(!closed, "reported full for a closed ring");
                                prop_assert_eq!(model.len(), capacity, "refused a push with room");
                                prop_assert_eq!(returned.value, value, "the value was not handed back");
                            }
                            Err(PushError::Closed(returned)) => {
                                prop_assert!(closed, "reported closed before anyone closed it");
                                prop_assert_eq!(returned.value, value, "the value was not handed back");
                            }
                        }
                    }
                    Op::Pop => {
                        let item = receiver.try_pop();
                        prop_assert_eq!(item.as_ref().map(|held| held.value), model.pop_front());
                        taken.extend(item);
                    }
                    Op::Close => {
                        sender.close();
                        closed = true;
                        prop_assert!(sender.is_closed());
                        prop_assert!(receiver.is_closed());
                    }
                }
            }
            if drain {
                // What the ring still holds comes out in order, and then it is empty.
                while let Some(expected) = model.pop_front() {
                    let item = receiver.try_pop();
                    prop_assert_eq!(item.as_ref().map(|held| held.value), Some(expected));
                    taken.extend(item);
                }
                prop_assert!(receiver.try_pop().is_none());
            }
            // Otherwise the endpoints go out of scope with items still inside, which is the case
            // where the ring itself has to destroy what it holds.
        }
        drop(sender);
        drop(receiver);
        let mut destroyed = dropped.lock().expect("the lock is never poisoned").clone();
        destroyed.sort_unstable();
        created.sort_unstable();
        prop_assert_eq!(destroyed, created, "every value made is destroyed exactly once");
    }
}
