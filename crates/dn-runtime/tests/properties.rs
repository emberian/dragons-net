// SPDX-License-Identifier: AGPL-3.0-or-later
//! Properties over generated operation sequences.
//!
//! The unit tests state single cases, and loom explores interleavings of a fixed program. What
//! neither reaches is a long sequence of operations in an order nobody thought of, which is
//! where an allocator or a counter drifts from what its callers were promised. Each property
//! below is an invariant of the interface, checked against a model kept beside the real thing:
//! which token is live, how many permits are held, how many bytes went out. The model is
//! deliberately naive — a list and a counter — so that agreement means something.
// Not under Miri: proptest keeps its counterexamples in a file beside the test, and Miri runs
// with the filesystem isolated; interpreting hundreds of generated cases would also cost more
// than it tells. Miri's job here is the unsafe code under a few schedules, not case coverage.
#![cfg(all(not(loom), not(miri)))]

use dn_runtime::{ConnectionLimit, OutputCursor, Slab};
use proptest::prelude::*;
use std::collections::HashSet;

/// What a caller may ask of a slab, as generated data rather than as a written-out test.
#[derive(Clone, Copy, Debug)]
enum Op {
    /// Store a value.
    Insert(i64),
    /// Remove the n-th live entry, if there is one.
    RemoveLive(usize),
    /// Remove through a token whose entry is already gone.
    RemoveDead(usize),
    /// Read the n-th live entry.
    GetLive(usize),
    /// Read through a token whose entry is already gone.
    GetDead(usize),
}

fn ops() -> impl Strategy<Value = Vec<Op>> {
    // Removals and reads are generated as an index into what is live, so a sequence stays
    // meaningful however the allocator chooses slots.
    let op = prop_oneof![
        3 => any::<i64>().prop_map(Op::Insert),
        2 => any::<usize>().prop_map(Op::RemoveLive),
        1 => any::<usize>().prop_map(Op::RemoveDead),
        2 => any::<usize>().prop_map(Op::GetLive),
        2 => any::<usize>().prop_map(Op::GetDead),
    ];
    prop::collection::vec(op, 0..200)
}

proptest! {
    /// A token stops resolving the moment its entry is removed, and never resolves again,
    /// whatever the slab does with the slot afterwards. This is the property the whole design
    /// exists for: a late completion must not reach whoever holds the slot now.
    #[test]
    fn a_removed_token_never_resolves_again(capacity in 1usize..8, script in ops()) {
        let mut slab = Slab::new(capacity);
        let mut live: Vec<(dn_runtime::Token, i64)> = Vec::new();
        let mut dead: Vec<dn_runtime::Token> = Vec::new();
        for op in script {
            match op {
                Op::Insert(value) => {
                    let full = live.len() == capacity;
                    match slab.insert(value) {
                        Ok(token) => {
                            prop_assert!(!full, "inserted into a full slab");
                            prop_assert_ne!(token.index(), 0, "index 0 is the wakeup sentinel");
                            prop_assert!(token.index() <= capacity);
                            live.push((token, value));
                        }
                        Err(returned) => {
                            prop_assert!(full, "refused an insert with room to spare");
                            prop_assert_eq!(returned, value, "the value was not handed back");
                        }
                    }
                }
                Op::RemoveLive(n) if !live.is_empty() => {
                    let (token, value) = live.remove(n % live.len());
                    prop_assert_eq!(slab.remove(token), Some(value));
                    dead.push(token);
                }
                Op::GetLive(n) if !live.is_empty() => {
                    let (token, value) = live[n % live.len()];
                    prop_assert_eq!(slab.get(token), Some(&value));
                }
                Op::RemoveDead(n) if !dead.is_empty() => {
                    prop_assert_eq!(slab.remove(dead[n % dead.len()]), None);
                }
                Op::GetDead(n) if !dead.is_empty() => {
                    prop_assert_eq!(slab.get(dead[n % dead.len()]), None);
                }
                _ => {}
            }
            // Every token ever removed stays dead, not only the one just used, and through
            // both readers: `get_mut` carries its own copy of the generation check.
            for token in &dead {
                prop_assert_eq!(slab.get(*token), None, "a removed token resolved again");
                prop_assert!(slab.get_mut(*token).is_none(), "a removed token resolved for writing");
            }
            let names: HashSet<usize> = live.iter().map(|(token, _)| token.index()).collect();
            prop_assert_eq!(names.len(), live.len(), "two live entries share a slot");
        }
    }

    /// Admission stops exactly at the maximum — not one earlier, which refuses a caller with
    /// room, and not one later, which is the bug the limit exists to prevent — and the count it
    /// reports is what a caller can reconstruct from the outside: admissions minus releases.
    #[test]
    fn admission_counts_exactly_the_permits_held(maximum in 0usize..6,
                                                 script in prop::collection::vec((any::<bool>(), any::<usize>()), 0..80)) {
        let limit = ConnectionLimit::new(maximum);
        let mut held = Vec::new();
        let (mut admitted, mut released) = (0usize, 0usize);
        for (acquire, which) in script {
            if acquire {
                match limit.try_acquire() {
                    Some(permit) => {
                        prop_assert!(held.len() < maximum, "admitted past the maximum");
                        held.push(permit);
                        admitted += 1;
                    }
                    None => prop_assert_eq!(held.len(), maximum, "refused a caller with room"),
                }
            } else if !held.is_empty() {
                // Any held permit, not always the newest: the slot a permit gives back must not
                // depend on the order the permits were taken in.
                // Dropping the permit is what releases the slot.
                drop(held.remove(which % held.len()));
                released += 1;
            }
            prop_assert_eq!(limit.used(), admitted - released);
            prop_assert!(limit.used() <= limit.maximum());
        }
    }

    /// Reported sends move the cursor by exactly what was reported, an over-report is refused,
    /// and a refusal leaves the cursor where it was: the bytes that go out are the bytes that
    /// were given, in order, once each.
    #[test]
    fn a_cursor_sends_each_byte_once_and_in_order(bytes in prop::collection::vec(any::<u8>(), 0..64),
                                                  script in prop::collection::vec((0u8..3, any::<usize>()), 0..40)) {
        let mut cursor = OutputCursor::new(&bytes);
        let mut sent = 0usize;
        for (kind, value) in script {
            let left = bytes.len() - sent;
            // The interesting counts are the ones just past the remainder but still inside the
            // buffer: a check written against the buffer rather than the remainder accepts
            // exactly those, and a generator that only produces fitting or absurd counts
            // never shows it.
            let count = match kind {
                0 => value % (left + 1),
                1 => left + 1 + value % (bytes.len() - left + 1),
                _ => value,
            };
            let before = cursor.remaining();
            if cursor.complete(count).is_ok() {
                sent += count;
            } else {
                prop_assert!(count > bytes.len() - sent, "refused a count that fits");
                prop_assert_eq!(cursor.remaining(), before, "a refusal moved the cursor");
            }
            prop_assert_eq!(cursor.sent(), sent);
            prop_assert_eq!(cursor.remaining(), &bytes[sent..]);
            prop_assert_eq!(cursor.is_complete(), sent == bytes.len());
        }
    }
}
