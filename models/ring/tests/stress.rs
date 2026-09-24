// SPDX-License-Identifier: AGPL-3.0-or-later
//! Non-loom smoke lane: the same source, real threads, big item counts.
//! This does not explore interleavings systematically (that is loom's job);
//! it exists so the twin also runs as ordinary code on real hardware.

#![cfg(not(loom))]

use std::future::Future;
use std::pin::pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::task::{Context, Poll, Waker};
use std::thread;

use dn_ring_model::{PushError, channel};

/// Minimal single-future executor: park the thread on `Pending`, let the
/// waker unpark it. Unpark-before-park is a token, so no lost wakeups at
/// this layer.
fn block_on<F: Future>(fut: F) -> F::Output {
    struct ThreadWaker(thread::Thread);
    impl std::task::Wake for ThreadWaker {
        fn wake(self: Arc<Self>) {
            self.0.unpark();
        }
    }

    let mut fut = pin!(fut);
    let waker = Waker::from(Arc::new(ThreadWaker(thread::current())));
    let mut cx = Context::from_waker(&waker);
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(v) => return v,
            Poll::Pending => thread::park(),
        }
    }
}

/// Under Miri every instruction is interpreted, and the lane runs the program under thirty-two
/// schedules, so the count is what decides whether that fits. Two thousand is two orders of
/// magnitude past the four- and eight-slot rings used below, which is what the paths here need:
/// the slot array wraps hundreds of times, the ring is full within the first few pushes, and the
/// close still lands while the consumer is draining.
#[cfg(miri)]
const ITEMS: u64 = 2_000;
#[cfg(not(miri))]
const ITEMS: u64 = 100_000;

/// Spin lane: raw try_push/try_pop under real contention, then close.
#[test]
fn spin_conservation_and_close() {
    let (tx, mut rx) = channel::<u64>(8);

    let producer = thread::spawn(move || {
        for i in 0..ITEMS {
            let mut v = i;
            loop {
                match tx.try_push(v) {
                    Ok(()) => break,
                    Err(PushError::Full(back)) => {
                        v = back;
                        thread::yield_now();
                    }
                    Err(PushError::Closed(_)) => panic!("receiver never closes"),
                }
            }
        }
        tx.close();
    });

    let mut expected = 0u64;
    loop {
        match rx.try_pop() {
            Some(v) => {
                assert_eq!(v, expected, "order preserved, exactly once");
                expected += 1;
            }
            None => {
                if rx.is_closed() {
                    // Close is set after the last push; one more pop settles
                    // any item published just before the close.
                    match rx.try_pop() {
                        Some(v) => {
                            assert_eq!(v, expected);
                            expected += 1;
                        }
                        None => break,
                    }
                } else {
                    thread::yield_now();
                }
            }
        }
    }
    producer.join().unwrap();
    assert_eq!(expected, ITEMS, "every item received exactly once");
}

/// Async lane: the send/recv futures (the check-register-recheck paths)
/// under real threads and a real parking executor.
#[test]
fn async_conservation_and_close() {
    let (tx, mut rx) = channel::<u64>(4);

    let producer = thread::spawn(move || {
        block_on(async move {
            for i in 0..ITEMS {
                tx.send(i).await.expect("receiver never closes");
            }
            tx.close();
        });
    });

    let received = block_on(async move {
        let mut n = 0u64;
        while let Some(v) = rx.recv().await {
            assert_eq!(v, n, "order preserved, exactly once");
            n += 1;
        }
        n
    });

    producer.join().unwrap();
    assert_eq!(received, ITEMS, "drained fully, then observed close");
}

/// Close from the receiver side unblocks a sender stuck on a full ring.
#[test]
fn receiver_close_releases_blocked_sender() {
    let (tx, rx) = channel::<u64>(1);
    tx.try_push(1).unwrap();

    let producer = thread::spawn(move || {
        block_on(async move {
            let err = tx
                .send(2)
                .await
                .expect_err("receiver closes without popping");
            assert_eq!(err, PushError::Closed(2));
        });
    });

    // Give the sender a chance to actually park before the close.
    thread::yield_now();
    rx.close();
    producer.join().unwrap();
}

/// A value that reports its own destruction and owns a heap allocation, so the
/// ring's `Drop` can be held to "each stored value is destroyed exactly once".
/// The allocation matters: destroying a slot that was already taken is
/// undefined behaviour, and a counter alone cannot see it — freeing the same
/// box twice is loud, and the Miri lane reads the same tests.
#[derive(Debug)]
struct Counted {
    drops: Arc<AtomicUsize>,
    owned: Box<u64>,
}

impl Counted {
    fn new(drops: &Arc<AtomicUsize>, value: u64) -> Counted {
        Counted {
            drops: drops.clone(),
            owned: Box::new(value),
        }
    }
}

impl Drop for Counted {
    fn drop(&mut self) {
        assert_ne!(
            *self.owned,
            u64::MAX,
            "a destroyed value was destroyed again"
        );
        *self.owned = u64::MAX;
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}

/// **Undrained items are destroyed once.** Dropping a ring that still holds
/// values must run each destructor exactly once: the slot walk in `Drop` reads
/// the encoded counters, and an index computed from the wrong one would destroy
/// a slot twice or leak it. Every other test in this crate stores integers,
/// whose destructor is a no-op and cannot show the difference.
#[test]
fn undrained_items_are_destroyed_exactly_once() {
    let drops = Arc::new(AtomicUsize::new(0));
    {
        let (tx, mut rx) = channel::<Counted>(4);
        for _ in 0..4 {
            tx.try_push(Counted::new(&drops, 1)).expect("capacity 4");
        }
        // One value leaves through the consumer and dies here; three stay in
        // the ring and must die with it.
        drop(rx.try_pop().expect("one item"));
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert!(rx.try_pop().is_some());
        assert_eq!(drops.load(Ordering::SeqCst), 2);
    }
    assert_eq!(
        drops.load(Ordering::SeqCst),
        4,
        "every value stored in the ring was destroyed exactly once"
    );
}

/// The same across the wrap of the slot array: pushes and pops keep cycling the
/// same four slots, so a `Drop` that walked the wrong range would show up here.
#[test]
fn destruction_survives_slot_reuse() {
    let drops = Arc::new(AtomicUsize::new(0));
    {
        let (tx, mut rx) = channel::<Counted>(2);
        // Four push/pop pairs walk the two slots twice round, so the counters
        // are well past the slot array by the time anything is left behind.
        for _ in 0..4 {
            tx.try_push(Counted::new(&drops, 2))
                .expect("the ring is empty here");
            drop(rx.try_pop().expect("an item to take"));
        }
        assert_eq!(drops.load(Ordering::SeqCst), 4);
        // Two values left in reused slots for the ring's own `Drop` to destroy.
        tx.try_push(Counted::new(&drops, 3)).expect("capacity 2");
        tx.try_push(Counted::new(&drops, 3)).expect("capacity 2");
    }
    assert_eq!(drops.load(Ordering::SeqCst), 6);
}
