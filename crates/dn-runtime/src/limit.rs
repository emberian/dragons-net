use crate::sync::{AtomicUsize, Ordering};

/// A process-wide admission limit. Share one instance across all reactor
/// shards: the bound is on the counter, so a per-shard copy would multiply it.
#[derive(Debug)]
pub struct ConnectionLimit {
    maximum: usize,
    used: AtomicUsize,
}

impl ConnectionLimit {
    /// A limit admitting at most `maximum` concurrent holders.
    #[cfg(not(loom))]
    #[must_use]
    pub const fn new(maximum: usize) -> Self {
        Self {
            maximum,
            used: AtomicUsize::new(0),
        }
    }

    /// A limit admitting at most `maximum` concurrent holders. Not `const`
    /// under `--cfg loom`: the instrumented atomics have no const constructor.
    #[cfg(loom)]
    #[must_use]
    pub fn new(maximum: usize) -> Self {
        Self {
            maximum,
            used: AtomicUsize::new(0),
        }
    }

    /// Take one admission slot, or `None` when the limit is reached.
    ///
    /// The successful update is `AcqRel` and the release in [`Permit::drop`] is
    /// `Release`, so whatever the previous holder wrote before releasing its
    /// slot is visible to whoever takes that slot next. Under `Relaxed` the
    /// count would still be correct, but the data a permit stands for would not
    /// be ordered between holders, which `tests/loom.rs` checks.
    #[must_use = "dropping the permit immediately releases the slot it took"]
    pub fn try_acquire(&self) -> Option<Permit<'_>> {
        self.used
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |used| {
                (used < self.maximum).then(|| used + 1)
            })
            .ok()
            .map(|_| Permit { limit: self })
    }

    /// How many slots are currently held.
    #[must_use]
    pub fn used(&self) -> usize {
        self.used.load(Ordering::Acquire)
    }

    /// The limit this gate was built with.
    #[must_use]
    pub const fn maximum(&self) -> usize {
        self.maximum
    }
}

/// An admission slot, released when dropped. Releasing is tied to ownership:
/// the permit cannot be cloned, and dropping it is the only way to give the
/// slot back.
#[derive(Debug)]
#[must_use = "the slot is released as soon as the permit is dropped"]
pub struct Permit<'a> {
    limit: &'a ConnectionLimit,
}

impl Drop for Permit<'_> {
    fn drop(&mut self) {
        let previous = self.limit.used.fetch_sub(1, Ordering::Release);
        debug_assert_ne!(previous, 0, "a permit released a slot that was not held");
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    #[test]
    fn bounded_and_released_on_drop() {
        let gate = ConnectionLimit::new(1);
        let permit = gate.try_acquire().unwrap();
        assert!(gate.try_acquire().is_none());
        drop(permit);
        assert!(gate.try_acquire().is_some());
        assert_eq!(gate.used(), 0);
        assert!(ConnectionLimit::new(0).try_acquire().is_none());
    }

    #[test]
    fn shared_limit_cannot_multiply_with_shards() {
        let gate = ConnectionLimit::new(3);
        let barrier = std::sync::Barrier::new(16);
        // The threads record what they saw instead of asserting inside the
        // barrier: an assertion between two `wait` calls would leave the other
        // fifteen threads blocked forever, so a broken gate would hang the run
        // instead of failing it.
        let peak = AtomicUsize::new(0);
        let held_at_once = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..16 {
                scope.spawn(|| {
                    let held = gate.try_acquire();
                    if held.is_some() {
                        held_at_once.fetch_add(1, Ordering::AcqRel);
                    }
                    barrier.wait();
                    peak.fetch_max(gate.used(), Ordering::AcqRel);
                    barrier.wait();
                    drop(held);
                });
            }
        });
        assert_eq!(
            peak.load(Ordering::Acquire),
            3,
            "the shared limit admitted a different number"
        );
        assert_eq!(
            held_at_once.load(Ordering::Acquire),
            3,
            "exactly three of the sixteen shards got a permit"
        );
        assert_eq!(gate.used(), 0);
    }
}
