use std::sync::atomic::{AtomicUsize, Ordering};

/// Share one instance across all reactor shards for a process-wide limit.
pub struct ConnectionLimit {
    maximum: usize,
    used: AtomicUsize,
}

impl ConnectionLimit {
    pub const fn new(maximum: usize) -> Self {
        Self {
            maximum,
            used: AtomicUsize::new(0),
        }
    }

    pub fn try_acquire(&self) -> Option<Permit<'_>> {
        self.used
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |used| {
                (used < self.maximum).then(|| used + 1)
            })
            .ok()
            .map(|_| Permit { limit: self })
    }

    pub fn used(&self) -> usize {
        self.used.load(Ordering::Relaxed)
    }
}

/// Releasing admission is tied to ownership; a permit cannot be cloned.
pub struct Permit<'a> {
    limit: &'a ConnectionLimit,
}

impl Drop for Permit<'_> {
    fn drop(&mut self) {
        self.limit.used.fetch_sub(1, Ordering::Relaxed);
    }
}

#[cfg(test)]
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
        std::thread::scope(|scope| {
            for _ in 0..16 {
                scope.spawn(|| {
                    let held = gate.try_acquire();
                    barrier.wait();
                    assert_eq!(gate.used(), 3);
                    barrier.wait();
                    drop(held);
                });
            }
        });
        assert_eq!(gate.used(), 0);
    }
}
