/// Completion identity. Fields are private so callers cannot manufacture tokens.
/// Tokens belong to one slab; adapters must not route them between shards/slabs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    index: usize,
    generation: u64,
}

struct Slot<T> {
    generation: u64,
    value: Option<T>,
}

/// Fixed-capacity table. Insert/remove allocate nothing after construction.
/// Slot generations reject late completions after close and slot reuse.
pub struct Slab<T> {
    slots: Vec<Slot<T>>,
    free: Vec<usize>,
}

impl<T> Slab<T> {
    pub fn new(capacity: usize) -> Self {
        Self {
            slots: (0..capacity)
                .map(|_| Slot {
                    generation: 0,
                    value: None,
                })
                .collect(),
            free: (0..capacity).rev().collect(),
        }
    }
    pub fn insert(&mut self, value: T) -> Result<Token, T> {
        let Some(index) = self.free.pop() else {
            return Err(value);
        };
        let slot = &mut self.slots[index];
        slot.value = Some(value);
        Ok(Token {
            index,
            generation: slot.generation,
        })
    }
    pub fn get(&self, token: Token) -> Option<&T> {
        let slot = self.slots.get(token.index)?;
        (slot.generation == token.generation)
            .then_some(slot.value.as_ref())
            .flatten()
    }
    pub fn get_mut(&mut self, token: Token) -> Option<&mut T> {
        let slot = self.slots.get_mut(token.index)?;
        if slot.generation != token.generation {
            return None;
        }
        slot.value.as_mut()
    }
    pub fn remove(&mut self, token: Token) -> Option<T> {
        let slot = self.slots.get_mut(token.index)?;
        if slot.generation != token.generation {
            return None;
        }
        let value = slot.value.take()?;
        // Exhaustion retires the slot permanently; wrapping would admit an old token.
        if let Some(next) = slot.generation.checked_add(1) {
            slot.generation = next;
            self.free.push(token.index);
        }
        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn stale_completion_cannot_touch_reused_slot() {
        let mut slab = Slab::new(1);
        let old = slab.insert(10).unwrap();
        assert_eq!(slab.insert(20), Err(20));
        assert_eq!(slab.remove(old), Some(10));
        let new = slab.insert(30).unwrap();
        assert_ne!(old, new);
        assert_eq!(slab.get(old), None);
        assert_eq!(slab.get_mut(old), None);
        assert_eq!(slab.remove(old), None);
        assert_eq!(slab.get(new), Some(&30));
        assert_eq!(slab.remove(new), Some(30));
        assert_eq!(slab.remove(new), None);
    }
    #[test]
    fn generation_exhaustion_retires_slot() {
        let mut slab = Slab::new(1);
        slab.slots[0].generation = u64::MAX;
        let token = slab.insert(1).unwrap();
        assert_eq!(slab.remove(token), Some(1));
        assert_eq!(slab.insert(2), Err(2));
        assert_eq!(slab.get(token), None);
    }
}
