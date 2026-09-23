// SPDX-License-Identifier: AGPL-3.0-or-later
/// Completion identity. Fields are private so callers cannot manufacture tokens.
/// Tokens belong to one slab; adapters must not route them between shards/slabs.
///
/// Index 0 is never handed out: a completion whose user data is zero is either
/// an unset field or this reactor's own wakeup, never a live operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Token {
    index: usize,
    generation: u64,
}

impl Token {
    /// The slot this token names. Always nonzero.
    #[must_use]
    pub const fn index(&self) -> usize {
        self.index
    }

    /// The generation the slot had when the token was issued.
    #[must_use]
    pub const fn generation(&self) -> u64 {
        self.generation
    }
}

#[derive(Debug)]
struct Slot<T> {
    generation: u64,
    value: Option<T>,
}

/// Fixed-capacity table. Insert/remove allocate nothing after construction.
/// Slot generations reject late completions after close and slot reuse.
///
/// Where this differs from the Lean model of the same structure
/// (`DN.Dataplane.Io.Slab`), and why: this table has a fixed capacity and hands
/// out the most recently freed slot, while the model grows without bound and
/// takes the lowest free index. Neither difference is observable through a
/// token — both reserve index 0, both bump the slot's generation on removal,
/// and both reject a token whose generation no longer matches — but the model
/// is not a description of this allocator's choices, and a refinement proof
/// would have to start by reconciling them. The generation is a `u64` here and
/// a `Nat` there; a slot is retired when incrementing would overflow, which the
/// model does not represent at all.
#[derive(Debug)]
pub struct Slab<T> {
    slots: Vec<Slot<T>>,
    free: Vec<usize>,
}

impl<T> Slab<T> {
    /// A slab with room for `capacity` live entries.
    ///
    /// Slot 0 exists but is never allocated, so no token ever names it.
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        Self {
            slots: (0..=capacity)
                .map(|_| Slot {
                    generation: 0,
                    value: None,
                })
                .collect(),
            free: (1..=capacity).rev().collect(),
        }
    }

    /// How many entries this slab can hold at once.
    #[must_use]
    pub const fn capacity(&self) -> usize {
        self.slots.len() - 1
    }

    /// Store `value`, returning the token that names it, or hand the value back
    /// when every slot is taken or retired.
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
    /// The value `token` names, if the slot still holds that generation.
    #[must_use]
    pub fn get(&self, token: Token) -> Option<&T> {
        let slot = self.slots.get(token.index)?;
        (slot.generation == token.generation)
            .then_some(slot.value.as_ref())
            .flatten()
    }
    /// Mutable access to the value `token` names.
    pub fn get_mut(&mut self, token: Token) -> Option<&mut T> {
        let slot = self.slots.get_mut(token.index)?;
        if slot.generation != token.generation {
            return None;
        }
        slot.value.as_mut()
    }
    /// Take the value `token` names and free its slot, bumping the slot's
    /// generation so every token minted before this call stops resolving.
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
    fn index_zero_is_never_handed_out() {
        let mut slab = Slab::new(4);
        let mut tokens = Vec::new();
        while let Ok(token) = slab.insert(0u8) {
            assert_ne!(token.index(), 0, "index 0 is reserved for the wakeup");
            tokens.push(token);
        }
        assert_eq!(tokens.len(), slab.capacity());
        for token in tokens {
            assert_eq!(slab.remove(token), Some(0));
        }
    }

    #[test]
    fn generation_exhaustion_retires_slot() {
        let mut slab = Slab::new(1);
        slab.slots[1].generation = u64::MAX;
        let token = slab.insert(1).unwrap();
        assert_eq!(slab.remove(token), Some(1));
        assert_eq!(slab.insert(2), Err(2));
        assert_eq!(slab.get(token), None);
    }
}
