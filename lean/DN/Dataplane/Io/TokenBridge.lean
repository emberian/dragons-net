-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Dataplane.Io.Slab
import DN.Dataplane.Flow.Token

/-!
# DN.Dataplane.Io.TokenBridge — checked slab-key token encoding

`Io.Key.pack` is arithmetic over `Nat`; it does not by itself establish that a
key fits the shared 64-bit token partition. This module supplies the narrow
checked seam. A key is encoded only when the corresponding `Flow.Token.slab` is
well formed: its index is nonzero and below `2^32`, and its generation is below
`2^31`. Successful conversion therefore inherits the token partition's decode
round trip and 64-bit bound.

This is a model-level conversion. It does not claim correspondence to a native
adapter or change the allocation and exhaustion behavior of `Io.Slab`.
-/

namespace DN.Dataplane.Io

/-- Convert an I/O slab key to its shared completion-token word exactly when it
satisfies the slab namespace's index and generation bounds. -/
def Key.toToken? (k : Key) : Option Nat :=
  if (DN.Dataplane.Flow.Token.slab k.idx k.gen).Wf then
    some (DN.Dataplane.Flow.Token.slab k.idx k.gen).encode
  else none

/-- A successfully converted key decodes as the same slab token. -/
theorem Key.toToken?_decode {k : Key} {w : Nat}
    (h : k.toToken? = some w) :
    DN.Dataplane.Flow.Token.decode w =
      some (.slab k.idx k.gen) := by
  unfold Key.toToken? at h
  split at h
  next hw =>
    simp only [Option.some.injEq] at h
    subst w
    exact DN.Dataplane.Flow.Token.decode_encode _ hw
  next => simp at h

/-- A successfully converted key fits the shared 64-bit token space. -/
theorem Key.toToken?_lt_tokenSpace {k : Key} {w : Nat}
    (h : k.toToken? = some w) :
    w < DN.Dataplane.Flow.tokenSpace := by
  unfold Key.toToken? at h
  split at h
  next hw =>
    simp only [Option.some.injEq] at h
    subst w
    exact DN.Dataplane.Flow.Token.encode_lt_tokenSpace _ hw
  next => simp at h

-- The wakeup-sentinel index is rejected.
example : (Key.toToken? ⟨0, 0⟩) = none := by decide

-- An index that does not fit the low 32 bits is rejected.
example : (Key.toToken? ⟨2 ^ 32, 0⟩) = none := by decide

-- The known recv-multishot tag collision is rejected by the generation bound.
example : (Key.toToken? ⟨5, 0xBECF0000⟩) = none := by decide

-- The largest valid index and generation are accepted.
example :
    (Key.toToken? ⟨2 ^ 32 - 1, 2 ^ 31 - 1⟩).isSome = true := by decide

end DN.Dataplane.Io
