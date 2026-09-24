-- SPDX-License-Identifier: AGPL-3.0-or-later

/-!
# DN.Dataplane.Recycling — the discipline two stores share, stated once

A dataplane recycles slots: a file descriptor is closed and reopened, a pending
operation completes and its slot is handed to the next one. The danger is the
same in both cases and is called ABA: a key captured before the recycling must
not select what took the place of what it named. Two stores in this project face
it — the connection table keyed by descriptor
(`DN.Dataplane.Slab.Reactor`, one counter for the whole table) and the
pending-operation slab keyed by slot (`DN.Dataplane.Io.Slab`, a counter per
slot). They are different designs, not two copies of one: which of them a
completion adapter keeps is an open question, and guessing it before the adapter
exists would be inventing the answer.

What need not be guessed is the property both must have, so it is stated here
once and proven once, and each store supplies the pieces:

* `Wf` — the store's own well-formedness, preserved by every operation;
* `Ended s k` — the incarnation `k` names is over in `s`;
* an ended incarnation stays ended (`ended_step`), and an ended key resolves to
  nothing (`resolve_ended`).

`never_resolves_again` then holds for any operation sequence at all, and is what
each store instantiates rather than re-proving.
-/

namespace DN.Dataplane

universe u v w x

/-- A store whose keys name incarnations that can end, with the operations that
drive it. The fields are the obligations a store discharges; the theorem below is
what it gets in return. -/
structure Recycling (S : Type u) (Op : Type v) (Key : Type w) (Val : Type x) where
  /-- One operation on the store. -/
  step : S → Op → S
  /-- What a key selects, if its incarnation is still current. -/
  resolve : S → Key → Option Val
  /-- The store's own well-formedness. -/
  Wf : S → Prop
  /-- The incarnation this key names is over. -/
  Ended : S → Key → Prop
  /-- Well-formedness survives every operation. -/
  wf_step : ∀ s op, Wf s → Wf (step s op)
  /-- An ended incarnation never comes back, whatever the store does next. -/
  ended_step : ∀ s op k, Wf s → Ended s k → Ended (step s op) k
  /-- A key whose incarnation is over selects nothing. -/
  resolve_ended : ∀ s k, Wf s → Ended s k → resolve s k = none

namespace Recycling

variable {S : Type u} {Op : Type v} {Key : Type w} {Val : Type x}

/-- Apply a sequence of operations. -/
def run (R : Recycling S Op Key Val) (s : S) : List Op → S
  | [] => s
  | op :: rest => R.run (R.step s op) rest

/-- **A key whose incarnation has ended never selects anything again**, after any
sequence of operations — not merely after the next one. This is the ABA
guarantee: the store may recycle the slot or the descriptor as often as it likes,
and the stale key keeps resolving to nothing. -/
theorem never_resolves_again (R : Recycling S Op Key Val) {s : S} {k : Key}
    (hwf : R.Wf s) (hend : R.Ended s k) (ops : List Op) :
    R.resolve (R.run s ops) k = none := by
  induction ops generalizing s with
  | nil => exact R.resolve_ended s k hwf hend
  | cons op rest ih =>
    exact ih (R.wf_step s op hwf) (R.ended_step s op k hwf hend)

end Recycling

end DN.Dataplane
