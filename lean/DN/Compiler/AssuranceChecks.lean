-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.AssuranceChecks

Why a premise stated over every model state cannot be met. The inherited
certificates that carried such premises were removed with their workloads, so
these theorems guard no live API; they record the shape and its refutation, so
that a precondition written that way is refused rather than rediscovered. See
`docs/reviews/compiler-assurance.md`.
-/

import DN.Compiler.Semantics

namespace DN.Compiler.AssuranceChecks

open DN.Compiler

/-- A premise requiring one local to be bound in every model state is
contradictory: choose the state with an empty locals map. -/
theorem universalBoundLocal_false {σ : Type} (ffi : σ) (name : String)
    (value : PancakeState σ → Word)
    (h : ∀ s : PancakeState σ, s.locals name = some (value s)) : False := by
  let s : PancakeState σ :=
    { locals := fun _ => none
      memory := fun _ => 0
      memaddrs := fun _ => false
      be := false
      clock := 0
      ffi := ffi
      baseAddr := 0 }
  have hs := h s
  simp [s] at hs

/-- A premise requiring a computed address to belong to every model state's
memory domain is contradictory: choose the state with an empty domain. -/
theorem universalMemoryDomain_false {σ : Type} (ffi : σ)
    (address : PancakeState σ → Word)
    (h : ∀ s : PancakeState σ, s.memaddrs (address s) = true) : False := by
  let s : PancakeState σ :=
    { locals := fun _ => none
      memory := fun _ => 0
      memaddrs := fun _ => false
      be := false
      clock := 0
      ffi := ffi
      baseAddr := 0 }
  have hs := h s
  simp [s] at hs

end DN.Compiler.AssuranceChecks
