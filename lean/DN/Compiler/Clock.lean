-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.Clock

Adapted from the compiler extraction recorded in docs/provenance.json.
These definitions and theorems concern the Lean model. Correspondence to the
HOL4 backend, pretty-printer/parser, ABI and executable is tracked separately
in docs/assurance.md. The model is a restricted 64-bit Pancake fragment.
-/
import DN.Compiler.Region

namespace DN.Compiler.Clock

open DN.Compiler DN.Compiler.Region

variable {σ : Type}

/-! ## 0. The clock-accounting refinement predicate

`RefinesClk o p P Q`: from any state satisfying the precondition `P`, the emitted
program `p` runs to a NORMAL termination (`result = none`) in a state `s'` related
to the entry by `Q`, having consumed clock MONOTONICALLY (`s'.clock ≤ s.clock`).
This permits clock CONSUMPTION (a loop) and a PRECONDITION (an
invariant + budget, or an enabling context); the `≤` accounting is what keeps the
per-boundary clock-clamps no-ops so the predicate still composes. -/
def RefinesClk (o : Oracle σ) (p : PancakeProg)
    (P : PancakeState σ → Prop) (Q : PancakeState σ → PancakeState σ → Prop) : Prop :=
  ∀ s, P s → ∃ s', PancakeSem o p s = (none, s') ∧ Q s s' ∧ s'.clock ≤ s.clock

/-! ## 1. Straight-line stages -/

theorem refinesClk_assign (o : Oracle σ) (x : String) (e : PancakeExp)
    (P : PancakeState σ → Prop) (f : PancakeState σ → Value)
    (hf : ∀ s, P s → eval s e = some (f s)) :
    RefinesClk o (.assign x e) P
      (fun s s' => s' = { s with locals := setLocal s.locals x (f s) }) := by
  intro s hP
  exact ⟨_, sem_assign (oracle := o) (hf s hP), rfl, Nat.le_refl _⟩

/-! ## 2. The compose rules -/

/-- THE COMPOSE RULE. Two `RefinesClk` stages compose sequentially, given the
link `P₁ ∧ Q₁ → P₂` (the first stage's postcondition enables the second's
precondition). The `Seq` clock-clamp `min s.clock s1.clock` collapses to `s1.clock`
by the `≤` accounting (`hc1 : s1.clock ≤ s.clock`), so the clamped mid-state is
`defeq` to the unclamped one. Works in EITHER order — a loop then a straight-line
frame, or a frame then a loop — since it is symmetric in the stage roles. -/
theorem refinesClk_seq (o : Oracle σ) {p1 p2 : PancakeProg}
    {P1 : PancakeState σ → Prop} {Q1 : PancakeState σ → PancakeState σ → Prop}
    {P2 : PancakeState σ → Prop} {Q2 : PancakeState σ → PancakeState σ → Prop}
    (h1 : RefinesClk o p1 P1 Q1)
    (h2 : RefinesClk o p2 P2 Q2)
    (hlink : ∀ s s1, P1 s → Q1 s s1 → P2 s1) :
    RefinesClk o (.seq p1 p2) P1 (fun s s' => ∃ s1, Q1 s s1 ∧ Q2 s1 s') := by
  intro s hP1
  obtain ⟨s1, he1, hQ1, hc1⟩ := h1 s hP1
  obtain ⟨s2, he2, hQ2, hc2⟩ := h2 s1 (hlink s s1 hP1 hQ1)
  refine ⟨s2, ?_, ⟨s1, hQ1, hQ2⟩, Nat.le_trans hc2 hc1⟩
  have hmin : min s.clock s1.clock = s1.clock := by omega
  rw [sem_seq_none (oracle := o) he1, hmin]
  -- `{ s1 with clock := s1.clock }` is defeq `s1` (structure eta)
  exact he2

/-- The lexical-scope (`Dec`) compose rule. `Dec v e cont` binds `v := eval e`,
runs `cont`, then restores the shadowed binding. Given the bind evaluates under
`P` and the continuation is a `RefinesClk` stage whose precondition `Pc` is
established on the extended scope, the `Dec` is a `RefinesClk` stage. Clock is
untouched by the bind/restore, so `cont`'s `≤` accounting carries through. -/
theorem refinesClk_dec (o : Oracle σ) (v : String) (e : PancakeExp)
    {cont : PancakeProg}
    (P : PancakeState σ → Prop) (f : PancakeState σ → Value)
    (Pc : PancakeState σ → Prop) (Qc : PancakeState σ → PancakeState σ → Prop)
    (hf : ∀ s, P s → eval s e = some (f s))
    (hcont : RefinesClk o cont Pc Qc)
    (hlink : ∀ s, P s → Pc { s with locals := setLocal s.locals v (f s) }) :
    RefinesClk o (.dec v e cont) P
      (fun s s' => ∃ smid,
        Qc { s with locals := setLocal s.locals v (f s) } smid ∧
        s' = { smid with locals := resVar smid.locals v (s.locals v) }) := by
  intro s hP
  obtain ⟨smid, hemid, hQmid, hcmid⟩ := hcont _ (hlink s hP)
  refine ⟨{ smid with locals := resVar smid.locals v (s.locals v) },
    sem_dec (oracle := o) (hf s hP) hemid, ⟨smid, hQmid, rfl⟩, ?_⟩
  -- (restore smid).clock = smid.clock ≤ (bind s).clock = s.clock
  exact hcmid

/-- Consequence: strengthen the precondition and weaken the postcondition of a
`RefinesClk` stage. Lets a composed stage be re-stated with a clean contract. -/
theorem refinesClk_conseq (o : Oracle σ) {p : PancakeProg}
    {P Q} {P' : PancakeState σ → Prop} {Q' : PancakeState σ → PancakeState σ → Prop}
    (h : RefinesClk o p P Q)
    (hP : ∀ s, P' s → P s)
    (hQ : ∀ s s', P' s → Q s s' → Q' s s') :
    RefinesClk o p P' Q' := by
  intro s hP's
  obtain ⟨s', he, hq, hc⟩ := h s (hP s hP's)
  exact ⟨s', he, hQ s s' hP's hq, hc⟩

/-! ## 3. The bounded-`While` rule with clock accounting

`while_inv_cond` (EmitCorrectLoop) delivers `∃ s', … ∧ I 0 s'` but does NOT track
the final clock. `RefinesClk` needs `s'.clock ≤ s.clock`, so we re-run the same
induction adding the clock bound — the body hypothesis already supplies
`s2.clock = s.clock - 1` per step, so the bound telescopes. -/
theorem while_inv_cond_clk (o : Oracle σ) (e : PancakeExp) (body : PancakeProg)
    (I : Nat → PancakeState σ → Prop)
    (hguard : ∀ n s, I n s → eval s e = some (if n = 0 then (0 : Word) else 1))
    (hbody : ∀ n s, I (n + 1) s →
      ∃ s2, PancakeSem o body (decClock s) = (none, s2) ∧ I n s2 ∧ s2.clock = s.clock - 1) :
    ∀ (rem : Nat) (s : PancakeState σ), I rem s → rem ≤ s.clock →
      ∃ s', PancakeSem o (.while_ e body) s = (none, s') ∧ I 0 s' ∧ s'.clock ≤ s.clock := by
  intro rem
  induction rem with
  | zero =>
    intro s hI _
    refine ⟨s, ?_, hI, Nat.le_refl _⟩
    rw [PancakeSem, hguard 0 s hI]; simp
  | succ m ih =>
    intro s hI hclock
    have hclock0 : s.clock ≠ 0 := by omega
    have hcond : eval s e = some (1 : Word) := by
      have := hguard (m + 1) s hI; simpa using this
    obtain ⟨s2, hs2eq, hs2I, hs2clk⟩ := hbody m s hI
    have hmin : min (s.clock - 1) s2.clock = s2.clock := by omega
    have hclamp : ({ s2 with clock := min (s.clock - 1) s2.clock } : PancakeState σ) = s2 := by
      rw [hmin]
    obtain ⟨s', hs'eq, hs'I, hs'clk⟩ := ih s2 hs2I (by omega)
    refine ⟨s', ?_, hs'I, by omega⟩
    rw [PancakeSem]
    simp only [hcond, ne_eq, show ((1 : Word) = 0) = False from by decide, not_false_eq_true,
               if_true, hclock0, if_false, clampClock, hs2eq]
    rw [hclamp]
    exact hs'eq

end DN.Compiler.Clock
