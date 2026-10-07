-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Safe

/-!
# DN.Compiler.Wp

What a program computes, not only that it does not fail. A program carries an invariant on each
loop (`AProg`); `wp c Q` is an assertion before it from which every run that finishes normally ends
in `Q`, and `vc c Q` what its loops ask of their invariants. `wp_sound` turns the two into
`Safe` once for every program, so a program is shown to compute what it should by unfolding `wp`
and `vc` and proving what is left about words, bytes and lists.

The semantics adjusts the clock between statements, so `Q` and the invariants may not look at it
(`ClockFree`), and neither does `wp` (`wp_clockFree`).
-/

namespace DN.Compiler.Wp

open DN.Compiler DN.Compiler.Safe

variable {σ : Type}

abbrev Assn (σ : Type) := PancakeState σ → Prop

/-- A program with an invariant on each loop. -/
inductive AProg (σ : Type)
  | skip
  | dec (v : String) (e : PancakeExp) (cont : AProg σ)
  | assign (v : String) (e : PancakeExp)
  | store (dst src : PancakeExp)
  | storeByte (dst src : PancakeExp)
  | extCall (name : String) (confPtr confLen arrPtr arrLen : PancakeExp)
  | seq (c1 c2 : AProg σ)
  | cond (e : PancakeExp) (c1 c2 : AProg σ)
  | while_ (inv : Assn σ) (e : PancakeExp) (body : AProg σ)
  | ret (e : PancakeExp)

/-- The program without its invariants. -/
def AProg.erase : AProg σ → PancakeProg
  | .skip => .skip
  | .dec v e c => .dec v e c.erase
  | .assign v e => .assign v e
  | .store d e => .store d e
  | .storeByte d e => .storeByte d e
  | .extCall n c cl a al => .extCall n c cl a al
  | .seq c1 c2 => .seq c1.erase c2.erase
  | .cond e c1 c2 => .cond e c1.erase c2.erase
  | .while_ _ e c => .while_ e c.erase
  | .ret e => .ret e

/-- The state after a declaration's scope ends: the local back to what it was before. -/
def restore (t : PancakeState σ) (v : String) (old : Option Value) : PancakeState σ :=
  { t with locals := resVar t.locals v old }

def wp : AProg σ → Assn σ → Assn σ
  | .skip, Q => Q
  | .dec v e c, Q => fun s =>
    match eval s e with
    | some val =>
      wp c (fun t => Q (restore t v (s.locals v))) { s with locals := setLocal s.locals v val }
    | none => False
  | .assign x e, Q => fun s =>
    match eval s e, s.locals x with
    | some val, some _ => Q { s with locals := setLocal s.locals x val }
    | _, _ => False
  | .store d e, Q => fun s =>
    match eval s d, eval s e with
    | some a, some val =>
      match memStoreWord s.memory s.memaddrs a val with
      | some m => Q { s with memory := m }
      | none => False
    | _, _ => False
  | .storeByte d e, Q => fun s =>
    match eval s d, eval s e with
    | some a, some val =>
      match memStoreByte s.memory s.memaddrs s.be a (val.setWidth 8) with
      | some m => Q { s with memory := m }
      | none => False
    | _, _ => False
  | .extCall _ c cl a al, Q => fun s =>
    match eval s c, eval s cl, eval s a, eval s al with
    | some cp, some clv, some ap, some alv =>
      match readByteArray s.memory s.memaddrs s.be cp clv.toNat,
        readByteArray s.memory s.memaddrs s.be ap alv.toNat with
      | some _, some arr => ∀ ffi' (bytes : List (BitVec 8)), bytes.length = arr.length →
          Q { s with memory := writeByteArray s.memaddrs s.be ap bytes s.memory, ffi := ffi' }
      | _, _ => False
    | _, _, _, _ => False
  | .seq c1 c2, Q => wp c1 (wp c2 Q)
  | .cond e c1 c2, Q => fun s =>
    match eval s e with
    | some w => if w = 0 then wp c2 Q s else wp c1 Q s
    | none => False
  | .while_ inv _ _, _ => inv
  | .ret e, _ => fun s => (eval s e).isSome

/-- What the loops ask: each invariant ignores the clock, has its condition defined, and is kept
by the body while the condition holds and gives `Q` once it fails. -/
def vc : AProg σ → Assn σ → Prop
  | .dec v _ c, Q => ∀ old, vc c (fun t => Q (restore t v old))
  | .seq c1 c2, Q => vc c1 (wp c2 Q) ∧ vc c2 Q
  | .cond _ c1 c2, Q => vc c1 Q ∧ vc c2 Q
  | .while_ inv e body, Q => ClockFree inv ∧ vc body inv ∧
      ∀ s, inv s →
        match eval s e with
        | some w => if w = 0 then Q s else wp body inv s
        | none => False
  | _, _ => True

theorem restore_clockFree {Q : Assn σ} (hQ : ClockFree Q) (v : String) (old : Option Value) :
    ClockFree (fun t => Q (restore t v old)) :=
  fun t k h => hQ (restore t v old) k h

/-- `wp` does not look at the clock. -/
theorem wp_clockFree : ∀ (c : AProg σ) (Q : Assn σ), ClockFree Q → vc c Q → ClockFree (wp c Q)
  | .skip, _, hQ, _ => hQ
  | .dec v e c, Q, hQ, hv => by
    intro s k h
    simp only [wp, eval_clock] at h ⊢
    split at h
    · rename_i val hval
      exact wp_clockFree c _ (restore_clockFree hQ v (s.locals v)) (hv (s.locals v)) _ k h
    · exact h.elim
  | .assign x e, Q, hQ, _ => by
    intro s k h
    simp only [wp, eval_clock] at h ⊢
    split at h
    · rename_i val old hval hold
      exact hQ _ k h
    · exact h.elim
  | .store d e, Q, hQ, _ => by
    intro s k h
    simp only [wp, eval_clock] at h ⊢
    split at h
    · rename_i a val ha he
      split at h
      · rename_i m hm
        exact hQ _ k h
      · exact h.elim
    · exact h.elim
  | .storeByte d e, Q, hQ, _ => by
    intro s k h
    simp only [wp, eval_clock] at h ⊢
    split at h
    · rename_i a val ha he
      split at h
      · rename_i m hm
        exact hQ _ k h
      · exact h.elim
    · exact h.elim
  | .extCall _ c cl a al, Q, hQ, _ => by
    intro s k h
    simp only [wp, eval_clock] at h ⊢
    split at h
    · rename_i cp clv ap alv hc hcl ha hal
      split at h
      · rename_i conf arr hconf harr
        exact fun ffi' bytes hl => hQ _ k (h ffi' bytes hl)
      · exact h.elim
    · exact h.elim
  | .seq c1 c2, Q, hQ, hv => wp_clockFree c1 _ (wp_clockFree c2 Q hQ hv.2) hv.1
  | .cond e c1 c2, Q, hQ, hv => by
    intro s k h
    simp only [wp, eval_clock] at h ⊢
    split at h
    · rename_i w hw
      by_cases hz : w = 0
      · simp only [hz, if_true] at h ⊢
        exact wp_clockFree c2 Q hQ hv.2 s k h
      · simp only [hz, if_false] at h ⊢
        exact wp_clockFree c1 Q hQ hv.1 s k h
    · exact h.elim
  | .while_ _ _ _, _, _, hv => hv.1
  | .ret e, _, _, _ => by
    intro s k h
    simpa only [wp, eval_clock] using h

/-- **`wp` is sound**: from `wp c Q`, a run of the program either ends as a run may end or
finishes normally in `Q`, once `Q` ignores the clock and the loops' conditions hold. -/
theorem wp_sound (o : Oracle σ) :
    ∀ (c : AProg σ) (Q : Assn σ), ClockFree Q → vc c Q → Safe o (wp c Q) c.erase Q
  | .skip, Q, _, _ => Safe.skip o Q
  | .dec v e c, Q, hQ, hv => by
    intro s0 hs0
    have k := Safe.dec (o := o) (P := fun s => s = s0)
      (P' := wp c (fun t => Q (restore t v (s0.locals v))))
      (Q' := fun t => Q (restore t v (s0.locals v))) (Q := Q)
      (fun s hs => by
        subst hs
        simp only [wp] at hs0
        split at hs0
        · rename_i val hval
          exact ⟨val, hval, hs0⟩
        · exact hs0.elim)
      (wp_sound o c _ (restore_clockFree hQ v (s0.locals v)) (hv (s0.locals v)))
      (fun s t hs hq => by subst hs; exact hq)
    exact k s0 rfl
  | .assign x e, Q, _, _ => Safe.assign fun s h => by
    simp only [wp] at h
    split at h
    · rename_i val old hval hold
      exact ⟨val, old, hval, hold, h⟩
    · exact h.elim
  | .store d e, Q, _, _ => Safe.store fun s h => by
    simp only [wp] at h
    split at h
    · rename_i a val ha he
      split at h
      · rename_i m hm
        exact ⟨a, val, m, ha, he, hm, h⟩
      · exact h.elim
    · exact h.elim
  | .storeByte d e, Q, _, _ => Safe.storeByte fun s h => by
    simp only [wp] at h
    split at h
    · rename_i a val ha he
      split at h
      · rename_i m hm
        exact ⟨a, val, m, ha, he, hm, h⟩
      · exact h.elim
    · exact h.elim
  | .extCall _ c cl a al, Q, _, _ => Safe.extCall fun s h => by
    simp only [wp] at h
    split at h
    · rename_i cp clv ap alv hc hcl ha hal
      split at h
      · rename_i conf arr hconf harr
        exact ⟨cp, clv, ap, alv, conf, arr, hc, hcl, ha, hal, hconf, harr, h⟩
      · exact h.elim
    · exact h.elim
  | .seq c1 c2, Q, hQ, hv =>
    Safe.seq (wp_sound o c1 _ (wp_clockFree c2 Q hQ hv.2) hv.1) (wp_sound o c2 Q hQ hv.2)
      (wp_clockFree c2 Q hQ hv.2)
  | .cond e c1 c2, Q, hQ, hv => by
    refine Safe.cond (fun s h => ?_) (Safe.conseq (wp_sound o c1 Q hQ hv.1) (fun s h => ?_)
      (fun _ q => q)) (Safe.conseq (wp_sound o c2 Q hQ hv.2) (fun s h => ?_) (fun _ q => q))
    · simp only [wp] at h
      split at h
      · rename_i w hw
        exact ⟨w, hw⟩
      · exact h.elim
    · obtain ⟨h, hne⟩ := h
      simp only [wp] at h
      split at h
      · rename_i w hw
        have : w ≠ 0 := fun hz => hne (by rw [hw, hz])
        simpa only [this, if_false] using h
      · exact h.elim
    · obtain ⟨h, heq⟩ := h
      simp only [wp] at h
      rw [heq] at h
      simpa only [if_true] using h
  | .while_ inv e body, Q, _, hv => by
    obtain ⟨hI, hbody, hstep⟩ := hv
    refine Safe.conseq (Safe.while_ (fun s h => ?_) (Safe.conseq (wp_sound o body inv hI hbody)
      (fun s h => ?_) (fun _ q => q)) hI) (fun _ h => h) (fun s h => ?_)
    · have := hstep s h
      split at this
      · rename_i w hw
        exact ⟨w, hw⟩
      · exact this.elim
    · obtain ⟨h, hne⟩ := h
      have hs := hstep s h
      split at hs
      · rename_i w hw
        have hw0 : w ≠ 0 := fun hz => hne (by rw [hw, hz])
        simpa only [hw0, if_false] using hs
      · exact hs.elim
    · obtain ⟨h, heq⟩ := h
      have := hstep s h
      rw [heq] at this
      simpa only [if_true] using this
  | .ret e, Q, _, _ => Safe.ret fun s h => by
    simp only [wp] at h
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
    exact ⟨w, hw⟩

/-- A weaker `Q` asks no more. -/
theorem wp_mono : ∀ (c : AProg σ) {Q R : Assn σ}, (∀ t, Q t → R t) → ∀ s, wp c Q s → wp c R s
  | .skip, _, _, h, s, hw => h s hw
  | .dec _ _ c, _, _, h, s, hw => by
    simp only [wp] at hw ⊢
    split at hw
    · exact wp_mono c (fun t hq => h _ hq) _ hw
    · exact hw.elim
  | .assign .., _, _, h, s, hw => by
    simp only [wp] at hw ⊢
    split at hw
    · exact h _ hw
    · exact hw.elim
  | .store .., _, _, h, s, hw => by
    simp only [wp] at hw ⊢
    split at hw
    · split at hw
      · exact h _ hw
      · exact hw.elim
    · exact hw.elim
  | .storeByte .., _, _, h, s, hw => by
    simp only [wp] at hw ⊢
    split at hw
    · split at hw
      · exact h _ hw
      · exact hw.elim
    · exact hw.elim
  | .extCall .., _, _, h, s, hw => by
    simp only [wp] at hw ⊢
    split at hw
    · split at hw
      · exact fun ffi' bytes hl => h _ (hw ffi' bytes hl)
      · exact hw.elim
    · exact hw.elim
  | .seq c1 c2, _, _, h, s, hw => wp_mono c1 (fun t => wp_mono c2 h t) s hw
  | .cond _ c1 c2, _, _, h, s, hw => by
    simp only [wp] at hw ⊢
    split at hw
    · rename_i w _
      by_cases hz : w = 0
      · simp only [hz, if_true] at hw ⊢
        exact wp_mono c2 h s hw
      · simp only [hz, if_false] at hw ⊢
        exact wp_mono c1 h s hw
    · exact hw.elim
  | .while_ .., _, _, _, _, hw => hw
  | .ret _, _, _, _, _, hw => hw

/-! ## Running a program forward, one statement at a time -/

theorem setLocal_same (lc : String → Option Value) (x : String) (w : Value) :
    setLocal lc x w x = some w := by simp [setLocal]

theorem setLocal_ne (lc : String → Option Value) {x y : String} (w : Value) (h : y ≠ x) :
    setLocal lc x w y = lc y := by simp [setLocal, h]

/-- After `c1`, `M`; from `M`, `c2` ends in `Q`. -/
theorem wp_seq {c1 c2 : AProg σ} {M Q : Assn σ} {s : PancakeState σ} (h1 : wp c1 M s)
    (h2 : ∀ t, M t → wp c2 Q t) : wp (.seq c1 c2) Q s :=
  wp_mono c1 h2 s h1

theorem wp_assign {x : String} {e : PancakeExp} {Q : Assn σ} {s : PancakeState σ} {val old : Value}
    (he : eval s e = some val) (hx : s.locals x = some old)
    (hq : Q { s with locals := setLocal s.locals x val }) : wp (.assign x e) Q s := by
  simp only [wp, he, hx]
  exact hq

/-- What the loops ask can hold: a local counted down to zero, its invariant that it is bound. -/
theorem vc_witness :
    vc (σ := Unit) (.while_ (fun s => ∃ w, s.locals "n" = some w) (.var "n")
      (.assign "n" (.op .sub (.var "n") (.const 1)))) (fun s => ∃ w, s.locals "n" = some w) := by
  refine ⟨fun _ _ h => h, trivial, fun s ⟨w, hw⟩ => ?_⟩
  simp only [eval, hw]
  split
  · exact ⟨w, rfl⟩
  · simp only [wp, eval, hw]
    exact ⟨w - 1, by simp [setLocal]⟩

end DN.Compiler.Wp
