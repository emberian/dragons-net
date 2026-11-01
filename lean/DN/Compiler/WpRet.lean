-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Wp

/-!
# DN.Compiler.WpRet

What a function gives back. `Safe` lets a run end in any return; a function's result is its return
and the memory it leaves, the session's functions putting theirs in the heap (`give`). So
`SafeR o pre prog R post` asks besides that a return's value and the memory it leaves satisfy `R`,
and `wpR c R Q` is `wp c Q` with a return asking `R` of its value and the memory. `wpR_sound` turns
it, with `vcR`, into `SafeR`, as `wp_sound` does `wp` into `Safe`.

`R` sees neither locals nor the clock: a return empties the locals and the call gives the caller's
back, and the clock is the caller's to clamp. Nor does it see the external world's state: the
session's functions make no external call, its `main` alone does.
-/

namespace DN.Compiler.WpRet

open DN.Compiler DN.Compiler.Entry DN.Compiler.Safe DN.Compiler.Wp

variable {σ : Type}

/-- What a function may give back: the value returned and the memory left. -/
abbrev Ret := Value → (Word → Word) → Prop

/-- What a run may come to: a normal finish in `post`, a return satisfying `R`, or an ending that
is not a failure. -/
def OkR (R : Ret) (post : PancakeState σ → Prop) : Option Result × PancakeState σ → Prop
  | (none, t) => post t
  | (some (.return_ v), t) => R v t.memory
  | (some r, _) => ends (some r) = true

/-- From every state satisfying `pre`, the run of `prog` comes to `OkR R post`. -/
def SafeR (o : Oracle σ) (pre : PancakeState σ → Prop) (prog : PancakeProg) (R : Ret)
    (post : PancakeState σ → Prop) : Prop :=
  ∀ s, pre s → OkR R post (PancakeSem o prog s)

/-- A run that gives back as `R` asks is a run that does not fail. -/
theorem safe {o : Oracle σ} {P Q : PancakeState σ → Prop} {c : PancakeProg} {R : Ret}
    (h : SafeR o P c R Q) : Safe o P c Q := by
  intro s hs
  have k := h s hs
  revert k
  cases PancakeSem o c s with
  | mk r t => cases r with
    | none => exact id
    | some res => cases res <;> first | exact fun _ => rfl | exact id

/-- A program with no `return` of its own: a call's return is its caller's to take. -/
def noRet : PancakeProg → Bool
  | .dec _ _ c | .while_ _ c | .decCall _ _ _ c => noRet c
  | .seq c1 c2 | .cond _ c1 c2 => noRet c1 && noRet c2
  | .ret _ => false
  | _ => true

/-- **A program with no `return` never ends in one.** -/
theorem noRet_run (o : Oracle σ) :
    ∀ (n : Nat) (p : PancakeProg) (s : PancakeState σ), s.clock ≤ n → noRet p = true →
      ∀ v, (PancakeSem o p s).1 ≠ some (.return_ v) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro p
  induction p with
  | skip => intro s _ _ v; rw [PancakeSem.eq_1]; simp
  | dec x e c ih =>
    intro s hc hp v
    rw [PancakeSem.eq_2]
    cases eval s e with
    | none => simp
    | some val => exact ih { s with locals := setLocal s.locals x val } hc hp v
  | assign x e =>
    intro s _ _ v
    rw [PancakeSem.eq_3]
    cases eval s e <;> cases s.locals x <;> simp
  | store d e =>
    intro s _ _ v
    rw [PancakeSem.eq_4]
    cases eval s d <;> cases eval s e <;> try simp
    rename_i a w
    cases memStoreWord s.memory s.memaddrs a w <;> simp
  | storeByte d e =>
    intro s _ _ v
    rw [PancakeSem.eq_10]
    cases eval s d <;> cases eval s e <;> try simp
    rename_i a w
    cases memStoreByte s.memory s.memaddrs s.be a (w.setWidth 8) <;> simp
  | extCall name a b c d =>
    intro s _ _ v
    rw [PancakeSem.eq_5]
    cases eval s a <;> cases eval s b <;> cases eval s c <;> cases eval s d <;> try simp
    rename_i cp cl ap al
    cases readByteArray s.memory s.memaddrs s.be cp cl.toNat <;>
      cases readByteArray s.memory s.memaddrs s.be ap al.toNat <;> try simp
    rename_i conf arr
    cases callFFI o s.ffi name conf arr <;> simp
  | seq c1 c2 ih1 ih2 =>
    intro s hc hp v
    simp only [noRet, Bool.and_eq_true] at hp
    rw [PancakeSem.eq_6]
    have h1 := ih1 s hc hp.1
    have hcl : (clampClock s.clock (PancakeSem o c1 s)).2.clock ≤ n := by
      simp only [clampClock]; omega
    revert h1 hcl
    generalize PancakeSem o c1 s = R
    obtain ⟨x, t⟩ := R
    intro h1 hcl
    simp only [clampClock] at hcl ⊢
    cases x with
    | none => exact ih2 _ hcl hp.2 v
    | some r => simpa using h1 v
  | cond e c1 c2 ih1 ih2 =>
    intro s hc hp v
    simp only [noRet, Bool.and_eq_true] at hp
    rw [PancakeSem.eq_7]
    cases eval s e with
    | none => simp
    | some w =>
      simp only
      split
      · exact ih1 s hc hp.1 v
      · exact ih2 s hc hp.2 v
  | while_ e c _ =>
    intro s hc hp v
    rw [PancakeSem.eq_8]
    cases eval s e with
    | none => simp
    | some w =>
      simp only
      split
      · split
        · simp
        · rename_i h0
          have hb := ihn (s.clock - 1) (by omega) c (decClock s) (by simp [decClock]) hp
          have hcl : (clampClock (s.clock - 1) (PancakeSem o c (decClock s))).2.clock < n := by
            simp only [clampClock]; omega
          revert hb hcl
          generalize PancakeSem o c (decClock s) = R
          obtain ⟨x, t⟩ := R
          intro hb hcl
          simp only [clampClock] at hcl ⊢
          have hloop := ihn _ hcl (.while_ e c) { t with clock := min (s.clock - 1) t.clock }
            (Nat.le_refl _) hp
          cases x with
          | none => exact hloop v
          | some r =>
            cases r with
            | continue_ => exact hloop v
            | return_ u => exact absurd rfl (hb u)
            | _ => simp
      · simp
  | ret e => intro _ _ hp; cases hp
  | decCall rt f args c _ =>
    intro s hc hp v
    rw [PancakeSem.eq_11]
    cases evalArgs s args with
    | none => simp
    | some vs =>
      simp only
      cases lookupCode s.code f vs with
      | none => simp
      | some bp =>
        obtain ⟨body, params⟩ := bp
        simp only
        split
        · simp
        · rename_i h0
          have hcl : (clampClock (s.clock - 1)
              (PancakeSem o body { decClock s with locals := params })).2.clock < n := by
            simp only [clampClock]; omega
          revert hcl
          generalize PancakeSem o body { decClock s with locals := params } = R
          obtain ⟨x, t⟩ := R
          intro hcl
          simp only [clampClock] at hcl ⊢
          cases x with
          | none => simp [callEnded]
          | some r =>
            cases r with
            | return_ u =>
              exact ihn _ hcl c _ (Nat.le_refl _) hp v
            | _ => simp [callEnded, emptyLocals]

/-- **A fragment shown not to fail serves inside a function**: with no `return` of its own, it gives
back as any `R` asks. -/
theorem ofSafe {o : Oracle σ} {P Q : PancakeState σ → Prop} {c : PancakeProg} (R : Ret)
    (hc : noRet c = true) (h : Safe o P c Q) : SafeR o P c R Q := by
  intro s hs
  have k := h s hs
  have hr := noRet_run o s.clock c s (Nat.le_refl _) hc
  revert k hr
  cases PancakeSem o c s with
  | mk r t => cases r with
    | none => exact fun k _ => k
    | some res =>
      cases res with
      | return_ u => exact fun _ hr => absurd rfl (hr u)
      | _ => exact fun k _ => k

theorem skip (o : Oracle σ) (P : PancakeState σ → Prop) (R : Ret) : SafeR o P .skip R P :=
  ofSafe R rfl (Safe.skip o P)

theorem conseq {o : Oracle σ} {P P' Q Q' : PancakeState σ → Prop} {R R' : Ret} {c : PancakeProg}
    (h : SafeR o P c R Q) (hpre : ∀ s, P' s → P s) (hret : ∀ v m, R v m → R' v m)
    (hpost : ∀ s, Q s → Q' s) : SafeR o P' c R' Q' := by
  intro s hs
  have k := h s (hpre s hs)
  revert k
  cases PancakeSem o c s with
  | mk r t => cases r with
    | none => exact hpost t
    | some res => cases res <;> first | exact hret _ _ | exact id

theorem seq {o : Oracle σ} {P M Q : PancakeState σ → Prop} {R : Ret} {c1 c2 : PancakeProg}
    (h1 : SafeR o P c1 R M) (h2 : SafeR o M c2 R Q) (hM : ClockFree M) :
    SafeR o P (.seq c1 c2) R Q := by
  intro s hs
  have k1 := h1 s hs
  rw [PancakeSem]
  simp only [clampClock]
  revert k1
  cases PancakeSem o c1 s with
  | mk r t => cases r with
    | none => intro k1; exact h2 _ (hM t _ k1)
    | some res => cases res <;> exact id

theorem ret {o : Oracle σ} {P Q : PancakeState σ → Prop} {R : Ret} {e : PancakeExp}
    (h : ∀ s, P s → ∃ w, eval s e = some w ∧ R w s.memory) : SafeR o P (.ret e) R Q := by
  intro s hs
  obtain ⟨w, hw, hr⟩ := h s hs
  rw [PancakeSem]
  simp only [hw]
  exact hr

theorem assign {o : Oracle σ} {P Q : PancakeState σ → Prop} {R : Ret} {x : String} {e : PancakeExp}
    (h : ∀ s, P s → ∃ val old, eval s e = some val ∧ s.locals x = some old ∧
      Q { s with locals := setLocal s.locals x val }) : SafeR o P (.assign x e) R Q :=
  ofSafe R rfl (Safe.assign h)

theorem store {o : Oracle σ} {P Q : PancakeState σ → Prop} {R : Ret} {d e : PancakeExp}
    (h : ∀ s, P s → ∃ addr val m, eval s d = some addr ∧ eval s e = some val ∧
      memStoreWord s.memory s.memaddrs addr val = some m ∧ Q { s with memory := m }) :
    SafeR o P (.store d e) R Q :=
  ofSafe R rfl (Safe.store h)

theorem storeByte {o : Oracle σ} {P Q : PancakeState σ → Prop} {R : Ret} {d e : PancakeExp}
    (h : ∀ s, P s → ∃ addr val m, eval s d = some addr ∧ eval s e = some val ∧
      memStoreByte s.memory s.memaddrs s.be addr (val.setWidth 8) = some m ∧
      Q { s with memory := m }) : SafeR o P (.storeByte d e) R Q :=
  ofSafe R rfl (Safe.storeByte h)

theorem extCall {o : Oracle σ} {P Q : PancakeState σ → Prop} {R : Ret} {name : String}
    {c cl a al : PancakeExp}
    (h : ∀ s, P s → ∃ cp clv ap alv conf arr,
      eval s c = some cp ∧ eval s cl = some clv ∧ eval s a = some ap ∧ eval s al = some alv ∧
      readByteArray s.memory s.memaddrs s.be cp clv.toNat = some conf ∧
      readByteArray s.memory s.memaddrs s.be ap alv.toNat = some arr ∧
      ∀ ffi' bytes, bytes.length = arr.length →
        Q { s with memory := writeByteArray s.memaddrs s.be ap bytes s.memory, ffi := ffi' }) :
    SafeR o P (.extCall name c cl a al) R Q :=
  ofSafe R rfl (Safe.extCall h)

theorem dec {o : Oracle σ} {P Q P' Q' : PancakeState σ → Prop} {R : Ret} {v : String}
    {e : PancakeExp} {cont : PancakeProg}
    (hval : ∀ s, P s → ∃ val, eval s e = some val ∧ P' { s with locals := setLocal s.locals v val })
    (hcont : SafeR o P' cont R Q')
    (hpost : ∀ s t, P s → Q' t → Q { t with locals := resVar t.locals v (s.locals v) }) :
    SafeR o P (.dec v e cont) R Q := by
  intro s hs
  obtain ⟨val, hv, hp'⟩ := hval s hs
  have k := hcont _ hp'
  rw [PancakeSem]
  simp only [hv]
  revert k
  cases PancakeSem o cont { s with locals := setLocal s.locals v val } with
  | mk r t => cases r with
    | none => exact hpost s t hs
    | some res => cases res <;> exact id

theorem cond {o : Oracle σ} {P Q : PancakeState σ → Prop} {R : Ret} {e : PancakeExp}
    {c1 c2 : PancakeProg} (hdef : ∀ s, P s → ∃ w, eval s e = some w)
    (h1 : SafeR o (fun s => P s ∧ eval s e ≠ some 0) c1 R Q)
    (h2 : SafeR o (fun s => P s ∧ eval s e = some 0) c2 R Q) : SafeR o P (.cond e c1 c2) R Q := by
  intro s hs
  obtain ⟨w, hw⟩ := hdef s hs
  rw [PancakeSem]
  simp only [hw]
  by_cases hz : w = 0
  · subst hz
    simp only [ne_eq, not_true_eq_false, if_false]
    exact h2 s ⟨hs, hw⟩
  · simp only [ne_eq, hz, not_false_eq_true, if_true]
    exact h1 s ⟨hs, by rw [hw]; simpa using hz⟩

theorem while_ {o : Oracle σ} {I : PancakeState σ → Prop} {R : Ret} {e : PancakeExp}
    {body : PancakeProg} (hdef : ∀ s, I s → ∃ w, eval s e = some w)
    (hbody : SafeR o (fun s => I s ∧ eval s e ≠ some 0) body R I) (hI : ClockFree I) :
    SafeR o I (.while_ e body) R (fun s => I s ∧ eval s e = some 0) := by
  suffices h : ∀ n (s : PancakeState σ), s.clock ≤ n → I s →
      OkR R (fun s => I s ∧ eval s e = some 0) (PancakeSem o (.while_ e body) s) from
    fun s hs => h s.clock s (Nat.le_refl _) hs
  intro n
  induction n with
  | zero =>
    intro s hc hs
    obtain ⟨w, hw⟩ := hdef s hs
    rw [PancakeSem]
    simp only [hw]
    by_cases hz : w = 0
    · subst hz
      simp only [ne_eq, not_true_eq_false, if_false]
      exact ⟨hs, hw⟩
    · simp only [ne_eq, hz, not_false_eq_true, if_true, Nat.le_zero.mp hc]
      rfl
  | succ n ih =>
    intro s hc hs
    obtain ⟨w, hw⟩ := hdef s hs
    rw [PancakeSem]
    simp only [hw]
    by_cases hz : w = 0
    · subst hz
      simp only [ne_eq, not_true_eq_false, if_false]
      exact ⟨hs, hw⟩
    · simp only [ne_eq, hz, not_false_eq_true, if_true]
      by_cases h0 : s.clock = 0
      · simp only [h0, if_true]
        rfl
      · simp only [h0, if_false, clampClock]
        have hd : I (decClock s) ∧ eval (decClock s) e ≠ some 0 :=
          ⟨hI s _ hs, by
            simp only [decClock, eval_clock, hw]
            simpa using hz⟩
        have k := hbody _ hd
        revert k
        cases PancakeSem o body (decClock s) with
        | mk r t =>
          cases r with
          | none =>
            intro k
            exact ih _ (by simp only; omega) (hI t _ k)
          | some res =>
            cases res with
            | continue_ => intro k; simp [OkR, ends] at k
            | break_ => intro k; simp [OkR, ends] at k
            | error => intro k; simp [OkR, ends] at k
            | timeout => intro _; rfl
            | return_ v => exact id
            | finalFFI ev => intro _; rfl

/-! ## The weakest precondition, with what a return gives back -/

/-- `wp` with a return asking `R` of its value and the memory; statements that cannot return are
`wp`'s. -/
def wpR : AProg σ → Ret → Assn σ → Assn σ
  | .skip, _, Q => Q
  | .dec v e c, R, Q => fun s =>
    match eval s e with
    | some val =>
      wpR c R (fun t => Q (restore t v (s.locals v))) { s with locals := setLocal s.locals v val }
    | none => False
  | .assign x e, _, Q => wp (.assign x e) Q
  | .store d e, _, Q => wp (.store d e) Q
  | .storeByte d e, _, Q => wp (.storeByte d e) Q
  | .extCall n c cl a al, _, Q => wp (.extCall n c cl a al) Q
  | .seq c1 c2, R, Q => wpR c1 R (wpR c2 R Q)
  | .cond e c1 c2, R, Q => fun s =>
    match eval s e with
    | some w => if w = 0 then wpR c2 R Q s else wpR c1 R Q s
    | none => False
  | .while_ inv _ _, _, _ => inv
  | .ret e, R, _ => fun s => ∃ w, eval s e = some w ∧ R w s.memory

/-- What the loops ask, a return in a loop's body giving back as `R` asks. -/
def vcR : AProg σ → Ret → Assn σ → Prop
  | .dec v _ c, R, Q => ∀ old, vcR c R (fun t => Q (restore t v old))
  | .seq c1 c2, R, Q => vcR c1 R (wpR c2 R Q) ∧ vcR c2 R Q
  | .cond _ c1 c2, R, Q => vcR c1 R Q ∧ vcR c2 R Q
  | .while_ inv e body, R, Q => ClockFree inv ∧ vcR body R inv ∧
      ∀ s, inv s →
        match eval s e with
        | some w => if w = 0 then Q s else wpR body R inv s
        | none => False
  | _, _, _ => True

/-- `wpR` does not look at the clock. -/
theorem wpR_clockFree :
    ∀ (c : AProg σ) (R : Ret) (Q : Assn σ), ClockFree Q → vcR c R Q → ClockFree (wpR c R Q)
  | .skip, _, _, hQ, _ => hQ
  | .dec v e c, R, Q, hQ, hv => by
    intro s k h
    simp only [wpR, eval_clock] at h ⊢
    split at h
    · exact wpR_clockFree c R _ (restore_clockFree hQ v (s.locals v)) (hv (s.locals v)) _ k h
    · exact h.elim
  | .assign x e, _, Q, hQ, _ => wp_clockFree (.assign x e) Q hQ trivial
  | .store d e, _, Q, hQ, _ => wp_clockFree (.store d e) Q hQ trivial
  | .storeByte d e, _, Q, hQ, _ => wp_clockFree (.storeByte d e) Q hQ trivial
  | .extCall n c cl a al, _, Q, hQ, _ => wp_clockFree (.extCall n c cl a al) Q hQ trivial
  | .seq c1 c2, R, Q, hQ, hv => wpR_clockFree c1 R _ (wpR_clockFree c2 R Q hQ hv.2) hv.1
  | .cond e c1 c2, R, Q, hQ, hv => by
    intro s k h
    simp only [wpR, eval_clock] at h ⊢
    split at h
    · rename_i w hw
      by_cases hz : w = 0
      · simp only [hz, if_true] at h ⊢
        exact wpR_clockFree c2 R Q hQ hv.2 s k h
      · simp only [hz, if_false] at h ⊢
        exact wpR_clockFree c1 R Q hQ hv.1 s k h
    · exact h.elim
  | .while_ _ _ _, _, _, _, hv => hv.1
  | .ret e, _, _, _, _ => by
    intro s k h
    simpa only [wpR, eval_clock] using h

/-- **`wpR` is sound**: from `wpR c R Q`, a run of the program ends as a run may end, returns as
`R` asks, or finishes normally in `Q`, once `Q` ignores the clock and the loops' conditions hold. -/
theorem wpR_sound (o : Oracle σ) :
    ∀ (c : AProg σ) (R : Ret) (Q : Assn σ), ClockFree Q → vcR c R Q → SafeR o (wpR c R Q) c.erase R Q
  | .skip, R, Q, _, _ => skip o Q R
  | .dec v e c, R, Q, hQ, hv => by
    intro s0 hs0
    have k := dec (o := o) (R := R) (P := fun s => s = s0)
      (P' := wpR c R (fun t => Q (restore t v (s0.locals v))))
      (Q' := fun t => Q (restore t v (s0.locals v))) (Q := Q)
      (fun s hs => by
        subst hs
        simp only [wpR] at hs0
        split at hs0
        · rename_i val hval
          exact ⟨val, hval, hs0⟩
        · exact hs0.elim)
      (wpR_sound o c R _ (restore_clockFree hQ v (s0.locals v)) (hv (s0.locals v)))
      (fun s t hs hq => by subst hs; exact hq)
    exact k s0 rfl
  | .assign x e, R, Q, hQ, _ => ofSafe R rfl (wp_sound o (.assign x e) Q hQ trivial)
  | .store d e, R, Q, hQ, _ => ofSafe R rfl (wp_sound o (.store d e) Q hQ trivial)
  | .storeByte d e, R, Q, hQ, _ => ofSafe R rfl (wp_sound o (.storeByte d e) Q hQ trivial)
  | .extCall n c cl a al, R, Q, hQ, _ => ofSafe R rfl (wp_sound o (.extCall n c cl a al) Q hQ trivial)
  | .seq c1 c2, R, Q, hQ, hv =>
    seq (wpR_sound o c1 R _ (wpR_clockFree c2 R Q hQ hv.2) hv.1) (wpR_sound o c2 R Q hQ hv.2)
      (wpR_clockFree c2 R Q hQ hv.2)
  | .cond e c1 c2, R, Q, hQ, hv => by
    refine cond (fun s h => ?_) (conseq (wpR_sound o c1 R Q hQ hv.1) (fun s h => ?_)
      (fun _ _ r => r) (fun _ q => q)) (conseq (wpR_sound o c2 R Q hQ hv.2) (fun s h => ?_)
      (fun _ _ r => r) (fun _ q => q))
    · simp only [wpR] at h
      split at h
      · rename_i w hw
        exact ⟨w, hw⟩
      · exact h.elim
    · obtain ⟨h, hne⟩ := h
      simp only [wpR] at h
      split at h
      · rename_i w hw
        have : w ≠ 0 := fun hz => hne (by rw [hw, hz])
        simpa only [this, if_false] using h
      · exact h.elim
    · obtain ⟨h, heq⟩ := h
      simp only [wpR] at h
      rw [heq] at h
      simpa only [if_true] using h
  | .while_ inv e body, R, Q, _, hv => by
    obtain ⟨hI, hbody, hstep⟩ := hv
    refine conseq (while_ (fun s h => ?_) (conseq (wpR_sound o body R inv hI hbody)
      (fun s h => ?_) (fun _ _ r => r) (fun _ q => q)) hI) (fun _ h => h) (fun _ _ r => r)
      (fun s h => ?_)
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
  | .ret e, R, Q, _, _ => ret fun s h => by
    simp only [wpR] at h
    exact h

/-- A weaker `Q` asks no more. -/
theorem wpR_mono : ∀ (c : AProg σ) (R : Ret) {Q Q' : Assn σ}, (∀ t, Q t → Q' t) →
    ∀ s, wpR c R Q s → wpR c R Q' s
  | .skip, _, _, _, h, s, hw => h s hw
  | .dec _ _ c, R, _, _, h, s, hw => by
    simp only [wpR] at hw ⊢
    split at hw
    · exact wpR_mono c R (fun t hq => h _ hq) _ hw
    · exact hw.elim
  | .assign x e, _, _, _, h, s, hw => wp_mono (.assign x e) h s hw
  | .store d e, _, _, _, h, s, hw => wp_mono (.store d e) h s hw
  | .storeByte d e, _, _, _, h, s, hw => wp_mono (.storeByte d e) h s hw
  | .extCall n c cl a al, _, _, _, h, s, hw => wp_mono (.extCall n c cl a al) h s hw
  | .seq c1 c2, R, _, _, h, s, hw => wpR_mono c1 R (fun t => wpR_mono c2 R h t) s hw
  | .cond _ c1 c2, R, _, _, h, s, hw => by
    simp only [wpR] at hw ⊢
    split at hw
    · rename_i w _
      by_cases hz : w = 0
      · simp only [hz, if_true] at hw ⊢
        exact wpR_mono c2 R h s hw
      · simp only [hz, if_false] at hw ⊢
        exact wpR_mono c1 R h s hw
    · exact hw.elim
  | .while_ .., _, _, _, _, _, hw => hw
  | .ret _, _, _, _, _, _, hw => hw

/-- A run keeps the memory's domain and `@base` (`Safe.sem_same`), so a proof carries them along. -/
theorem keeps {o : Oracle σ} {P Q : PancakeState σ → Prop} {c : PancakeProg} (h : Safe o P c Q)
    (dm : Word → Bool) (b : Word) :
    Safe o (fun s => P s ∧ s.memaddrs = dm ∧ s.baseAddr = b) c
      (fun t => Q t ∧ t.memaddrs = dm ∧ t.baseAddr = b) := by
  intro s ⟨hs, hd, hb⟩
  have k := h s hs
  have hsame := Safe.sem_same o s.clock c s (Nat.le_refl _)
  revert k hsame
  cases PancakeSem o c s with
  | mk r t => cases r with
    | none => intro k hsame; exact ⟨k, hsame.1.trans hd, hsame.2.1.trans hb⟩
    | some res => intro k _; exact k

/-- One run comes to both of two endings shown of it. -/
theorem both {o : Oracle σ} {P Q1 Q2 : PancakeState σ → Prop} {c : PancakeProg} (h1 : Safe o P c Q1)
    (h2 : Safe o P c Q2) : Safe o P c (fun t => Q1 t ∧ Q2 t) := by
  intro s hs
  have k1 := h1 s hs
  have k2 := h2 s hs
  revert k1 k2
  cases PancakeSem o c s with
  | mk r t => cases r with
    | none => exact fun a b => ⟨a, b⟩
    | some _ => exact fun a _ => a

/-- A program that writes no memory: no store, no external call, no call. -/
def noWrite : PancakeProg → Bool
  | .dec _ _ c | .while_ _ c => noWrite c
  | .seq c1 c2 | .cond _ c1 c2 => noWrite c1 && noWrite c2
  | .store .. | .storeByte .. | .extCall .. | .decCall .. => false
  | _ => true

/-- **A program that writes no memory leaves it as it was.** -/
theorem noWrite_run (o : Oracle σ) :
    ∀ (n : Nat) (p : PancakeProg) (s : PancakeState σ), s.clock ≤ n → noWrite p = true →
      (PancakeSem o p s).2.memory = s.memory := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro p
  induction p with
  | skip => intro s _ _; rw [PancakeSem.eq_1]
  | dec x e c ih =>
    intro s hc hp
    rw [PancakeSem.eq_2]
    cases eval s e with
    | none => rfl
    | some val => exact ih { s with locals := setLocal s.locals x val } hc hp
  | assign x e =>
    intro s _ _
    rw [PancakeSem.eq_3]
    cases eval s e <;> cases s.locals x <;> rfl
  | store d e => intro _ _ hp; cases hp
  | storeByte d e => intro _ _ hp; cases hp
  | extCall name a b c d => intro _ _ hp; cases hp
  | decCall rt f args c _ => intro _ _ hp; cases hp
  | seq c1 c2 ih1 ih2 =>
    intro s hc hp
    simp only [noWrite, Bool.and_eq_true] at hp
    rw [PancakeSem.eq_6]
    have h1 := ih1 s hc hp.1
    have hcl : (clampClock s.clock (PancakeSem o c1 s)).2.clock ≤ n := by
      simp only [clampClock]; omega
    revert h1 hcl
    generalize PancakeSem o c1 s = R
    obtain ⟨x, t⟩ := R
    intro h1 hcl
    simp only [clampClock] at hcl h1 ⊢
    cases x with
    | none => exact (ih2 _ hcl hp.2).trans h1
    | some r => exact h1
  | cond e c1 c2 ih1 ih2 =>
    intro s hc hp
    simp only [noWrite, Bool.and_eq_true] at hp
    rw [PancakeSem.eq_7]
    cases eval s e with
    | none => rfl
    | some w =>
      simp only
      split
      · exact ih1 s hc hp.1
      · exact ih2 s hc hp.2
  | while_ e c _ =>
    intro s hc hp
    rw [PancakeSem.eq_8]
    cases eval s e with
    | none => rfl
    | some w =>
      simp only
      split
      · split
        · rfl
        · rename_i h0
          have hb := ihn (s.clock - 1) (by omega) c (decClock s) (by simp [decClock]) hp
          have hcl : (clampClock (s.clock - 1) (PancakeSem o c (decClock s))).2.clock < n := by
            simp only [clampClock]; omega
          revert hb hcl
          generalize PancakeSem o c (decClock s) = R
          obtain ⟨x, t⟩ := R
          intro hb hcl
          simp only [clampClock] at hcl hb ⊢
          have hloop := ihn _ hcl (.while_ e c) { t with clock := min (s.clock - 1) t.clock }
            (Nat.le_refl _) hp
          cases x with
          | none => exact hloop.trans hb
          | some r =>
            cases r with
            | continue_ => exact hloop.trans hb
            | _ => exact hb
      · rfl
  | ret e =>
    intro s _ _
    rw [PancakeSem.eq_9]
    cases eval s e <;> rfl

/-- …so a proof of it carries the memory along. -/
theorem keepsMemory {o : Oracle σ} {P Q : PancakeState σ → Prop} {c : PancakeProg} (h : Safe o P c Q)
    (hc : noWrite c = true) (m0 : Word → Word) :
    Safe o (fun s => P s ∧ s.memory = m0) c (fun t => Q t ∧ t.memory = m0) := by
  intro s ⟨hs, hm⟩
  have k := h s hs
  have hw := noWrite_run o s.clock c s (Nat.le_refl _) hc
  revert k hw
  cases PancakeSem o c s with
  | mk r t => cases r with
    | none => intro k hw; exact ⟨k, hw.trans hm⟩
    | some res => intro k _; exact k

/-- Declarations of locals, each from zero, ahead of a program. -/
def zeros : List String → PancakeProg → PancakeProg
  | [], c => c
  | x :: xs, c => .dec x (.const 0) (zeros xs c)

/-- Each of `xs` holds some word. -/
def Bound (xs : List String) (s : PancakeState σ) : Prop := ∀ y ∈ xs, ∃ w, s.locals y = some w

/-- **Locals declared from zero** are bound for the program after them, the rest of the state as
`P` has it, when setting them keeps `P`; the program's ending is theirs when it does not look at
those locals, which their declarations' ends give back. -/
theorem zeros_runQ {o : Oracle σ} {R : Ret} (xs : List String) {c : PancakeProg} :
    ∀ {P Q : PancakeState σ → Prop},
      (∀ s y w, P s → y ∈ xs → P { s with locals := setLocal s.locals y w }) →
      (∀ t y v, Q t → y ∈ xs → Q (restore t y v)) →
      SafeR o (fun s => P s ∧ Bound xs s) c R Q → SafeR o P (zeros xs c) R Q := by
  induction xs with
  | nil =>
    intro P Q _ _ hc
    exact conseq hc (fun s hs => ⟨hs, fun _ h => by cases h⟩) (fun _ _ h => h) (fun _ h => h)
  | cons x xs ih =>
    intro P Q hP hQ hc
    refine dec (P' := fun s => P s ∧ ∃ w, s.locals x = some w) (Q' := Q)
      (fun s hs => ⟨0, rfl, hP s x 0 hs (by simp), 0, by simp [setLocal]⟩) ?_
      (fun s t _ hq => hQ t x (s.locals x) hq (by simp))
    refine ih (P := fun s => P s ∧ ∃ w, s.locals x = some w) (fun s y w ⟨hs, hx⟩ hy => ?_)
      (fun t y v hq hy => hQ t y v hq (List.mem_cons_of_mem _ hy))
      (conseq hc (fun s ⟨⟨hs, hx⟩, hb⟩ => ⟨hs, fun y hy => ?_⟩) (fun _ _ h => h) (fun _ h => h))
    · refine ⟨hP s y w hs (List.mem_cons_of_mem _ hy), ?_⟩
      by_cases e : x = y
      · exact ⟨w, by simp [setLocal, e]⟩
      · obtain ⟨u, hu⟩ := hx
        exact ⟨u, by simp [setLocal, e, hu]⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hb y hy

/-- …so for a program that never finishes normally, as a function's body, whose declarations'
scopes then never end. -/
theorem zeros_run {o : Oracle σ} {R : Ret} (xs : List String) {c : PancakeProg} :
    ∀ {P : PancakeState σ → Prop}, (∀ s y w, P s → y ∈ xs → P { s with locals := setLocal s.locals y w }) →
      SafeR o (fun s => P s ∧ Bound xs s) c R (fun _ => False) →
      SafeR o P (zeros xs c) R (fun _ => False) :=
  fun hP hc => zeros_runQ xs hP (fun _ _ _ h _ => h) hc

/-- A return can satisfy `R`: `return 7` gives back seven. -/
theorem wpR_witness :
    wpR (σ := Unit) (.ret (.const 7)) (fun v _ => v = 7) (fun _ => False) (bareState ()) :=
  ⟨7, rfl, rfl⟩

/-- `SafeR` can hold: `return 7` gives back seven, from any state. -/
theorem safeR_witness :
    SafeR (σ := Unit) Oracle.idle (fun _ => True) (.ret (.const 7)) (fun v _ => v = 7)
      (fun _ => False) :=
  ret fun _ _ => ⟨7, rfl, rfl⟩

/-- What the loops ask can hold: a local counted down to zero, its invariant that it is bound. -/
theorem vcR_witness :
    vcR (σ := Unit) (.while_ (fun s => ∃ w, s.locals "n" = some w) (.var "n")
      (.assign "n" (.op .sub (.var "n") (.const 1)))) (fun _ _ => True)
      (fun s => ∃ w, s.locals "n" = some w) := by
  refine ⟨fun _ _ h => h, trivial, fun s ⟨w, hw⟩ => ?_⟩
  simp only [eval, hw]
  split
  · exact ⟨w, rfl⟩
  · simp only [wpR, wp, eval, hw]
    exact ⟨w - 1, by simp [setLocal]⟩

/-- …and `R` is asked: `return 7` does not give back eight. -/
theorem safeR_refutes :
    ¬ SafeR (σ := Unit) Oracle.idle (fun s => s = bareState ()) (.ret (.const 7)) (fun v _ => v = 8)
      (fun _ => False) := by
  intro h
  have k := h (bareState ()) rfl
  simp [PancakeSem, OkR, eval] at k

/-- A result that is not a normal end does not depend on what the normal end would ask. -/
theorem okR_post {R : Ret} {P Q : PancakeState σ → Prop} {r : Option Result} {t t' : PancakeState σ}
    (hr : r ≠ none) (hm : t'.memory = t.memory) (h : OkR R P (r, t)) : OkR R Q (r, t') := by
  cases r with
  | none => exact absurd rfl hr
  | some res => cases res <;> simp_all [OkR]

theorem okR_witness : OkR (σ := Unit) (fun _ _ => True) (fun _ => True) (none, bareState ()) := trivial

/-- A run that goes on keeps every local bound, of a proof with returns. -/
theorem safeR_keeps {o : Oracle σ} {s : PancakeState σ} {c : PancakeProg} {R : Ret}
    {Q : PancakeState σ → Prop} (h : SafeR o (fun u => u = s) c R Q) :
    SafeR o (fun u => u = s) c R (fun t => Q t ∧ Safe.Keeps s t) := by
  rintro u rfl
  have k := h u rfl
  have hk := Safe.sem_keeps o u.clock c u (Nat.le_refl _)
  revert k hk
  rcases PancakeSem o c u with ⟨_ | r, t⟩
  · intro k hk; exact ⟨k, hk trivial⟩
  · intro k _; cases r <;> exact k

end DN.Compiler.WpRet
