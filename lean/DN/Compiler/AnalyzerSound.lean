-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Analyzer
import DN.Compiler.Safe
import DN.Compiler.Bytes

/-!
# DN.Compiler.AnalyzerSound

**A program the analysis of `DN.Compiler.Analyzer` accepts never errs.** From every state whose
heap covers `size` bytes from `@base` and whose locals and cells are as the abstract state says,
the run of a statement the analysis accepts ends as a run may end or finishes normally in a state
the abstract result stands for (`analyze_safe`); for a whole `main` the analysis accepts, no run
fails (`never_fails`).
-/

namespace DN.Compiler.Analyzer

open DN.Compiler DN.Compiler.Safe

variable {σ : Type}

/-! ## Words -/

/-- The words `v` stands for, with `b` for `@base`. -/
def AVal.holds (b : Word) (v : AVal) (w : Word) : Prop :=
  if v.ptr then
    ∃ x : Int, v.lo ≤ x ∧ x ≤ v.hi ∧ w = b + BitVec.ofInt 64 x ∧ ∀ r, v.res = some r → x % 8 = r
  else v.lo ≤ w.toInt ∧ w.toInt ≤ v.hi ∧ ∀ r, v.res = some r → w.toInt % 8 = r

theorem toInt_range (w : Word) : wordMin ≤ w.toInt ∧ w.toInt ≤ wordMax := by
  have h1 := BitVec.le_toInt w
  have h2 := @BitVec.toInt_le 64 w
  simp only [wordMin, wordMax] at *
  omega

theorem holds_top (b w : Word) : AVal.top.holds b w := by
  simp only [AVal.holds, AVal.top, Bool.false_eq_true, if_false, reduceCtorEq, false_implies,
    implies_true, and_true]
  exact toInt_range w

theorem holds_num {b w : Word} {lo hi : Int} {res : Option Nat} (h1 : lo ≤ w.toInt)
    (h2 : w.toInt ≤ hi) (h3 : ∀ r, res = some r → w.toInt % 8 = r) :
    (AVal.num lo hi res).holds b w := by
  unfold AVal.num
  split
  · simp only [AVal.holds, Bool.false_eq_true, if_false]
    exact ⟨h1, h2, h3⟩
  · exact holds_top b w

theorem holds_const (b w : Word) : (AVal.const w.toInt).holds b w := by
  apply holds_num (Int.le_refl _) (Int.le_refl _)
  intro r hr
  cases hr
  have : 0 ≤ w.toInt % 8 := Int.emod_nonneg _ (by decide)
  omega

theorem holds_flag (b : Word) (k : Option Bool) (c : Bool)
    (hk : ∀ t, k = some t → c = t) :
    (AVal.flag k).holds b (if c then 1 else 0) := by
  cases k with
  | none => cases c <;> exact holds_num (by decide) (by decide) (by simp)
  | some t =>
    cases hk t rfl
    cases c
    · exact holds_const b 0
    · exact holds_const b 1

/-- A signed sum, difference or product that stays within the words is the sum of the values. -/
theorem bmod_small {x : Int} (h1 : wordMin ≤ x) (h2 : x ≤ wordMax) : x.bmod (2 ^ 64) = x := by
  simp only [wordMin, wordMax] at h1 h2
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem holds_add {b w1 w2 : Word} {a c : AVal} (h1 : a.holds b w1) (h2 : c.holds b w2) :
    (add a c).holds b (w1 + w2) := by
  unfold add AVal.holds at *
  cases ha : a.ptr <;> cases hc : c.ptr <;> simp only [ha, hc, if_true, if_false,
    Bool.false_eq_true] at h1 h2 ⊢
  · obtain ⟨l1, u1, r1⟩ := h1
    obtain ⟨l2, u2, r2⟩ := h2
    unfold AVal.num
    split
    · simp only [Bool.false_eq_true, if_false]
      rw [BitVec.toInt_add, bmod_small (by omega) (by omega)]
      refine ⟨by omega, by omega, fun r h => ?_⟩
      unfold addRes at h
      split at h
      · rename_i p q hp hq
        cases h
        have := r1 p hp
        have := r2 q hq
        omega
      · cases h
    · exact holds_top b _
  · obtain ⟨l1, u1, r1⟩ := h1
    obtain ⟨x, l2, u2, e2, r2⟩ := h2
    refine ⟨w1.toInt + x, by omega, by omega, ?_, fun r h => ?_⟩
    · rw [e2, BitVec.ofInt_add, BitVec.ofInt_toInt]
      ac_rfl
    · unfold addRes at h
      split at h
      · rename_i p q hp hq
        cases h
        have := r1 p hp
        have := r2 q hq
        omega
      · cases h
  · obtain ⟨x, l1, u1, e1, r1⟩ := h1
    obtain ⟨l2, u2, r2⟩ := h2
    refine ⟨x + w2.toInt, by omega, by omega, ?_, fun r h => ?_⟩
    · rw [e1, BitVec.ofInt_add, BitVec.ofInt_toInt]
      ac_rfl
    · unfold addRes at h
      split at h
      · rename_i p q hp hq
        cases h
        have := r1 p hp
        have := r2 q hq
        omega
      · cases h
  · exact holds_top b _

theorem holds_sub {b w1 w2 : Word} {a c : AVal} (h1 : a.holds b w1) (h2 : c.holds b w2) :
    (sub a c).holds b (w1 - w2) := by
  unfold sub AVal.holds at *
  cases ha : a.ptr <;> cases hc : c.ptr <;> simp only [ha, hc, if_true, if_false,
    Bool.false_eq_true] at h1 h2 ⊢
  · obtain ⟨l1, u1, r1⟩ := h1
    obtain ⟨l2, u2, r2⟩ := h2
    unfold AVal.num
    split
    · simp only [Bool.false_eq_true, if_false]
      rw [BitVec.toInt_sub, bmod_small (by omega) (by omega)]
      refine ⟨by omega, by omega, fun r h => ?_⟩
      unfold subRes at h
      split at h
      · rename_i p q hp hq
        cases h
        have := r1 p hp
        have := r2 q hq
        omega
      · cases h
    · exact holds_top b _
  · exact holds_top b _
  · obtain ⟨x, l1, u1, e1, r1⟩ := h1
    obtain ⟨l2, u2, r2⟩ := h2
    refine ⟨x - w2.toInt, by omega, by omega, ?_, fun r h => ?_⟩
    · rw [e1, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_toInt]
      rw [BitVec.sub_eq_add_neg]
      ac_rfl
    · unfold subRes at h
      split at h
      · rename_i p q hp hq
        cases h
        have := r1 p hp
        have := r2 q hq
        omega
      · cases h
  · exact holds_top b _

theorem mulRes_sound {x y : Int} {p q : Option Nat} (hx : ∀ r, p = some r → x % 8 = r)
    (hy : ∀ r, q = some r → y % 8 = r) : ∀ r, mulRes p q = some r → (x * y) % 8 = r := by
  intro r h
  unfold mulRes at h
  split at h
  · cases h
    rw [Int.mul_emod, hx 0 rfl]
    simp
  · cases h
    rw [Int.mul_emod, hy 0 rfl]
    simp
  · cases h

theorem holds_scale {b w1 w2 : Word} {a : AVal} {k : Int} {kres : Option Nat}
    (h1 : a.holds b w1) (hp : a.ptr = false) (hk : w2.toInt = k)
    (hr : ∀ r, kres = some r → k % 8 = r) : (scale a k kres).holds b (w1 * w2) := by
  simp only [AVal.holds, hp, Bool.false_eq_true, if_false] at h1
  obtain ⟨l1, u1, r1⟩ := h1
  have res := mulRes_sound r1 hr
  unfold scale AVal.num
  have range := toInt_range (w1 * w2)
  split <;> split
  · rename_i hk0 hin
    simp only [AVal.holds, Bool.false_eq_true, if_false]
    rw [BitVec.toInt_mul, hk]
    have m1 : a.lo * k ≤ w1.toInt * k := Int.mul_le_mul_of_nonneg_right l1 hk0
    have m2 : w1.toInt * k ≤ a.hi * k := Int.mul_le_mul_of_nonneg_right u1 hk0
    rw [bmod_small (by omega) (by omega)]
    exact ⟨m1, m2, res⟩
  · exact holds_top b _
  · rename_i hk0 hin
    simp only [AVal.holds, Bool.false_eq_true, if_false]
    rw [BitVec.toInt_mul, hk]
    have hk' : k ≤ 0 := by omega
    have m1 : a.hi * k ≤ w1.toInt * k := Int.mul_le_mul_of_nonpos_right u1 hk'
    have m2 : w1.toInt * k ≤ a.lo * k := Int.mul_le_mul_of_nonpos_right l1 hk'
    rw [bmod_small (by omega) (by omega)]
    exact ⟨m1, m2, res⟩
  · exact holds_top b _

theorem holds_mul {b w1 w2 : Word} {a c : AVal} (h1 : a.holds b w1) (h2 : c.holds b w2) :
    (mul a c).holds b (w1 * w2) := by
  unfold mul
  split
  · exact holds_top b _
  · rename_i hp
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
    split
    · rename_i he
      have h2' := h2
      simp only [AVal.holds, hp.2, Bool.false_eq_true, if_false] at h2'
      have hk : w2.toInt = c.lo := by omega
      exact holds_scale h1 hp.1 hk (fun r h => hk ▸ h2'.2.2 r h)
    · split
      · rename_i _ he
        have h1' := h1
        simp only [AVal.holds, hp.1, Bool.false_eq_true, if_false] at h1'
        rw [BitVec.mul_comm]
        have hk : w1.toInt = a.lo := by omega
        exact holds_scale h2 hp.2 hk (fun r h => hk ▸ h1'.2.2 r h)
      · exact holds_top b _

theorem toInt_of_nonneg {w : Word} (h : 0 ≤ w.toInt) : w.toInt = w.toNat := by
  have := BitVec.toInt_eq_toNat_cond w
  have hlt := w.isLt
  split at this <;> omega

theorem holds_and {b w1 w2 : Word} {a c : AVal} (h1 : a.holds b w1) (h2 : c.holds b w2) :
    (and_ a c).holds b (w1 &&& w2) := by
  unfold and_
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hpa, hpc⟩, la⟩, lc⟩ := hc
    simp only [AVal.holds, hpa, hpc, Bool.false_eq_true, if_false] at h1 h2
    have e1 := toInt_of_nonneg (by omega : 0 ≤ w1.toInt)
    have e2 := toInt_of_nonneg (by omega : 0 ≤ w2.toInt)
    have n1 : w1.toNat &&& w2.toNat ≤ w1.toNat := Nat.and_le_left
    have n2 : w1.toNat &&& w2.toNat ≤ w2.toNat := Nat.and_le_right
    have r1 := toInt_range w1
    have r2 := toInt_range w2
    simp only [wordMin, wordMax] at r1 r2
    apply holds_num
    · rw [BitVec.toInt_and,
        bmod_small (by simp only [wordMin]; omega) (by simp only [wordMax]; omega)]
      omega
    · rw [BitVec.toInt_and,
        bmod_small (by simp only [wordMin]; omega) (by simp only [wordMax]; omega)]
      omega
    · intro r h
      cases h
  · exact holds_top b _

theorem ltKnown_sound {b w1 w2 : Word} {a c : AVal} (h1 : a.holds b w1) (h2 : c.holds b w2) :
    ∀ t, ltKnown a c = some t → signedLt w1 w2 = t := by
  intro t h
  unfold ltKnown at h
  split at h
  · cases h
  · rename_i hp
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
    simp only [AVal.holds, hp.1, hp.2, Bool.false_eq_true, if_false] at h1 h2
    unfold signedLt
    split at h
    · cases h
      rw [BitVec.slt_eq_decide]
      simp only [decide_eq_true_eq]
      omega
    · split at h
      · cases h
        rw [BitVec.slt_eq_decide]
        simp only [decide_eq_false_iff_not]
        omega
      · cases h

theorem eqKnown_sound {b w1 w2 : Word} {a c : AVal} (h1 : a.holds b w1) (h2 : c.holds b w2) :
    ∀ t, eqKnown a c = some t → decide (w1 = w2) = t := by
  intro t h
  unfold eqKnown at h
  split at h
  · cases h
  · rename_i hp
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
    simp only [AVal.holds, hp.1, hp.2, Bool.false_eq_true, if_false] at h1 h2
    split at h
    · cases h
      rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [decide_eq_true_eq]
      exact BitVec.toInt_inj.mp (by omega)
    · split at h
      · cases h
        rename_i _ hd
        simp only [decide_eq_false_iff_not]
        intro he
        subst he
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hd
        omega
      · cases h

/-! ## States -/

/-- The heap covers `size` bytes from `b`: the word that holds each of its bytes, and each word of
it on a word boundary, is in the program's memory `dm`. -/
def Covers (size : Nat) (dm : Word → Bool) (b : Word) : Prop :=
  (∀ off, off < size → dm (byteAlign (b + BitVec.ofNat 64 off)) = true) ∧
  (∀ off, off < size → off % 8 = 0 → dm (b + BitVec.ofNat 64 off) = true)

/-- Every local the abstract state has in scope is declared, with a value it stands for. -/
def LocalsHold (b : Word) (ls : List (String × AVal)) (locals : String → Option Word) : Prop :=
  ∀ x v, lookup x ls = some v → ∃ w, locals x = some w ∧ v.holds b w

/-- Every cell holds a word its range stands for. -/
def CellsHold (s : PancakeState σ) (cs : List (String × Int × AVal)) : Prop :=
  ∀ x k v, lookupCell x k cs = some v → ∀ p, s.locals x = some p →
    v.holds s.baseAddr (s.memory (p + BitVec.ofInt 64 k))

/-- The runs `A` stands for, in a heap of `size` bytes. -/
def Holds (size : Nat) (A : AState) (s : PancakeState σ) : Prop :=
  Covers size s.memaddrs s.baseAddr ∧ LocalsHold s.baseAddr A.locals s.locals ∧ CellsHold s A.cells

theorem ofInt_of_nonneg {x : Int} (h : 0 ≤ x) : BitVec.ofInt 64 x = BitVec.ofNat 64 x.toNat := by
  rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg h]

theorem byte_in_heap {size : Nat} {dm : Word → Bool} {b w : Word} {p : AVal}
    (hc : Covers size dm b) (hp : p.holds b w) (ok : byteOk size p = true) :
    dm (byteAlign w) = true := by
  simp only [byteOk, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨pp, lo⟩, hi⟩ := ok
  simp only [AVal.holds, pp, if_true] at hp
  obtain ⟨x, l, u, e, _⟩ := hp
  rw [e, ofInt_of_nonneg (by omega)]
  exact hc.1 _ (by omega)

theorem word_in_heap {size : Nat} {dm : Word → Bool} {b w : Word} {p : AVal}
    (hc : Covers size dm b) (hp : p.holds b w) (ok : wordOk size p = true) :
    dm w = true := by
  simp only [wordOk, byteOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok
  obtain ⟨⟨⟨pp, lo⟩, hi⟩, r0⟩ := ok
  simp only [AVal.holds, pp, if_true] at hp
  obtain ⟨x, l, u, e, r⟩ := hp
  have := r 0 r0
  rw [e, ofInt_of_nonneg (by omega)]
  exact hc.2 _ (by omega) (by omega)

theorem holds_byte (b : Word) (y : BitVec 8) :
    (AVal.num 0 255 none).holds b (y.setWidth 64) := by
  have hy := y.isLt
  have e : (y.setWidth 64).toInt = y.toNat := by
    rw [BitVec.toInt_setWidth, bmod_small (by simp only [wordMin]; omega)
      (by simp only [wordMax]; omega)]
  apply holds_num <;> first | omega | (intro r h; cases h)

theorem cellOf_eval {s : PancakeState σ} {a : PancakeExp} {x : String} {k : Int} {w : Word}
    (hc : cellOf a = some (x, k)) (he : eval s a = some w) :
    ∃ p, s.locals x = some p ∧ w = p + BitVec.ofInt 64 k := by
  unfold cellOf at hc
  split at hc
  · cases hc
    exact ⟨w, he, by simp⟩
  · cases hc
    rename_i y c
    simp only [eval] at he
    split at he
    · rename_i p q hp hq
      cases hq
      cases he
      exact ⟨p, hp, by rw [BitVec.ofInt_toInt]⟩
    · cases he
  · cases hc

theorem evalA_sound {size : Nat} {A : AState} {s : PancakeState σ} (h : Holds size A s) :
    ∀ (e : PancakeExp) (v : AVal), evalA size A e = some v →
      ∃ w, eval s e = some w ∧ v.holds s.baseAddr w := by
  intro e
  induction e with
  | const w =>
    intro v hv
    simp only [evalA, Option.some.injEq] at hv
    subst hv
    exact ⟨w, rfl, holds_const _ w⟩
  | var x =>
    intro v hv
    exact h.2.1 x v hv
  | base =>
    intro v hv
    simp only [evalA, Option.some.injEq] at hv
    subst hv
    refine ⟨s.baseAddr, rfl, ?_⟩
    simp only [AVal.holds, if_true]
    exact ⟨0, Int.le_refl _, Int.le_refl _, by simp, fun r hr => by cases hr; rfl⟩
  | op bop l r ihl ihr =>
    intro v hv
    simp only [evalA] at hv
    split at hv
    · rename_i a c hl hr
      obtain ⟨w1, e1, h1⟩ := ihl a hl
      obtain ⟨w2, e2, h2⟩ := ihr c hr
      cases bop <;> simp only [Option.some.injEq] at hv <;> subst hv
      · exact ⟨_, by simp only [eval, e1, e2], holds_add h1 h2⟩
      · exact ⟨_, by simp only [eval, e1, e2], holds_and h1 h2⟩
      · exact ⟨_, by simp only [eval, e1, e2], holds_sub h1 h2⟩
    · cases hv
  | mul l r ihl ihr =>
    intro v hv
    simp only [evalA] at hv
    split at hv
    · rename_i a c hl hr
      obtain ⟨w1, e1, h1⟩ := ihl a hl
      obtain ⟨w2, e2, h2⟩ := ihr c hr
      simp only [Option.some.injEq] at hv
      subst hv
      exact ⟨_, by simp only [eval, e1, e2], holds_mul h1 h2⟩
    · cases hv
  | shiftR l r ihl ihr =>
    intro v hv
    simp only [evalA] at hv
    split at hv
    · rename_i a c hl hr
      obtain ⟨w1, e1, _⟩ := ihl a hl
      obtain ⟨w2, e2, h2⟩ := ihr c hr
      unfold shiftR at hv
      split at hv
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
        obtain ⟨⟨hp, lo⟩, hi⟩ := hc
        simp only [Option.some.injEq] at hv
        subst hv
        simp only [AVal.holds, hp, Bool.false_eq_true, if_false] at h2
        have t := toInt_of_nonneg (w := w2) (by omega)
        refine ⟨w1 >>> w2.toNat, ?_, holds_top _ _⟩
        simp only [eval, e1, e2]
        have : ¬ (w2.toNat ≠ 0 && w2.toNat ≥ 64) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        simp only [this, Bool.false_eq_true, ↓reduceIte]
      · cases hv
    · cases hv
  | cmp c l r ihl ihr =>
    intro v hv
    simp only [evalA] at hv
    split at hv
    · rename_i a d hl hr
      obtain ⟨w1, e1, h1⟩ := ihl a hl
      obtain ⟨w2, e2, h2⟩ := ihr d hr
      cases c <;> simp only [Option.some.injEq] at hv <;> subst hv
      · refine ⟨if signedLt w1 w2 then 1 else 0, by simp only [eval, e1, e2], ?_⟩
        exact holds_flag _ _ _ (ltKnown_sound h1 h2)
      · refine ⟨if w1 = w2 then 1 else 0, by simp only [eval, e1, e2], ?_⟩
        rw [show (if w1 = w2 then (1 : Word) else 0) = if decide (w1 = w2) then 1 else 0 by simp]
        exact holds_flag _ _ _ (eqKnown_sound h1 h2)
      · refine ⟨if signedLt w1 w2 then 0 else 1, by simp only [eval, e1, e2], ?_⟩
        rw [show (if signedLt w1 w2 then (0 : Word) else 1) = if !signedLt w1 w2 then 1 else 0 by
          cases signedLt w1 w2 <;> rfl]
        apply holds_flag
        intro t ht
        simp only [Option.map_eq_some_iff] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        rw [ltKnown_sound h1 h2 u hu]
    · cases hv
  | loadByte a ih =>
    intro v hv
    simp only [evalA] at hv
    split at hv
    · rename_i p hp
      obtain ⟨w, e, hw⟩ := ih p hp
      split at hv
      · rename_i ok
        simp only [Option.some.injEq] at hv
        subst hv
        have hd := byte_in_heap h.1 hw ok
        refine ⟨_, ?_, holds_byte _ (getByte w (s.memory (byteAlign w)) s.be)⟩
        simp only [eval, e, memLoadByte, hd, if_true]
      · cases hv
    · cases hv
  | loadWord a ih =>
    intro v hv
    simp only [evalA] at hv
    split at hv
    · rename_i p hp
      obtain ⟨w, e, hw⟩ := ih p hp
      split at hv
      · rename_i ok
        simp only [Option.some.injEq] at hv
        subst hv
        have hd := word_in_heap h.1 hw ok
        refine ⟨s.memory w, by simp only [eval, e, hd, if_true], ?_⟩
        split
        · rename_i x k hc
          cases hl : lookupCell x k A.cells with
          | none => exact holds_top _ _
          | some u =>
            simp only [Option.getD_some]
            obtain ⟨q, hq, rfl⟩ := cellOf_eval hc e
            exact h.2.2 x k u hl q hq
        · exact holds_top _ _
      · cases hv
    · cases hv

/-! ## Locals and cells -/

theorem lookup_setVar_same {x : String} {v : AVal} :
    ∀ {ls ls' : List (String × AVal)}, setVar x v ls = some ls' → lookup x ls' = some v
  | [], _, h => by cases h
  | (y, w) :: rest, ls', h => by
    unfold setVar at h
    split at h
    · rename_i hxy
      cases h
      simp [lookup, hxy]
    · rename_i hne
      simp only [Option.map_eq_map, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp only [lookup, hne, if_false]
      exact lookup_setVar_same hr

theorem lookup_setVar_other {x y : String} {v : AVal} (hne : y ≠ x) :
    ∀ {ls ls' : List (String × AVal)}, setVar x v ls = some ls' → lookup y ls' = lookup y ls
  | [], _, h => by cases h
  | (z, w) :: rest, ls', h => by
    unfold setVar at h
    split at h
    · cases h
      rename_i hxz
      subst hxz
      simp [lookup, hne]
    · simp only [Option.map_eq_map, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp only [lookup]
      split
      · rfl
      · exact lookup_setVar_other hne hr

theorem setVar_found {x : String} {v : AVal} :
    ∀ {ls ls' : List (String × AVal)}, setVar x v ls = some ls' → ∃ u, lookup x ls = some u
  | [], _, h => by cases h
  | (y, w) :: rest, ls', h => by
    unfold setVar at h
    split at h
    · rename_i hxy
      exact ⟨w, by simp [lookup, hxy]⟩
    · rename_i hne
      simp only [Option.map_eq_map, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      simp only [lookup, hne, if_false]
      exact setVar_found hr

theorem setVar_of_found {x : String} {v : AVal} :
    ∀ {ls : List (String × AVal)} {u : AVal}, lookup x ls = some u → ∃ ls', setVar x v ls = some ls'
  | [], _, h => by cases h
  | (y, w) :: rest, u, h => by
    unfold lookup at h
    unfold setVar
    split
    · exact ⟨_, rfl⟩
    · rename_i hne
      simp only [hne, if_false] at h
      obtain ⟨r, hr⟩ := setVar_of_found (v := v) h
      exact ⟨(y, w) :: r, by simp [hr]⟩

theorem lookup_dropVar_other {x y : String} (hne : y ≠ x) :
    ∀ ls : List (String × AVal), lookup y (dropVar x ls) = lookup y ls
  | [] => rfl
  | (z, w) :: rest => by
    unfold dropVar
    split
    · rename_i hxz
      subst hxz
      simp [lookup, hne]
    · simp only [lookup]
      split
      · rfl
      · exact lookup_dropVar_other hne rest

theorem lookupCell_kill {x y : String} {k : Int} (hne : y ≠ x) :
    ∀ cs : List (String × Int × AVal), lookupCell y k (killCells x cs) = lookupCell y k cs
  | [] => rfl
  | (z, j, v) :: rest => by
    unfold killCells at *
    simp only [List.filter_cons]
    by_cases hz : z = x
    · subst hz
      have : (y = z && k = j) = false := by simp [hne]
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false, lookupCell, this]
      exact lookupCell_kill hne rest
    · have : (z != x) = true := by simp [hz]
      simp only [this, if_true, lookupCell]
      split
      · rfl
      · exact lookupCell_kill hne rest

theorem holds_setLocal {b : Word} {ls ls' : List (String × AVal)} {locals : String → Option Word}
    {x : String} {v : AVal} {w : Word} (h : LocalsHold b ls locals) (hs : setVar x v ls = some ls')
    (hw : v.holds b w) : LocalsHold b ls' (setLocal locals x w) := by
  intro y u hu
  by_cases hy : y = x
  · subst hy
    rw [lookup_setVar_same hs] at hu
    cases hu
    exact ⟨w, by simp [setLocal], hw⟩
  · rw [lookup_setVar_other hy hs] at hu
    obtain ⟨w', e, hw'⟩ := h y u hu
    exact ⟨w', by simp [setLocal, hy, e], hw'⟩

theorem lookupCell_killed (x : String) (k : Int) :
    ∀ cs : List (String × Int × AVal), lookupCell x k (killCells x cs) = none
  | [] => rfl
  | (z, j, v) :: rest => by
    unfold killCells
    simp only [List.filter_cons]
    by_cases hz : z = x
    · subst hz
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      exact lookupCell_killed z k rest
    · have : (z != x) = true := by simp [hz]
      have hxz : (x = z && k = j) = false := by simp [Ne.symm hz]
      simp only [this, if_true, lookupCell, hxz, Bool.false_eq_true, if_false]
      exact lookupCell_killed x k rest

theorem cells_setLocal {s : PancakeState σ} {cs : List (String × Int × AVal)} {x : String}
    {w : Word} (h : CellsHold s cs) :
    CellsHold { s with locals := setLocal s.locals x w } (killCells x cs) := by
  intro y k v hv p hp
  by_cases hy : y = x
  · subst hy
    rw [lookupCell_killed] at hv
    cases hv
  · rw [lookupCell_kill hy] at hv
    simp only [setLocal, hy, if_false] at hp
    exact h y k v hv p hp

theorem holds_empty_cells (s : PancakeState σ) : CellsHold s [] := by
  intro x k v hv
  cases hv

/-! ## Conditions -/

theorem meet_sound {b w : Word} {v : AVal} {lo hi : Int} (hv : v.holds b w) (hp : v.ptr = false)
    (h1 : lo ≤ w.toInt) (h2 : w.toInt ≤ hi) : ∃ v', meet v lo hi = some v' ∧ v'.holds b w := by
  simp only [AVal.holds, hp, Bool.false_eq_true, if_false] at hv
  obtain ⟨l, u, r⟩ := hv
  dsimp only [meet]
  split
  · refine ⟨_, rfl, ?_⟩
    simp only [AVal.holds, hp, Bool.false_eq_true, if_false]
    exact ⟨by omega, by omega, r⟩
  · rename_i hn
    exact absurd (by omega) hn

theorem eval_loadWord_inv {s : PancakeState σ} {a : PancakeExp} {w : Word}
    (h : eval s (.loadWord a) = some w) :
    ∃ q, eval s a = some q ∧ s.memaddrs q = true ∧ w = s.memory q := by
  simp only [eval] at h
  split at h
  · rename_i q hq
    split at h
    · cases h
      exact ⟨q, hq, by assumption, rfl⟩
    · cases h
  · cases h

theorem lookupCell_filter {x y : String} {k j : Int} (hne : ¬ (y = x ∧ j = k)) :
    ∀ cs : List (String × Int × AVal),
      lookupCell y j (cs.filter fun c => !(c.1 = x && c.2.1 = k)) = lookupCell y j cs
  | [] => rfl
  | (z, i, v) :: rest => by
    simp only [List.filter_cons]
    by_cases hz : z = x ∧ i = k
    · obtain ⟨rfl, rfl⟩ := hz
      have hq : (y = z && j = i) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases hy : y = z
        · exact Or.inr fun hj => hne ⟨hy, hj⟩
        · exact Or.inl hy
      simp only [decide_true, Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
        lookupCell, hq]
      exact lookupCell_filter hne rest
    · have : (!(decide (z = x) && decide (i = k))) = true := by
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases hzx : z = x
        · exact Or.inr fun hi => hz ⟨hzx, hi⟩
        · exact Or.inl hzx
      simp only [this, if_true, lookupCell]
      split
      · rfl
      · exact lookupCell_filter hne rest

theorem refine_sound {size : Nat} {A : AState} {s : PancakeState σ} (h : Holds size A s)
    {e : PancakeExp} {w : Word} (he : eval s e = some w) {lo hi : Int}
    (h1 : lo ≤ w.toInt) (h2 : w.toInt ≤ hi) :
    ∃ A', refine size A e lo hi = some A' ∧ Holds size A' s := by
  unfold refine
  split
  · rename_i x
    split
    · rename_i v hv
      split
      · exact ⟨A, rfl, h⟩
      · rename_i hp
        obtain ⟨w', e', hw'⟩ := h.2.1 x v hv
        simp only [eval] at he
        rw [he] at e'
        cases e'
        obtain ⟨v', hm, hv'⟩ := meet_sound hw' (by simpa using hp) h1 h2
        obtain ⟨ls, hs⟩ := setVar_of_found (v := v') hv
        refine ⟨{ A with locals := ls }, by simp [hm, hs], h.1, ?_, h.2.2⟩
        intro y u hu
        by_cases hy : y = x
        · subst hy
          rw [lookup_setVar_same hs] at hu
          cases hu
          exact ⟨w, he, hv'⟩
        · rw [lookup_setVar_other hy hs] at hu
          exact h.2.1 y u hu
    · exact ⟨A, rfl, h⟩
  · rename_i a
    split
    · rename_i x k v hc hv
      split
      · exact ⟨A, rfl, h⟩
      · rename_i hp
        obtain ⟨w', e', hw'⟩ := evalA_sound h _ _ hv
        rw [he] at e'
        cases e'
        obtain ⟨v', hm, hv'⟩ := meet_sound hw' (by simpa using hp) h1 h2
        refine ⟨{ A with cells := (x, k, v') :: A.cells.filter fun c => !(c.1 = x && c.2.1 = k) },
          by rw [hm]; rfl, h.1, h.2.1, ?_⟩
        intro y j u hu p hp'
        by_cases hk : y = x ∧ j = k
        · obtain ⟨rfl, rfl⟩ := hk
          simp only [lookupCell, decide_true, Bool.and_self, if_true, Option.some.injEq] at hu
          subst hu
          obtain ⟨q, hq, _, hw⟩ := eval_loadWord_inv he
          obtain ⟨p', hp'', hq'⟩ := cellOf_eval hc hq
          rw [hp'] at hp''
          cases hp''
          rw [← hq', ← hw]
          exact hv'
        · have hq : (decide (y = x) && decide (j = k)) = false := by
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
            by_cases hy : y = x
            · exact Or.inr fun hj => hk ⟨hy, hj⟩
            · exact Or.inl hy
          simp only [lookupCell, hq, Bool.false_eq_true, if_false] at hu
          rw [lookupCell_filter hk] at hu
          exact h.2.2 y j u hu p hp'
    · exact ⟨A, rfl, h⟩
  · exact ⟨A, rfl, h⟩

theorem eval_less_inv {s : PancakeState σ} {l r : PancakeExp} {w : Word}
    (h : eval s (.cmp .less l r) = some w) : ∃ a b, eval s l = some a ∧ eval s r = some b ∧
      w = if signedLt a b then 1 else 0 := by
  simp only [eval] at h
  split at h
  · rename_i a b ha hb
    cases h
    exact ⟨a, b, ha, hb, rfl⟩
  · cases h

theorem eval_notLess_inv {s : PancakeState σ} {l r : PancakeExp} {w : Word}
    (h : eval s (.cmp .notLess l r) = some w) : ∃ a b, eval s l = some a ∧ eval s r = some b ∧
      w = if signedLt a b then 0 else 1 := by
  simp only [eval] at h
  split at h
  · rename_i a b ha hb
    cases h
    exact ⟨a, b, ha, hb, rfl⟩
  · cases h

theorem eval_equal_inv {s : PancakeState σ} {l r : PancakeExp} {w : Word}
    (h : eval s (.cmp .equal l r) = some w) : ∃ a b, eval s l = some a ∧ eval s r = some b ∧
      w = if a = b then 1 else 0 := by
  simp only [eval] at h
  split at h
  · rename_i a b ha hb
    cases h
    exact ⟨a, b, ha, hb, rfl⟩
  · cases h

theorem assumeLt_sound {size : Nat} {A : AState} {s : PancakeState σ} (h : Holds size A s)
    {a b : PancakeExp} {wa wb : Word} (ha : eval s a = some wa) (hb : eval s b = some wb)
    (t : Bool) (ht : signedLt wa wb = t) :
    ∃ A', assumeLt size A a b t = some A' ∧ Holds size A' s := by
  unfold assumeLt
  split
  · rename_i va vb hva hvb
    obtain ⟨wa', ea, hwa⟩ := evalA_sound h _ _ hva
    obtain ⟨wb', eb, hwb⟩ := evalA_sound h _ _ hvb
    rw [ha] at ea
    rw [hb] at eb
    cases ea
    cases eb
    split
    · exact ⟨A, rfl, h⟩
    · rename_i hp
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
      simp only [AVal.holds, hp.1, hp.2, Bool.false_eq_true, if_false] at hwa hwb
      have ra := toInt_range wa
      have rb := toInt_range wb
      unfold signedLt at ht
      rw [BitVec.slt_eq_decide] at ht
      cases t
      · simp only [decide_eq_false_iff_not] at ht
        simp only [Bool.false_eq_true, if_false]
        obtain ⟨A1, e1, h1⟩ := refine_sound h ha (lo := vb.lo) (hi := wordMax) (by omega) ra.2
        obtain ⟨A2, e2, h2⟩ := refine_sound h1 hb (lo := wordMin) (hi := va.hi) rb.1 (by omega)
        exact ⟨A2, by simp [e1, e2], h2⟩
      · simp only [decide_eq_true_eq] at ht
        simp only [if_true]
        obtain ⟨A1, e1, h1⟩ := refine_sound h ha (lo := wordMin) (hi := vb.hi - 1) ra.1 (by omega)
        obtain ⟨A2, e2, h2⟩ := refine_sound h1 hb (lo := va.lo + 1) (hi := wordMax) (by omega) rb.2
        exact ⟨A2, by simp [e1, e2], h2⟩
  · exact ⟨A, rfl, h⟩

theorem assumeEq_sound {size : Nat} {A : AState} {s : PancakeState σ} (h : Holds size A s)
    {a b : PancakeExp} {w : Word} (ha : eval s a = some w) (hb : eval s b = some w) :
    ∃ A', assumeEq size A a b = some A' ∧ Holds size A' s := by
  unfold assumeEq
  split
  · rename_i va vb hva hvb
    obtain ⟨wa', ea, hwa⟩ := evalA_sound h _ _ hva
    obtain ⟨wb', eb, hwb⟩ := evalA_sound h _ _ hvb
    rw [ha] at ea
    rw [hb] at eb
    cases ea
    cases eb
    split
    · exact ⟨A, rfl, h⟩
    · rename_i hp
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
      simp only [AVal.holds, hp.1, hp.2, Bool.false_eq_true, if_false] at hwa hwb
      obtain ⟨A1, e1, h1⟩ := refine_sound h ha (lo := vb.lo) (hi := vb.hi) (by omega) (by omega)
      obtain ⟨A2, e2, h2⟩ := refine_sound h1 hb (lo := va.lo) (hi := va.hi) (by omega) (by omega)
      exact ⟨A2, by simp [e1, e2], h2⟩
  · exact ⟨A, rfl, h⟩
theorem eval_add_inv {s : PancakeState σ} {l r : PancakeExp} {w : Word}
    (h : eval s (.op .add l r) = some w) :
    ∃ a b, eval s l = some a ∧ eval s r = some b ∧ w = a + b := by
  simp only [eval] at h
  split at h
  · rename_i a b ha hb
    cases h
    exact ⟨a, b, ha, hb, rfl⟩
  · cases h

theorem eval_and_inv {s : PancakeState σ} {l r : PancakeExp} {w : Word}
    (h : eval s (.op .and_ l r) = some w) :
    ∃ a b, eval s l = some a ∧ eval s r = some b ∧ w = a &&& b := by
  simp only [eval] at h
  split at h
  · rename_i a b ha hb
    cases h
    exact ⟨a, b, ha, hb, rfl⟩
  · cases h

theorem toInt_eq_zero {w : Word} : w.toInt = 0 ↔ w = 0 := by
  rw [← BitVec.toInt_inj]
  simp

theorem flag_word {b w : Word} {v : AVal} (hv : v.holds b w) (hf : isFlag v = true) :
    0 ≤ w.toInt ∧ w.toInt ≤ 1 := by
  simp only [isFlag, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hf
  obtain ⟨⟨hp, lo⟩, hi⟩ := hf
  simp only [AVal.holds, hp, Bool.false_eq_true, if_false] at hv
  omega

theorem assume_sound {size : Nat} {s : PancakeState σ} :
    ∀ (A : AState) (e : PancakeExp) (t : Bool), Holds size A s → ∀ w, eval s e = some w →
      decide (w ≠ 0) = t → ∃ A', assume size A e t = some A' ∧ Holds size A' s := by
  intro A e t
  fun_induction assume size A e t with
  | case1 A z a b va vb hvb hva hc ih2 ih1 =>
    intro hA w hw ht
    obtain ⟨wz, wab, ez, eab, rfl⟩ := eval_less_inv hw
    obtain ⟨wa, wb, ea, eb, rfl⟩ := eval_add_inv eab
    simp only [eval, Option.some.injEq] at ez
    subst ez
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨rfl, fa⟩, fb⟩ := hc
    obtain ⟨wa', ea', hwa⟩ := evalA_sound hA _ _ hva
    obtain ⟨wb', eb', hwb⟩ := evalA_sound hA _ _ hvb
    rw [ea] at ea'
    rw [eb] at eb'
    cases ea'
    cases eb'
    have ra := flag_word hwa fa
    have rb := flag_word hwb fb
    have hsum : (wa + wb).toInt = wa.toInt + wb.toInt := by
      rw [BitVec.toInt_add,
        bmod_small (by simp only [wordMin]; omega) (by simp only [wordMax]; omega)]
    have hlt : signedLt 0 (wa + wb) = false := by
      revert ht
      cases signedLt 0 (wa + wb) <;> simp
    unfold signedLt at hlt
    rw [BitVec.slt_eq_decide] at hlt
    simp only [decide_eq_false_iff_not] at hlt
    have z0 : BitVec.toInt (0 : Word) = 0 := rfl
    have za : wa = 0 := toInt_eq_zero.mp (by omega)
    have zb : wb = 0 := toInt_eq_zero.mp (by omega)
    obtain ⟨A1, e1, h1⟩ := ih2 hA wa ea (by simp [za])
    obtain ⟨A2, e2, h2⟩ := ih1 A1 h1 wb eb (by simp [zb])
    exact ⟨A2, by simp [e1, e2], h2⟩
  | case2 => intro hA; exact fun _ _ _ => ⟨_, rfl, hA⟩
  | case3 => intro hA; exact fun _ _ _ => ⟨_, rfl, hA⟩
  | case4 A a b =>
    intro hA w hw ht
    obtain ⟨wi, wz, ei, ez, rfl⟩ := eval_equal_inv hw
    obtain ⟨wa, wb, ea, eb, rfl⟩ := eval_equal_inv ei
    simp only [eval, Option.some.injEq] at ez
    subst ez
    have heq : wa = wb := by
      by_cases hne : wa = wb
      · exact hne
      · simp [hne] at ht
    subst heq
    exact assumeEq_sound hA ea eb
  | case5 => intro hA; exact fun _ _ _ => ⟨_, rfl, hA⟩
  | case6 A a b va vb hvb hva hc ih2 ih1 =>
    intro hA w hw ht
    obtain ⟨wa, wb, ea, eb, rfl⟩ := eval_and_inv hw
    simp only [Bool.and_eq_true] at hc
    obtain ⟨wa', ea', hwa⟩ := evalA_sound hA _ _ hva
    obtain ⟨wb', eb', hwb⟩ := evalA_sound hA _ _ hvb
    rw [ea] at ea'
    rw [eb] at eb'
    cases ea'
    cases eb'
    have ra := flag_word hwa hc.1
    have rb := flag_word hwb hc.2
    simp only [ne_eq, decide_eq_true_eq] at ht
    have na : wa ≠ 0 := by
      intro z
      apply ht
      rw [z]
      exact BitVec.zero_and
    have nb : wb ≠ 0 := by
      intro z
      apply ht
      rw [z]
      exact BitVec.and_zero
    obtain ⟨A1, e1, h1⟩ := ih2 hA wa ea (by simpa using na)
    obtain ⟨A2, e2, h2⟩ := ih1 A1 h1 wb eb (by simpa using nb)
    exact ⟨A2, by simp [e1, e2], h2⟩
  | case7 => intro hA; exact fun _ _ _ => ⟨_, rfl, hA⟩
  | case8 => intro hA; exact fun _ _ _ => ⟨_, rfl, hA⟩
  | case9 A a b t =>
    intro hA w hw ht
    obtain ⟨wa, wb, ea, eb, rfl⟩ := eval_less_inv hw
    refine assumeLt_sound hA ea eb t ?_
    cases hs : signedLt wa wb <;> simp [hs] at ht <;> simp [ht]
  | case10 A a b t =>
    intro hA w hw ht
    obtain ⟨wa, wb, ea, eb, rfl⟩ := eval_notLess_inv hw
    refine assumeLt_sound hA ea eb (!t) ?_
    cases hs : signedLt wa wb <;> simp [hs] at ht <;> simp [← ht]
  | case11 A a b =>
    intro hA w hw ht
    obtain ⟨wa, wb, ea, eb, rfl⟩ := eval_equal_inv hw
    have heq : wa = wb := by
      by_cases hne : wa = wb
      · exact hne
      · simp [hne] at ht
    subst heq
    exact assumeEq_sound hA ea eb
  | case12 => intro hA; exact fun _ _ _ => ⟨_, rfl, hA⟩
  | case13 A e _ _ p hp hnp hz =>
    intro hA w hw ht
    obtain ⟨w', e', hw'⟩ := evalA_sound hA _ _ hp
    rw [hw] at e'
    cases e'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
    simp only [Bool.not_eq_true] at hnp
    simp only [AVal.holds, hnp, Bool.false_eq_true, if_false] at hw'
    have : w = 0 := toInt_eq_zero.mp (by omega)
    simp [this] at ht
  | case14 A e _ _ p hp hnp _ hlo =>
    intro hA w hw ht
    obtain ⟨w', e', hw'⟩ := evalA_sound hA _ _ hp
    rw [hw] at e'
    cases e'
    simp only [Bool.not_eq_true] at hnp
    simp only [AVal.holds, hnp, Bool.false_eq_true, if_false] at hw'
    simp only [ne_eq, decide_eq_true_eq] at ht
    have hne : w.toInt ≠ 0 := fun z => ht (toInt_eq_zero.mp z)
    exact refine_sound hA hw (by omega) (toInt_range w).2
  | case15 => intro hA; exact fun _ _ _ => ⟨_, rfl, hA⟩
  | case16 A e t _ _ _ _ _ _ p hp hnp hf =>
    intro hA w hw ht
    have : w = 0 := by
      cases t
      · simpa using ht
      · exact absurd rfl hf
    subst this
    exact refine_sound hA hw (by simp) (by simp)
  | case17 => intro hA; exact fun _ _ _ => ⟨_, rfl, hA⟩

/-! ## Order -/

theorem le_sound {b w : Word} {a c : AVal} (hle : a.le c = true) (h : a.holds b w) :
    c.holds b w := by
  unfold AVal.le at hle
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    beq_iff_eq, Option.isNone_iff_eq_none] at hle
  rcases hle with ⟨⟨⟨hp, hlo⟩, hhi⟩, hr⟩ | ⟨⟨⟨hp, hlo⟩, hhi⟩, hr⟩
  · have := toInt_range w
    simp only [AVal.holds, hp, Bool.false_eq_true, if_false, hr, reduceCtorEq, false_implies,
      implies_true, and_true]
    omega
  · unfold AVal.holds at h ⊢
    rw [← hp]
    split
    · rename_i hpa
      simp only [hpa, if_true] at h
      obtain ⟨x, l, u, e, r⟩ := h
      refine ⟨x, by omega, by omega, e, fun q hq => ?_⟩
      rcases hr with hr | hr
      · rw [hr] at hq
        cases hq
      · rw [hr] at hq
        exact r q hq
    · rename_i hpa
      simp only [hpa, Bool.false_eq_true, if_false] at h
      obtain ⟨l, u, r⟩ := h
      refine ⟨by omega, by omega, fun q hq => ?_⟩
      rcases hr with hr | hr
      · rw [hr] at hq
        cases hq
      · rw [hr] at hq
        exact r q hq

theorem join_left {b w : Word} {a c : AVal} (h : a.holds b w) : (a.join c).holds b w := by
  unfold AVal.join
  split
  · rename_i hp
    simp only [beq_iff_eq] at hp
    unfold AVal.holds at h ⊢
    simp only
    split
    · rename_i hpa
      simp only [hpa, if_true] at h
      obtain ⟨x, l, u, e, r⟩ := h
      refine ⟨x, by omega, by omega, e, fun q hq => ?_⟩
      split at hq
      · exact r q hq
      · cases hq
    · rename_i hpa
      simp only [hpa, Bool.false_eq_true, if_false] at h
      obtain ⟨l, u, r⟩ := h
      refine ⟨by omega, by omega, fun q hq => ?_⟩
      split at hq
      · exact r q hq
      · cases hq
  · exact holds_top b w

theorem join_right {b w : Word} {a c : AVal} (h : c.holds b w) : (a.join c).holds b w := by
  unfold AVal.join
  split
  · rename_i hp
    simp only [beq_iff_eq] at hp
    unfold AVal.holds at h ⊢
    simp only
    split
    · rename_i hpa
      rw [hp] at hpa
      simp only [hpa, if_true] at h
      obtain ⟨x, l, u, e, r⟩ := h
      refine ⟨x, by omega, by omega, e, fun q hq => ?_⟩
      split at hq
      · rename_i heq
        simp only [beq_iff_eq] at heq
        rw [heq] at hq
        exact r q hq
      · cases hq
    · rename_i hpa
      rw [hp] at hpa
      simp only [hpa, Bool.false_eq_true, if_false] at h
      obtain ⟨l, u, r⟩ := h
      refine ⟨by omega, by omega, fun q hq => ?_⟩
      split at hq
      · rename_i heq
        simp only [beq_iff_eq] at heq
        rw [heq] at hq
        exact r q hq
      · cases hq
  · exact holds_top b w

theorem localsLe_lookup {x : String} :
    ∀ {l1 l2 : List (String × AVal)} {v2 : AVal}, localsLe l1 l2 = true →
      lookup x l2 = some v2 → ∃ v1, lookup x l1 = some v1 ∧ v1.le v2 = true
  | [], [], _, _, h2 => by cases h2
  | (y, a) :: r, (z, c) :: s, v2, hle, h2 => by
    simp only [localsLe, Bool.and_eq_true, decide_eq_true_eq] at hle
    obtain ⟨⟨rfl, hac⟩, hrs⟩ := hle
    simp only [lookup] at h2 ⊢
    split
    · rename_i hx
      simp only [hx, if_true, Option.some.injEq] at h2
      subst h2
      exact ⟨a, rfl, hac⟩
    · rename_i hx
      simp only [hx, if_false] at h2
      exact localsLe_lookup hrs h2
  | [], _ :: _, _, hle, _ => by simp [localsLe] at hle
  | _ :: _, [], _, hle, _ => by simp [localsLe] at hle

theorem localsMap_lookup {f : AVal → AVal → AVal} {x : String} :
    ∀ {l1 l2 l3 : List (String × AVal)} {v3 : AVal}, localsMap f l1 l2 = some l3 →
      lookup x l3 = some v3 →
      ∃ v1 v2, lookup x l1 = some v1 ∧ lookup x l2 = some v2 ∧ v3 = f v1 v2
  | [], [], l3, _, hm, h3 => by
    simp only [localsMap, Option.some.injEq] at hm
    subst hm
    cases h3
  | (y, a) :: r, (z, c) :: s, l3, v3, hm, h3 => by
    simp only [localsMap] at hm
    split at hm
    · rename_i hyz
      subst hyz
      simp only [Option.map_eq_map, Option.map_eq_some_iff] at hm
      obtain ⟨l, hl, rfl⟩ := hm
      simp only [lookup] at h3 ⊢
      split
      · rename_i hx
        simp only [hx, if_true, Option.some.injEq] at h3
        exact ⟨a, c, rfl, rfl, h3.symm⟩
      · rename_i hx
        simp only [hx, if_false] at h3
        exact localsMap_lookup hl h3
    · cases hm
  | [], _ :: _, _, _, hm, _ => by simp [localsMap] at hm
  | _ :: _, [], _, _, hm, _ => by simp [localsMap] at hm

theorem lookupCell_mem {x : String} {k : Int} :
    ∀ {cs : List (String × Int × AVal)} {v : AVal}, lookupCell x k cs = some v → (x, k, v) ∈ cs
  | [], _, h => by cases h
  | (y, j, u) :: rest, v, h => by
    simp only [lookupCell] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupCell_mem h)

theorem cellsJoin_lookup {x : String} {k : Int} {D : List (String × Int × AVal)} :
    ∀ {C : List (String × Int × AVal)} {v : AVal}, lookupCell x k (cellsJoin C D) = some v →
      ∃ u u', lookupCell x k C = some u ∧ lookupCell x k D = some u' ∧ v = u.join u'
  | [], _, h => by cases h
  | (y, j, u) :: rest, v, h => by
    unfold cellsJoin at h
    simp only [List.filterMap_cons] at h
    cases hd : lookupCell y j D with
    | none =>
      simp only [hd, Option.map_none] at h
      obtain ⟨u1, u2, h1, h2, rfl⟩ := cellsJoin_lookup h
      refine ⟨u1, u2, ?_, h2, rfl⟩
      simp only [lookupCell]
      split
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        rw [hd] at h2
        cases h2
      · exact h1
    | some u' =>
      simp only [hd, Option.map_some] at h
      simp only [lookupCell] at h ⊢
      split
      · rename_i hc
        simp only [hc, if_true, Option.some.injEq] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨u, u', rfl, hd, h.symm⟩
      · rename_i hc
        simp only [hc, Bool.false_eq_true, if_false] at h
        exact cellsJoin_lookup h

theorem le_holds {size : Nat} {A B : AState} {s : PancakeState σ} (hle : A.le B = true)
    (h : Holds size A s) : Holds size B s := by
  simp only [AState.le, Bool.and_eq_true, List.all_eq_true] at hle
  refine ⟨h.1, fun x v hv => ?_, fun x k v hv p hp => ?_⟩
  · obtain ⟨v1, h1, hl⟩ := localsLe_lookup hle.1 hv
    obtain ⟨w, e, hw⟩ := h.2.1 x v1 h1
    exact ⟨w, e, le_sound hl hw⟩
  · have := hle.2 _ (lookupCell_mem hv)
    simp only at this
    split at this
    · rename_i u hu
      exact le_sound this (h.2.2 x k u hu p hp)
    · cases this

theorem join_holds {size : Nat} {A B J : AState} {s : PancakeState σ} (hj : A.join B = some J)
    (h : Holds size A s ∨ Holds size B s) : Holds size J s := by
  simp only [AState.join, Option.map_eq_some_iff] at hj
  obtain ⟨ls, hls, rfl⟩ := hj
  have hc : Covers size s.memaddrs s.baseAddr := by rcases h with h | h <;> exact h.1
  refine ⟨hc, fun x v hv => ?_, fun x k v hv p hp => ?_⟩
  · obtain ⟨v1, v2, h1, h2, rfl⟩ := localsMap_lookup hls hv
    rcases h with h | h
    · obtain ⟨w, e, hw⟩ := h.2.1 x v1 h1
      exact ⟨w, e, join_left hw⟩
    · obtain ⟨w, e, hw⟩ := h.2.1 x v2 h2
      exact ⟨w, e, join_right hw⟩
  · obtain ⟨u1, u2, h1, h2, rfl⟩ := cellsJoin_lookup hv
    rcases h with h | h
    · exact join_left (h.2.2 x k u1 h1 p hp)
    · exact join_right (h.2.2 x k u2 h2 p hp)

/-! ## Statements -/

/-- The state a statement ends normally in, if it can: one the abstract result stands for. -/
def Post (size : Nat) (out : Option AState) (t : PancakeState σ) : Prop :=
  ∃ B, out = some B ∧ Holds size B t

theorem holds_clockFree (size : Nat) (A : AState) : ClockFree (σ := σ) (Holds size A) :=
  fun _ _ h => h

theorem post_clockFree (size : Nat) (out : Option AState) : ClockFree (σ := σ) (Post size out) :=
  fun _ _ h => h

theorem valOf_ok {size : Nat} {A : AState} {e : PancakeExp} {what : String} {v : AVal}
    (h : valOf size A e what = .ok v) : evalA size A e = some v := by
  unfold valOf at h
  split at h
  · cases h
    assumption
  · cases h

theorem need_ok {b : Bool} {why : Alarm} (h : need b why = .ok ()) : b = true := by
  unfold need at h
  split at h
  · assumption
  · cases h

theorem eval_of {size : Nat} {A : AState} {s : PancakeState σ} (h : Holds size A s)
    {e : PancakeExp} {what : String} {v : AVal} (hv : valOf size A e what = .ok v) :
    ∃ w, eval s e = some w ∧ v.holds s.baseAddr w :=
  evalA_sound h e v (valOf_ok hv)

/-- The cells of the other locals stay as they were when only `x` changes. -/
theorem cells_locals {s : PancakeState σ} {cs : List (String × Int × AVal)} {x : String}
    {locals : String → Option Word} (h : CellsHold s cs)
    (hsame : ∀ y, y ≠ x → locals y = s.locals y) :
    CellsHold { s with locals := locals } (killCells x cs) := by
  intro y k v hv p hp
  by_cases hy : y = x
  · subst hy
    rw [lookupCell_killed] at hv
    cases hv
  · rw [lookupCell_kill hy] at hv
    simp only at hp
    rw [hsame y hy] at hp
    exact h y k v hv p hp

theorem readByteArray_some (m : Word → Word) (dm : Word → Bool) (be : Bool) :
    ∀ (n : Nat) (a : Word), (∀ i, i < n → dm (byteAlign (a + BitVec.ofNat 64 i)) = true) →
      ∃ bs, readByteArray m dm be a n = some bs
  | 0, _, _ => ⟨[], rfl⟩
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    obtain ⟨bs, hbs⟩ := readByteArray_some m dm be n (a + 1) fun i hi => by
      have := h (i + 1) (by omega)
      rw [show a + 1 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) by
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        have one : (1 : Word).toNat = 1 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, one]
        omega]
      exact this
    refine ⟨getByte a (m (byteAlign a)) be :: bs, ?_⟩
    simp only [readByteArray, memLoadByte, h0, if_true, hbs]

theorem array_readable {size : Nat} {dm : Word → Bool} {b wp wl : Word} {p l : AVal}
    (m : Word → Word) (be : Bool) (hc : Covers size dm b) (hp : p.holds b wp) (hl : l.holds b wl)
    (ok : arrayOk size p l = true) : ∃ bs, readByteArray m dm be wp wl.toNat = some bs := by
  simp only [arrayOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨pp, plo⟩, lp⟩, llo⟩, fit⟩ := ok
  simp only [AVal.holds, pp, if_true] at hp
  simp only [AVal.holds, lp, Bool.false_eq_true, if_false] at hl
  obtain ⟨x, xl, xu, e, _⟩ := hp
  have tl := toInt_of_nonneg (w := wl) (by omega)
  apply readByteArray_some
  intro i hi
  rw [e, ofInt_of_nonneg (by omega), BitVec.add_assoc]
  rw [show BitVec.ofNat 64 x.toNat + BitVec.ofNat 64 i = BitVec.ofNat 64 (x.toNat + i) by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega]
  exact hc.1 _ (by omega)

theorem search_spec {size : Nat} {e : PancakeExp} {step : AState → Out} :
    ∀ (n : Nat) (X I : AState) (post : Option AState), search size e step n X = .ok (I, post) →
      step I = .ok post
  | 0, X, I, post, h => by
    simp only [search, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      cases h
      exact hr
  | n + 1, X, I, post, h => by
    simp only [search, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
        exact hr
      · split at h
        · cases h
          exact hr
        · split at h
          · cases h
          · split at h
            · exact search_spec n _ I post h
            · split at h
              · cases h
              · exact search_spec n _ I post h

theorem loop_spec {size : Nat} {e : PancakeExp} {body : AState → Out} {A : AState}
    {out : Option AState} (h : loop size e body A = .ok out) :
    ∃ I post, branch size e true body I = .ok post ∧ A.le I = true ∧
      (∃ v, evalA size I e = some v) ∧ leOpt post I = true ∧ out = assume size I e false := by
  simp only [loop, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r1 h1
    obtain ⟨I, post⟩ := r1
    simp only at h
    split at h
    · cases h
    · rename_i u hle
      split at h
      · cases h
      · rename_i v hv
        split at h
        · cases h
        · rename_i u' hlp
          cases h
          exact ⟨I, post, search_spec searchFuel A I post h1, need_ok hle, ⟨v, valOf_ok hv⟩,
            need_ok hlp, rfl⟩

theorem safe_false (o : Oracle σ) (p : PancakeProg) (Q : PancakeState σ → Prop) :
    Safe o (fun _ => False) p Q := fun _ h => h.elim

theorem post_none (o : Oracle σ) (p : PancakeProg) (size : Nat) (Q : PancakeState σ → Prop) :
    Safe o (Post size none) p Q := fun _ h => by
  obtain ⟨B, hB, _⟩ := h
  cases hB

theorem holds_store {size : Nat} {A : AState} {s : PancakeState σ} (h : Holds size A s)
    (m : Word → Word) : Holds size { A with cells := [] } { s with memory := m } :=
  ⟨h.1, h.2.1, holds_empty_cells _⟩

theorem joinOuts_up {o1 o2 out : Option AState} (h : joinOuts o1 o2 = .ok out) :
    (∀ size (t : PancakeState σ), Post size o1 t → Post size out t) ∧
      (∀ size (t : PancakeState σ), Post size o2 t → Post size out t) := by
  unfold joinOuts at h
  split at h
  · rename_i B1 B2
    split at h
    · rename_i B hj
      cases h
      exact ⟨fun _ _ ⟨_, e, hB1⟩ => by cases e; exact ⟨B, rfl, join_holds hj (.inl hB1)⟩,
        fun _ _ ⟨_, e, hB2⟩ => by cases e; exact ⟨B, rfl, join_holds hj (.inr hB2)⟩⟩
    · cases h
  · rename_i hne
    cases h
    constructor
    · intro _ _ ⟨B1, e, hB1⟩
      subst e
      cases o2 with
      | none => exact ⟨B1, rfl, hB1⟩
      | some B2 => exact absurd rfl (hne B1 B2 rfl)
    · intro _ _ ⟨B2, e, hB2⟩
      subst e
      cases o1 with
      | none => exact ⟨B2, rfl, hB2⟩
      | some B1 => exact absurd rfl (hne B1 B2 rfl)

/-- A branch the analysis accepts, run from a state in which its condition has the value that
leads to it, comes to what the whole statement may end in. -/
theorem branch_safe {o : Oracle σ} {size : Nat} {A : AState} {e : PancakeExp} {t : Bool}
    {c : PancakeProg} {ob out : Option AState} {s : PancakeState σ} {w : Word}
    (ih : ∀ (A : AState) (out : Option AState), analyze size A c = .ok out →
      Safe o (Holds size A) c (Post size out))
    (hb : branch size e t (fun X => analyze size X c) A = .ok ob) (hs : Holds size A s)
    (ew : eval s e = some w) (hw : decide (w ≠ 0) = t)
    (up : ∀ size (t : PancakeState σ), Post size ob t → Post size out t) :
    Ok (Post size out) (PancakeSem o c s) := by
  obtain ⟨G, hG, hsG⟩ := assume_sound A e t hs w ew hw
  simp only [branch, hG] at hb
  have k := ih G ob hb s hsG
  revert k
  cases PancakeSem o c s with
  | mk r t =>
    cases r with
    | none => exact up size t
    | some _ => exact id

/-- **A statement the analysis accepts never errs**: from every state the abstract one stands
for, a run ends as a run may end, or finishes normally in a state the result stands for. -/
theorem analyze_safe (o : Oracle σ) (size : Nat) :
    ∀ (p : PancakeProg) (A : AState) (out : Option AState), analyze size A p = .ok out →
      Safe o (Holds size A) p (Post size out) := by
  intro p
  induction p with
  | skip =>
    intro A out h
    simp only [analyze] at h
    cases h
    exact Safe.conseq (Safe.skip o _) (fun _ h => h) (fun _ h => ⟨A, rfl, h⟩)
  | dec x e c ih =>
    intro A out h
    simp only [analyze, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · cases h
      · rename_i r hr
        have inner := ih _ r hr
        apply Safe.dec
          (P' := Holds size { locals := (x, v) :: A.locals, cells := killCells x A.cells })
          (Q' := Post size r)
        · intro s hs
          obtain ⟨w, ew, hw⟩ := eval_of hs hv
          refine ⟨w, ew, hs.1, fun y u hu => ?_, cells_locals hs.2.2 fun y hy => by
            simp [setLocal, hy]⟩
          simp only [lookup] at hu
          split at hu
          · rename_i hy
            cases hu
            exact ⟨w, by simp [setLocal, hy], hw⟩
          · rename_i hy
            obtain ⟨w', e', hw'⟩ := hs.2.1 y u hu
            exact ⟨w', by simp [setLocal, hy, e'], hw'⟩
        · exact inner
        · intro s t _ ht
          obtain ⟨B, rfl, hB⟩ := ht
          simp only at h
          split at h
          · cases h
          · rename_i u hn
            cases h
            have hnone := need_ok hn
            simp only [Option.isNone_iff_eq_none] at hnone
            refine ⟨_, rfl, hB.1, fun y u hu => ?_, cells_locals hB.2.2 fun y hy => by
              simp [resVar, hy]⟩
            have hy : y ≠ x := by
              intro hyx
              subst hyx
              rw [hnone] at hu
              cases hu
            rw [lookup_dropVar_other hy] at hu
            obtain ⟨w, e', hw⟩ := hB.2.1 y u hu
            exact ⟨w, by simp [resVar, hy, e'], hw⟩
  | assign x e =>
    intro A out h
    simp only [analyze, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · rename_i ls hls
        cases h
        apply Safe.assign
        intro s hs
        obtain ⟨w, ew, hw⟩ := eval_of hs hv
        obtain ⟨u, hu⟩ := setVar_found hls
        obtain ⟨old, eold, _⟩ := hs.2.1 x u hu
        exact ⟨w, old, ew, eold, _, rfl, hs.1, holds_setLocal hs.2.1 hls hw,
          cells_setLocal hs.2.2⟩
      · cases h
  | store d e =>
    intro A out h
    simp only [analyze, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p hp
      split at h
      · cases h
      · rename_i v hv
        split at h
        · cases h
        · rename_i u hok
          cases h
          apply Safe.store
          intro s hs
          obtain ⟨a, ea, ha⟩ := eval_of hs hp
          obtain ⟨w, ew, _⟩ := eval_of hs hv
          have hd := word_in_heap hs.1 ha (need_ok hok)
          exact ⟨a, w, fun k => if k = a then w else s.memory k, ea, ew,
            by simp [memStoreWord, hd], _, rfl, holds_store hs _⟩
  | storeByte d e =>
    intro A out h
    simp only [analyze, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p hp
      split at h
      · cases h
      · rename_i v hv
        split at h
        · cases h
        · rename_i u hok
          cases h
          apply Safe.storeByte
          intro s hs
          obtain ⟨a, ea, ha⟩ := eval_of hs hp
          obtain ⟨w, ew, _⟩ := eval_of hs hv
          have hd := byte_in_heap hs.1 ha (need_ok hok)
          exact ⟨a, w, fun k => if k = byteAlign a then
              setByte a (w.setWidth 8) (s.memory (byteAlign a)) s.be else s.memory k, ea, ew,
            by simp [memStoreByte, hd], _, rfl, holds_store hs _⟩
  | extCall name c cl a al =>
    intro A out h
    simp only [analyze, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i cp hcp
      split at h
      · cases h
      · rename_i clv hclv
        split at h
        · cases h
        · rename_i ap hap
          split at h
          · cases h
          · rename_i alv halv
            split at h
            · cases h
            · rename_i u hok
              cases h
              have ok := need_ok hok
              simp only [Bool.and_eq_true] at ok
              apply Safe.extCall
              intro s hs
              obtain ⟨wc, ec, hc⟩ := eval_of hs hcp
              obtain ⟨wcl, ecl, hcl⟩ := eval_of hs hclv
              obtain ⟨wa, ea, ha⟩ := eval_of hs hap
              obtain ⟨wal, eal, hal⟩ := eval_of hs halv
              obtain ⟨conf, hconf⟩ := array_readable s.memory s.be hs.1 hc hcl ok.1
              obtain ⟨arr, harr⟩ := array_readable s.memory s.be hs.1 ha hal ok.2
              exact ⟨wc, wcl, wa, wal, conf, arr, ec, ecl, ea, eal, hconf, harr,
                fun _ _ _ => ⟨_, rfl, hs.1, hs.2.1, holds_empty_cells _⟩⟩
  | seq c1 c2 ih1 ih2 =>
    intro A out h
    simp only [analyze, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      apply Safe.seq (ih1 A r hr) _ (post_clockFree size r)
      split at h
      · cases h
        exact post_none o c2 size _
      · rename_i B
        intro s hs
        obtain ⟨B', hB', hsB⟩ := hs
        cases hB'
        exact ih2 B out h s hsB
  | cond e c1 c2 ih1 ih2 =>
    intro A out h
    simp only [analyze, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · cases h
      · rename_i o1 ho1
        split at h
        · cases h
        · rename_i o2 ho2
          obtain ⟨up1, up2⟩ := joinOuts_up h
          apply Safe.cond
          · intro s hs
            obtain ⟨w, ew, _⟩ := eval_of hs hv
            exact ⟨w, ew⟩
          · intro s ⟨hs, hne⟩
            obtain ⟨w, ew, _⟩ := eval_of hs hv
            have hw : decide (w ≠ 0) = true := by
              simp only [ne_eq, decide_eq_true_eq]
              intro z
              exact hne (by rw [ew, z])
            exact branch_safe ih1 ho1 hs ew hw up1
          · intro s ⟨hs, hz⟩
            exact branch_safe ih2 ho2 hs hz (by decide) up2
  | while_ e c ih =>
    intro A out h
    simp only [analyze] at h
    obtain ⟨I, post, hinto, hle, ⟨v, hv⟩, hlp, rfl⟩ := loop_spec h
    have body : Safe o (fun s => Holds size I s ∧ eval s e ≠ some 0) c (Holds size I) := by
      intro s ⟨hs, hne⟩
      obtain ⟨w, ew, _⟩ := evalA_sound hs e v hv
      have hw : decide (w ≠ 0) = true := by
        simp only [ne_eq, decide_eq_true_eq]
        intro z
        exact hne (by rw [ew, z])
      obtain ⟨G, hG, hsG⟩ := assume_sound I e true hs w ew hw
      simp only [branch, hG] at hinto
      have k := ih G post hinto s hsG
      revert k
      cases PancakeSem o c s with
      | mk r t =>
        cases r with
        | none =>
          intro ⟨B, hB, hsB⟩
          subst hB
          simp only [leOpt] at hlp
          exact le_holds hlp hsB
        | some _ => exact id
    have loopI := Safe.while_ (fun s hs => (evalA_sound hs e v hv).elim fun w hw => ⟨w, hw.1⟩)
      body (holds_clockFree size I)
    refine Safe.conseq loopI (fun s hs => le_holds hle hs) ?_
    intro s ⟨hs, hz⟩
    have hw : decide ((0 : Word) ≠ 0) = false := by decide
    obtain ⟨A', hA', hsA'⟩ := assume_sound I e false hs 0 hz hw
    exact ⟨A', hA', hsA'⟩
  | ret e =>
    intro A out h
    simp only [analyze, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i v hv
      apply Safe.ret
      intro s hs
      obtain ⟨w, ew, _⟩ := eval_of hs hv
      exact ⟨w, ew⟩

/-- The analysis of a whole `main`, accepted: from every state whose heap covers `size` bytes
from `@base`, the run never finishes normally and never errs. -/
theorem check_safe (o : Oracle σ) {size : Nat} {p : PancakeProg} (h : check size p = .ok ()) :
    Safe o (fun s => Covers size s.memaddrs s.baseAddr) p (fun _ => False) := by
  simp only [check, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    cases r with
    | none =>
      refine Safe.conseq (analyze_safe o size p _ none hr) (fun s hc => ⟨hc, ?_, ?_⟩) ?_
      · intro x v hv
        cases hv
      · exact holds_empty_cells s
      · intro s ⟨B, hB, _⟩
        cases hB
    | some B => cases h

/-- **No run of a `main` the analysis accepts fails**, whatever the external world answers and
whatever the clock, from a heap that covers `size` bytes from `@base`. -/
theorem never_fails (o : Oracle σ) {size : Nat} {p : PancakeProg} (h : check size p = .ok ())
    (s : PancakeState σ) (hc : Covers size s.memaddrs s.baseAddr) : ¬ Entry.Fails o p s :=
  Safe.not_fails (check_safe o h) (fun _ => hc)

/-! ## The premise -/

/-- A heap of the aligned words from `b`, `n` bytes of them. -/
def heapWords (b : Word) (n : Nat) (a : Word) : Bool :=
  a.toNat % 8 = 0 && b.toNat ≤ a.toNat && a.toNat < b.toNat + n

/-- The premise holds of a heap of just the aligned words of the layout, from any aligned `@base`
it fits above. -/
theorem covers_heap {size : Nat} (b : Word) (hs : size % 8 = 0) (hb : b.toNat % 8 = 0)
    (hfit : b.toNat + size < 2 ^ 64) : Covers size (heapWords b size) b := by
  have e : ∀ off, off < size → (b + BitVec.ofNat 64 off).toNat = b.toNat + off := by
    intro off hoff
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨fun off hoff => ?_, fun off hoff h8 => ?_⟩
  · simp only [heapWords, Bytes.byteAlign_toNat, e off hoff, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · simp only [heapWords, e off hoff, Bool.and_eq_true, decide_eq_true_eq]
    omega

/-! ## The premises can hold -/

theorem holds_witness : (AVal.const 5).holds 0 5 := holds_const 0 5

theorem locals_witness :
    LocalsHold 0 [("x", AVal.const 5)] (fun y => if y = "x" then some 5 else none) := by
  intro y v hv
  simp only [lookup] at hv
  split at hv
  · cases hv
    rename_i hy
    exact ⟨5, by simp [hy], holds_const 0 5⟩
  · cases hv

/-- A state of a heap of 64 bytes from address 0, with nothing declared. -/
def heapState : PancakeState Unit := { Entry.bare with memaddrs := heapWords 0 64 }

theorem cells_witness : CellsHold heapState [("x", 0, AVal.top)] := by
  intro x k v hv p _
  simp only [lookupCell] at hv
  split at hv
  · cases hv
    exact holds_top _ _
  · cases hv

theorem holds_state_witness : Holds 64 ⟨[], []⟩ heapState :=
  ⟨covers_heap 0 (by decide) (by decide) (by decide), (fun _ _ h => by cases h),
    holds_empty_cells _⟩

theorem post_witness : Post 64 (some ⟨[], []⟩) heapState := ⟨_, rfl, holds_state_witness⟩

end DN.Compiler.Analyzer
