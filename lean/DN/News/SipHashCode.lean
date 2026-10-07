-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Wp
import DN.News.SipHash

/-!
# DN.News.SipHashCode

SipHash-2-4 as Pancake statements, shown by `DN.Compiler.Wp` to compute `DN.News.SipHash`.
-/

namespace DN.News.SipHashCode

open DN.Compiler DN.Compiler.Wp DN.News.SipHash

variable {σ : Type}

private def c (k : Nat) : PancakeExp := .c k
private def v (x : String) : PancakeExp := .var x

/-- `x` rotated left by `b` bits: two shifts and an or. -/
def rotlE (x : String) (b : Nat) : PancakeExp :=
  .op .or_ (.shiftL (v x) (c b)) (.shiftR (v x) (c (64 - b)))

/-- One SipRound over the locals `v0` to `v3`. -/
def roundProg : AProg σ :=
  .seq (.assign "v0" (.op .add (v "v0") (v "v1"))) <|
  .seq (.assign "v1" (.op .xor (rotlE "v1" 13) (v "v0"))) <|
  .seq (.assign "v0" (rotlE "v0" 32)) <|
  .seq (.assign "v2" (.op .add (v "v2") (v "v3"))) <|
  .seq (.assign "v3" (.op .xor (rotlE "v3" 16) (v "v2"))) <|
  .seq (.assign "v0" (.op .add (v "v0") (v "v3"))) <|
  .seq (.assign "v3" (.op .xor (rotlE "v3" 21) (v "v0"))) <|
  .seq (.assign "v2" (.op .add (v "v2") (v "v1"))) <|
  .seq (.assign "v1" (.op .xor (rotlE "v1" 17) (v "v2"))) <|
  .assign "v2" (rotlE "v2" 32)

/-- The locals `v0` to `v3` hold the state `st`. -/
def Holds (st : State) (s : PancakeState σ) : Prop :=
  s.locals "v0" = some st.v0.toBitVec ∧ s.locals "v1" = some st.v1.toBitVec ∧
    s.locals "v2" = some st.v2.toBitVec ∧ s.locals "v3" = some st.v3.toBitVec

theorem eval_rotl {s : PancakeState σ} {x : String} {w : UInt64} {b : Nat} (hb0 : 0 < b)
    (hb : b < 64) (hx : s.locals x = some w.toBitVec) :
    eval s (rotlE x b) = some (rotl w (UInt64.ofNat b)).toBitVec := by
  have h1 : (BitVec.ofNat 64 b).toNat = b := by simp [BitVec.toNat_ofNat]; omega
  have h2 : (BitVec.ofNat 64 (64 - b)).toNat = 64 - b := by simp [BitVec.toNat_ofNat]; omega
  have e1 : ((UInt64.ofNat b).toBitVec % (64 : BitVec 64)).toNat = b := by
    simp [BitVec.toNat_umod, BitVec.toNat_ofNat]; omega
  have e2 : ((64 - UInt64.ofNat b).toBitVec % (64 : BitVec 64)).toNat = 64 - b := by
    simp [BitVec.toNat_umod, BitVec.toNat_sub, UInt64.toBitVec_ofNat, BitVec.toNat_ofNat]; omega
  have n1 : (decide (b ≠ 0) && decide (b ≥ 64)) = false := by simp; omega
  have n2 : (decide (64 - b ≠ 0) && decide (64 - b ≥ 64)) = false := by simp; omega
  simp only [rotlE, v, c, PancakeExp.c, eval, hx, h1, h2, n1, n2, Bool.false_eq_true, if_false,
    rotl,
    UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  rw [e1, e2]

theorem holds_v0 {st : State} {s : PancakeState σ} (h : Holds st s) (w : UInt64) :
    Holds { st with v0 := w } { s with locals := setLocal s.locals "v0" w.toBitVec } := by
  obtain ⟨_, h1, h2, h3⟩ := h
  simp [Holds, setLocal, h1, h2, h3]

theorem holds_v1 {st : State} {s : PancakeState σ} (h : Holds st s) (w : UInt64) :
    Holds { st with v1 := w } { s with locals := setLocal s.locals "v1" w.toBitVec } := by
  obtain ⟨h0, _, h2, h3⟩ := h
  simp [Holds, setLocal, h0, h2, h3]

theorem holds_v2 {st : State} {s : PancakeState σ} (h : Holds st s) (w : UInt64) :
    Holds { st with v2 := w } { s with locals := setLocal s.locals "v2" w.toBitVec } := by
  obtain ⟨h0, h1, _, h3⟩ := h
  simp [Holds, setLocal, h0, h1, h3]

theorem holds_v3 {st : State} {s : PancakeState σ} (h : Holds st s) (w : UInt64) :
    Holds { st with v3 := w } { s with locals := setLocal s.locals "v3" w.toBitVec } := by
  obtain ⟨h0, h1, h2, _⟩ := h
  simp [Holds, setLocal, h0, h1, h2]

theorem round_wp (st : State) (s : PancakeState σ) (h : Holds st s) :
    wp roundProg (Holds (sipRound st)) s := by
  obtain ⟨a, b, c', d⟩ := st
  refine wp_seq (wp_assign (val := (a + b).toBitVec)
    (by simp [eval, v, h.1, h.2.1])
    h.1 (holds_v0 h _)) fun s h => ?_
  refine wp_seq (wp_assign (val := (rotl b 13 ^^^ (a + b)).toBitVec)
    (by simp [eval, v, eval_rotl (b := 13) (by decide) (by decide) h.2.1, h.1])
    h.2.1 (holds_v1 h _)) fun s h => ?_
  refine wp_seq (wp_assign (val := (rotl (a + b) 32).toBitVec)
    (by simp [eval_rotl (b := 32) (by decide) (by decide) h.1])
    h.1 (holds_v0 h _)) fun s h => ?_
  refine wp_seq (wp_assign (val := (c' + d).toBitVec)
    (by simp [eval, v, h.2.2.1, h.2.2.2])
    h.2.2.1 (holds_v2 h _)) fun s h => ?_
  refine wp_seq (wp_assign (val := (rotl d 16 ^^^ (c' + d)).toBitVec)
    (by simp [eval, v, eval_rotl (b := 16) (by decide) (by decide) h.2.2.2, h.2.2.1])
    h.2.2.2 (holds_v3 h _)) fun s h => ?_
  refine wp_seq (wp_assign (val := ((rotl (a + b) 32) + (rotl d 16 ^^^ (c' + d))).toBitVec)
    (by simp [eval, v, h.1, h.2.2.2])
    h.1 (holds_v0 h _)) fun s h => ?_
  refine wp_seq (wp_assign
    (val := (rotl (rotl d 16 ^^^ (c' + d)) 21 ^^^
      ((rotl (a + b) 32) + (rotl d 16 ^^^ (c' + d)))).toBitVec)
    (by simp [eval, v, eval_rotl (b := 21) (by decide) (by decide) h.2.2.2, h.1])
    h.2.2.2 (holds_v3 h _)) fun s h => ?_
  refine wp_seq (wp_assign (val := ((c' + d) + (rotl b 13 ^^^ (a + b))).toBitVec)
    (by simp [eval, v, h.2.2.1, h.2.1])
    h.2.2.1 (holds_v2 h _)) fun s h => ?_
  refine wp_seq (wp_assign
    (val := (rotl (rotl b 13 ^^^ (a + b)) 17 ^^^
      ((c' + d) + (rotl b 13 ^^^ (a + b)))).toBitVec)
    (by simp [eval, v, eval_rotl (b := 17) (by decide) (by decide) h.2.1, h.2.2.1])
    h.2.1 (holds_v1 h _)) fun s h => ?_
  exact wp_assign (val := (rotl ((c' + d) + (rotl b 13 ^^^ (a + b))) 32).toBitVec)
    (by simp [eval_rotl (b := 32) (by decide) (by decide) h.2.2.1])
    h.2.2.1 (holds_v2 h _)

private def fourLocals : String → Option Value :=
  setLocal (setLocal (setLocal (setLocal (fun _ => none) "v0" 1) "v1" 2) "v2" 3) "v3" 4

/-- The locals can hold a state. -/
theorem holds_witness : Holds ⟨1, 2, 3, 4⟩ { bareState () with locals := fourLocals } := by
  simp [Holds, fourLocals, setLocal]

end DN.News.SipHashCode
