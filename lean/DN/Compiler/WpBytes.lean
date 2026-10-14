-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Wp

/-!
# DN.Compiler.WpBytes

Octets in memory, as a program reads them in a loop: `readByteArray` describes a buffer, and the
byte at each index of it is the one a load from that address gives. A loop that sums a buffer's
octets is shown to compute their sum, the shape of every loop over a buffer.
-/

namespace DN.Compiler.WpBytes

open DN.Compiler DN.Compiler.Wp

variable {σ : Type}

theorem readByteArray_length {m : Word → Word} {dm : Word → Bool} {be : Bool} :
    ∀ {p : Word} {n : Nat} {bs : List (BitVec 8)}, readByteArray m dm be p n = some bs →
      bs.length = n
  | _, 0, bs, h => by simp only [readByteArray, Option.some.injEq] at h; subst h; rfl
  | p, n + 1, bs, h => by
    simp only [readByteArray] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i bs' hr
        cases h
        simp only [List.length_cons, readByteArray_length hr]

/-- **The octet at index `k` of a buffer** is what a load from its address plus `k` gives. -/
theorem readByteArray_get {m : Word → Word} {dm : Word → Bool} {be : Bool} :
    ∀ {p : Word} {n : Nat} {bs : List (BitVec 8)}, readByteArray m dm be p n = some bs →
      ∀ k, k < n → memLoadByte m dm be (p + BitVec.ofNat 64 k) = bs[k]?
  | _, 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | p, n + 1, bs, h, k, hk => by
    simp only [readByteArray] at h
    split at h
    · cases h
    · rename_i b hb
      split at h
      · cases h
      · rename_i bs' hr
        cases h
        cases k with
        | zero => simpa using hb
        | succ k =>
          have := readByteArray_get hr k (by omega)
          rw [show p + BitVec.ofNat 64 (k + 1) = p + 1 + BitVec.ofNat 64 k by
            rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_comm 1]; rfl]
          simpa using this

/-- Signed comparison of two numbers below `2 ^ 63` is their order. -/
theorem signedLt_small {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    signedLt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [signedLt, BitVec.slt_eq_decide, BitVec.toInt_ofNat']
  rw [Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]
  simp

/-! ## A loop over a buffer -/

/-- The octets of `bs` summed as words. -/
def sumOf (bs : List (BitVec 8)) : Word := bs.foldl (fun acc b => acc + b.setWidth 64) 0

/-- The locals `p` and `n` name the buffer `bs`, which is in memory, and `r` is bound. -/
def Given (p : Word) (bs : List (BitVec 8)) (s : PancakeState σ) : Prop :=
  s.locals "p" = some p ∧ s.locals "n" = some (BitVec.ofNat 64 bs.length) ∧
    (∃ r, s.locals "r" = some r) ∧ readByteArray s.memory s.memaddrs s.be p bs.length = some bs

/-- After `k` octets: `i` is `k` and `acc` their sum. -/
def Summed (p : Word) (bs : List (BitVec 8)) (s : PancakeState σ) : Prop :=
  ∃ k, k ≤ bs.length ∧ Given p bs s ∧ s.locals "i" = some (BitVec.ofNat 64 k) ∧
    s.locals "acc" = some (sumOf (bs.take k))

/-- `r` gets the sum of the octets from `p` to `p + n`. -/
def sumProg (p : Word) (bs : List (BitVec 8)) : AProg σ :=
  .dec "i" (.c 0) <| .dec "acc" (.c 0) <|
    .seq (.while_ (Summed p bs) (.cmp .less (.var "i") (.var "n"))
      (.seq (.assign "acc" (.op .add (.var "acc") (.loadByte (.op .add (.var "p") (.var "i")))))
        (.assign "i" (.op .add (.var "i") (.c 1)))))
      (.assign "r" (.var "acc"))

theorem sumOf_take_succ (bs : List (BitVec 8)) (k : Nat) (hk : k < bs.length) :
    sumOf (bs.take (k + 1)) = sumOf (bs.take k) + bs[k].setWidth 64 := by
  unfold sumOf
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

theorem given_set {p : Word} {bs : List (BitVec 8)} {s : PancakeState σ} (h : Given p bs s)
    (x : String) (hp : x ≠ "p") (hn : x ≠ "n") (hr : x ≠ "r") (w : Value) :
    Given p bs { s with locals := setLocal s.locals x w } := by
  obtain ⟨h1, h2, ⟨r, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ⟨r, ?_⟩, h4⟩ <;> simp [setLocal, Ne.symm hp, Ne.symm hn, Ne.symm hr, *]

theorem sum_vc (p : Word) (bs : List (BitVec 8)) (hlen : bs.length < 2 ^ 63) :
    vc (sumProg (σ := σ) p bs) (fun t => t.locals "r" = some (sumOf bs)) := by
  intro old_i old_acc
  refine ⟨⟨fun s k h => h, ⟨trivial, trivial⟩, fun s ⟨k, hk, hg, hi, hacc⟩ => ?_⟩, trivial⟩
  obtain ⟨hp, hn, _, hbuf⟩ := hg
  simp only [eval, hi, hn, signedLt_small (by omega : k < 2 ^ 63) hlen]
  by_cases hlt : k < bs.length
  · have hb := readByteArray_get hbuf k hlt
    rw [List.getElem?_eq_getElem hlt] at hb
    simp only [hlt, decide_true, if_true]
    simp only [show ((1 : Word) = 0) = False by decide, if_false, wp, eval, hacc, hp, hi, hb,
      PancakeExp.c, setLocal_ne _ _ (show "i" ≠ "acc" by decide)]
    refine ⟨k + 1, hlt, given_set (given_set ⟨hp, hn, ‹_›, hbuf⟩ "acc" (by decide) (by decide)
      (by decide) _) "i" (by decide) (by decide) (by decide) _, ?_, ?_⟩
    · simp [setLocal, BitVec.ofNat_add]
    · simp [setLocal, sumOf_take_succ bs k hlt]
  · have : k = bs.length := by omega
    subst this
    obtain ⟨r, hr⟩ := ‹∃ r, s.locals "r" = some r›
    simp only [hlt, decide_false, Bool.false_eq_true, if_false, if_true, wp, eval, hacc, hr]
    simp [restore, resVar, setLocal, List.take_length]

theorem sum_wp (p : Word) (bs : List (BitVec 8)) (s : PancakeState σ) (h : Given p bs s) :
    wp (sumProg p bs) (fun t => t.locals "r" = some (sumOf bs)) s := by
  obtain ⟨hp, hn, hr, hbuf⟩ := h
  simp only [sumProg, wp, eval, PancakeExp.c]
  refine ⟨0, Nat.zero_le _, given_set (given_set ⟨hp, hn, hr, hbuf⟩ "i" (by decide) (by decide)
    (by decide) _) "acc" (by decide) (by decide) (by decide) _, ?_, ?_⟩
  · simp [setLocal]
  · simp [setLocal, sumOf]

/-- **The loop sums the buffer**: from a state where `p` and `n` name `bs` in memory, a run that
finishes normally has `r` equal to the sum of its octets. -/
theorem sum_safe (o : Oracle σ) (p : Word) (bs : List (BitVec 8)) (hlen : bs.length < 2 ^ 63) :
    Safe.Safe o (Given p bs) (sumProg (σ := σ) p bs).erase
      (fun t => t.locals "r" = some (sumOf bs)) :=
  Safe.conseq (wp_sound o _ _ (fun _ _ h => h) (sum_vc p bs hlen)) (fun s h => sum_wp p bs s h)
    (fun _ h => h)

private def threeLocals : String → Option Value :=
  setLocal (setLocal (setLocal (fun _ => none) "p" 64) "n" 2) "r" 0

/-- The loop's premise can hold: two octets of a zeroed heap. -/
theorem given_witness : Given 64 [0, 0] { bareState () with locals := threeLocals } := by
  refine ⟨by decide, by decide, ⟨0, by decide⟩, by decide⟩

end DN.Compiler.WpBytes
