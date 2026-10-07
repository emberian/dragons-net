-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.WpBytes
import DN.News.CrcProg
import DN.News.Journal

/-!
# DN.News.CrcCode

The CRC-32C of `DN.News.Journal`, a byte at a time from a table of 256 words. A shift of the
remainder is linear in exclusive or (`shiftB_xor`), so eight from `c ^ b` are the table's word for
its low octet and `c` moved down eight places (`crcByte_table`). The programs `DN.News.CrcProg`
prints lower to ones shown to build the table (`fill_safe`) and to read a buffer's CRC-32C from it
(`crc_safe`).
-/

namespace DN.News.CrcCode

open DN.News.Journal
open DN.News.FrameSpec (Byte)

/-- `shift` on bit vectors. -/
def shiftB (c : BitVec 32) : BitVec 32 :=
  if c.getLsbD 0 then (c >>> 1) ^^^ poly.toBitVec else c >>> 1

theorem low_bit (c : UInt32) : (c &&& 1 == 1) = c.toBitVec.getLsbD 0 := by
  have h : (c &&& 1).toBitVec = BitVec.setWidth 32 (BitVec.ofBool (c.toBitVec.getLsbD 0)) := by
    rw [UInt32.toBitVec_and]
    exact BitVec.and_one_eq_setWidth_ofBool_getLsbD
  cases hb : c.toBitVec.getLsbD 0 <;> rw [hb] at h
  · have : c &&& 1 ≠ 1 := fun e => by rw [e] at h; exact absurd h (by decide)
    simpa using this
  · have : c &&& 1 = 1 := UInt32.toBitVec_inj.mp (by rw [h]; decide)
    simp [this]

theorem shift_toBitVec (c : UInt32) : (shift c).toBitVec = shiftB c.toBitVec := by
  unfold shift shiftB
  rw [low_bit]
  split <;> simp

theorem xor_cancel (a b p : BitVec 32) : a ^^^ p ^^^ (b ^^^ p) = a ^^^ b := by
  rw [BitVec.xor_assoc a p (b ^^^ p), ← BitVec.xor_assoc p b p, BitVec.xor_comm p b,
    BitVec.xor_assoc b p p, BitVec.xor_self, BitVec.xor_zero]

theorem shiftB_xor (a b : BitVec 32) : shiftB (a ^^^ b) = shiftB a ^^^ shiftB b := by
  unfold shiftB
  simp only [BitVec.getLsbD_xor, BitVec.ushiftRight_xor_distrib]
  cases a.getLsbD 0 <;> cases b.getLsbD 0 <;> simp <;>
    first | ac_rfl | exact (xor_cancel _ _ _).symm

/-- `n` shifts of the remainder. -/
def shifts : Nat → BitVec 32 → BitVec 32
  | 0, c => c
  | n + 1, c => shiftB (shifts n c)

def shiftsU : Nat → UInt32 → UInt32
  | 0, c => c
  | n + 1, c => shift (shiftsU n c)

theorem shifts_xor (n : Nat) (a b : BitVec 32) :
    shifts n (a ^^^ b) = shifts n a ^^^ shifts n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shifts, ih, shiftB_xor]

/-- A remainder whose low `8` bits are clear only moves down through eight shifts. -/
theorem shifts_high (y : BitVec 32) (hy : ∀ i, i < 8 → y.getLsbD i = false) :
    ∀ k, k ≤ 8 → shifts k y = y >>> k
  | 0, _ => by simp [shifts]
  | k + 1, hk => by
    rw [shifts, shifts_high y hy k (by omega)]
    have : (y >>> k).getLsbD 0 = false := by simpa using hy k (by omega)
    simp only [shiftB, this, Bool.false_eq_true, if_false, BitVec.shiftRight_add]

theorem split_low (x : BitVec 32) : x = (x &&& 255#32) ^^^ (x &&& ~~~255#32) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases x[i] <;> cases (255#32)[i] <;> rfl

theorem testBit_255 (i : Nat) : (255 : Nat).testBit i = decide (i < 8) := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]

theorem high_clear (x : BitVec 32) : ∀ i, i < 8 → (x &&& ~~~255#32).getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, testBit_255]
  simp [hi]

theorem high_shift (x : BitVec 32) : (x &&& ~~~255#32) >>> 8 = x >>> 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_ofNat, testBit_255]
  by_cases h : 8 + i < 32
  · simp [h]
  · simp [BitVec.getLsbD_of_ge x (8 + i) (by omega)]

/-- Eight shifts of `x`: those of its low octet, and the rest of it moved down eight places. -/
theorem shifts_eight (x : BitVec 32) : shifts 8 x = shifts 8 (x &&& 255#32) ^^^ (x >>> 8) := by
  conv => lhs; rw [split_low x]
  rw [shifts_xor, shifts_high _ (high_clear x) 8 (Nat.le_refl _), high_shift]

/-- The table: eight shifts of each octet. -/
def table (i : UInt32) : UInt32 := shiftsU 8 i

theorem shiftsU_toBitVec (n : Nat) (c : UInt32) : (shiftsU n c).toBitVec = shifts n c.toBitVec := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shiftsU, shifts, shift_toBitVec, ih]

/-- **A byte at a time from the table**: the CRC step is the table's word for the low octet of
`c ^ b`, and `c` moved down eight places. -/
theorem crcByte_table (c : UInt32) (b : Byte) :
    crcByte c b = table ((c ^^^ b.toNat.toUInt32) &&& 255) ^^^ (c >>> 8) := by
  have hb : (b.toNat.toUInt32).toBitVec >>> 8 = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    have := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    simp
    omega
  apply UInt32.toBitVec_inj.mp
  have e : crcByte c b = shiftsU 8 (c ^^^ b.toNat.toUInt32) := rfl
  rw [e, shiftsU_toBitVec, UInt32.toBitVec_xor, shifts_eight, UInt32.toBitVec_xor, table,
    shiftsU_toBitVec, UInt32.toBitVec_and, UInt32.toBitVec_xor, UInt32.toBitVec_shiftRight,
    BitVec.ushiftRight_xor_distrib, hb, BitVec.xor_zero]
  rfl

/-! ## In words -/

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpBytes

variable {σ : Type}

/-- A remainder as a word. -/
def w32 (c : UInt32) : Word := c.toBitVec.setWidth 64

theorem w32_xor (a b : UInt32) : w32 (a ^^^ b) = w32 a ^^^ w32 b := by simp [w32]

theorem w32_and (a b : UInt32) : w32 (a &&& b) = w32 a &&& w32 b := by simp [w32]

theorem w32_shr (c : UInt32) : w32 (c >>> 8) = w32 c >>> 8 := by
  simp [w32, UInt32.toBitVec_shiftRight, BitVec.setWidth_ushiftRight]

theorem w32_toNat (c : UInt32) : (w32 c).toNat = c.toNat := by
  simp [w32, BitVec.toNat_setWidth, UInt32.toNat_toBitVec]

theorem w32_byte (b : Byte) : w32 b.toNat.toUInt32 = b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [w32_toNat]
  have := b.isLt
  simp
  omega

theorem w32_lit (k : Nat) (hk : k < 2 ^ 32) : w32 (UInt32.ofNat k) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [w32_toNat]
  simp
  omega

/-- The table, a word for each octet, from `t`. -/
def TableAt (m : Word → Word) (dm : Word → Bool) (t : Word) : Prop :=
  ∀ j : Nat, j < 256 → dm (t + BitVec.ofNat 64 (j * 8)) = true ∧
    m (t + BitVec.ofNat 64 (j * 8)) = w32 (table (UInt32.ofNat j))

/-- The locals `t`, `p` and `n` name the table and the buffer `bs`, both in memory, and `r` is
bound. -/
def CrcGiven (t p : Word) (bs : List Byte) (s : PancakeState σ) : Prop :=
  s.locals "t" = some t ∧ s.locals "p" = some p ∧
    s.locals "n" = some (BitVec.ofNat 64 bs.length) ∧ (∃ r, s.locals "r" = some r) ∧
    readByteArray s.memory s.memaddrs s.be p bs.length = some bs ∧ TableAt s.memory s.memaddrs t

/-- After `k` octets: `i` is `k`, and `acc` the remainder they leave. -/
def CrcSummed (t p : Word) (bs : List Byte) (s : PancakeState σ) : Prop :=
  ∃ k, k ≤ bs.length ∧ CrcGiven t p bs s ∧ s.locals "i" = some (BitVec.ofNat 64 k) ∧
    s.locals "acc" = some (w32 ((bs.take k).foldl crcByte 0xFFFFFFFF))

/-- The step: the table's word for the low octet of `acc ^ b`, and `acc` moved down. -/
def stepE : PancakeExp :=
  .op .xor (.loadWord (.op .add (.var "t") (.mul (.op .and_ (.op .xor (.var "acc")
    (.loadByte (.op .add (.var "p") (.var "i")))) (.c 255)) (.c 8)))) (.shiftR (.var "acc") (.c 8))

/-- `r` gets the CRC-32C of the octets from `p` to `p + n`, with the locals `i` and `acc`. -/
def crcA (t p : Word) (bs : List Byte) : AProg σ :=
  .seq (.assign "i" (.c 0)) <| .seq (.assign "acc" (.c 0xFFFFFFFF)) <|
    .seq (.while_ (CrcSummed t p bs) (.cmp .less (.var "i") (.var "n"))
      (.seq (.assign "acc" stepE) (.assign "i" (.op .add (.var "i") (.c 1)))))
      (.assign "r" (.op .xor (.var "acc") (.c 0xFFFFFFFF)))

theorem crcGiven_set {t p : Word} {bs : List Byte} {s : PancakeState σ} (h : CrcGiven t p bs s)
    (x : String) (ht : x ≠ "t") (hp : x ≠ "p") (hn : x ≠ "n") (hr : x ≠ "r") (w : Value) :
    CrcGiven t p bs { s with locals := setLocal s.locals x w } := by
  obtain ⟨h1, h2, h3, ⟨r, h4⟩, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ⟨r, ?_⟩, h5, h6⟩ <;>
    simp [setLocal, Ne.symm ht, Ne.symm hp, Ne.symm hn, Ne.symm hr, *]

/-- The step's word, for the remainder `c` and the octet `b` at `p + k`. -/
theorem eval_step {t p : Word} {bs : List Byte} {s : PancakeState σ} (h : CrcGiven t p bs s)
    {k : Nat} (hk : k < bs.length) {c : UInt32} (hi : s.locals "i" = some (BitVec.ofNat 64 k))
    (hacc : s.locals "acc" = some (w32 c)) :
    eval s stepE = some (w32 (crcByte c bs[k])) := by
  obtain ⟨ht, hp, _, _, hbuf, htab⟩ := h
  have hb := readByteArray_get hbuf k hk
  rw [List.getElem?_eq_getElem hk] at hb
  have hidx : ((c ^^^ bs[k].toNat.toUInt32) &&& 255).toNat < 256 := by
    rw [UInt32.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  obtain ⟨hdm, hm⟩ := htab _ hidx
  have haddr : t + ((w32 c ^^^ bs[k].setWidth 64) &&& BitVec.ofNat 64 255) * BitVec.ofNat 64 8 =
      t + BitVec.ofNat 64 (((c ^^^ bs[k].toNat.toUInt32) &&& 255).toNat * 8) := by
    rw [← w32_byte, ← w32_xor, ← w32_lit 255 (by decide), ← w32_and]
    congr 1
  simp only [stepE, eval, PancakeExp.c, ht, hp, hi, hacc, hb, haddr, hdm, hm, if_true,
    UInt32.ofNat_toNat]
  have h8 : (decide ((8#64).toNat ≠ 0) && decide ((8#64).toNat ≥ 64)) = false := by decide
  simp only [h8, Bool.false_eq_true, if_false, Option.some.injEq]
  rw [crcByte_table, w32_xor, w32_shr]
  rfl

theorem fold_take_succ (bs : List Byte) (k : Nat) (hk : k < bs.length) :
    (bs.take (k + 1)).foldl crcByte 0xFFFFFFFF =
      crcByte ((bs.take k).foldl crcByte 0xFFFFFFFF) bs[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

theorem crc_vc (t p : Word) (bs : List Byte) (hlen : bs.length < 2 ^ 63) :
    vc (crcA (σ := σ) t p bs) (fun s => s.locals "r" = some (w32 (crc32c bs))) := by
  refine ⟨trivial, trivial, ⟨fun s k h => h, ⟨trivial, trivial⟩, fun s ⟨k, hk, hg, hi, hacc⟩ => ?_⟩,
    trivial⟩
  have hn := hg.2.2.1
  simp only [eval, hi, hn, signedLt_small (by omega : k < 2 ^ 63) hlen]
  by_cases hlt : k < bs.length
  · simp only [hlt, decide_true, if_true]
    simp only [show ((1 : Word) = 0) = False by decide, if_false, wp, eval_step hg hlt hi hacc,
      hacc,
      eval, PancakeExp.c, setLocal_ne _ _ (show "i" ≠ "acc" by decide), hi]
    refine ⟨k + 1, hlt, crcGiven_set (crcGiven_set hg "acc" (by decide) (by decide) (by decide)
      (by decide) _) "i" (by decide) (by decide) (by decide) (by decide) _, ?_, ?_⟩
    · simp [setLocal, BitVec.ofNat_add]
    · simp [setLocal, fold_take_succ bs k hlt]
  · have : k = bs.length := by omega
    subst this
    obtain ⟨r, hr⟩ := hg.2.2.2.1
    simp only [hlt, decide_false, Bool.false_eq_true, if_false, if_true, wp, eval, hacc, hr,
      PancakeExp.c]
    simp only [List.take_length, setLocal]
    simp only [crc32c, w32_xor, show w32 0xFFFFFFFF = BitVec.ofNat 64 0xFFFFFFFF by decide]
    simp

/-- Besides what `CrcGiven` names, the locals `i` and `acc` are bound. -/
def CrcPre (t p : Word) (bs : List Byte) (s : PancakeState σ) : Prop :=
  CrcGiven t p bs s ∧ (∃ v, s.locals "i" = some v) ∧ ∃ v, s.locals "acc" = some v

theorem crc_wp (t p : Word) (bs : List Byte) (s : PancakeState σ) (h : CrcPre t p bs s) :
    wp (crcA t p bs) (fun t => t.locals "r" = some (w32 (crc32c bs))) s := by
  obtain ⟨hg, ⟨vi, hi⟩, ⟨va, ha⟩⟩ := h
  simp only [crcA, wp, eval, PancakeExp.c, hi, setLocal_ne _ _ (show "acc" ≠ "i" by decide), ha]
  refine ⟨0, Nat.zero_le _, crcGiven_set (crcGiven_set hg "i" (by decide) (by decide) (by decide)
    (by decide) _) "acc" (by decide) (by decide) (by decide) (by decide) _, ?_, ?_⟩
  · simp [setLocal]
  · simp [setLocal]
    decide

/-- **The loop computes the CRC-32C**: from a state where `t` names the table and `p` and `n` a
buffer `bs` in memory, a run that finishes normally has `r` equal to the CRC-32C of `bs`. -/
theorem crc_safe (o : Oracle σ) (t p : Word) (bs : List Byte) (hlen : bs.length < 2 ^ 63) :
    Safe.Safe o (CrcPre t p bs) (crcA (σ := σ) t p bs).erase
      (fun s => s.locals "r" = some (w32 (crc32c bs))) :=
  Safe.conseq (wp_sound o _ _ (fun _ _ h => h) (crc_vc t p bs hlen)) (fun s h => crc_wp t p bs s h)
    (fun _ h => h)

/-! ## The table, built at start -/

/-- One bit out of the remainder in `c`, without a branch: the polynomial is taken under a mask
of every bit when the low bit is set. -/
def shiftE : PancakeExp :=
  .op .xor (.shiftR (.var "c") (.c 1))
    (.op .and_ (.c 0x82F63B78) (.op .sub (.c 0) (.op .and_ (.var "c") (.c 1))))

theorem w32_shr1 (c : UInt32) : w32 (c >>> 1) = w32 c >>> 1 := by
  simp [w32, UInt32.toBitVec_shiftRight, BitVec.setWidth_ushiftRight]

theorem w32_low (c : UInt32) : w32 c &&& 1#64 = if c &&& 1 == 1 then 1#64 else 0#64 := by
  rw [low_bit]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [w32, BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
  cases i with
  | zero => cases c.toBitVec.getLsbD 0 <;> simp
  | succ i => cases c.toBitVec.getLsbD 0 <;> simp

theorem eval_shift {s : PancakeState σ} {x : UInt32} (hc : s.locals "c" = some (w32 x)) :
    eval s shiftE = some (w32 (shift x)) := by
  have h1 : (decide ((1#64).toNat ≠ 0) && decide ((1#64).toNat ≥ 64)) = false := by decide
  simp only [shiftE, eval, PancakeExp.c, hc, h1, Bool.false_eq_true, if_false, Option.some.injEq,
    w32_low]
  unfold shift
  split
  · simp only [w32_xor, w32_shr1]
    congr 1
  · simp only [w32_shr1]
    simp

/-- `n` statements, each one shift of `c`, then `rest`. -/
def nShifts : Nat → AProg σ → AProg σ
  | 0, rest => rest
  | n + 1, rest => .seq (.assign "c" shiftE) (nShifts n rest)

/-- The words written so far, from `t`: the first `k`, and the 256 in memory. -/
def Written (t : Word) (k : Nat) (s : PancakeState σ) : Prop :=
  s.locals "t" = some t ∧ s.locals "i" = some (BitVec.ofNat 64 k) ∧
    (∀ j, j < 256 → s.memaddrs (t + BitVec.ofNat 64 (j * 8)) = true) ∧
    (∀ j, j < k → s.memory (t + BitVec.ofNat 64 (j * 8)) = w32 (table (UInt32.ofNat j)))

/-- The loop's invariant: some first words written, `c` bound. -/
def Filled (t : Word) (s : PancakeState σ) : Prop :=
  ∃ k, k ≤ 256 ∧ Written t k s ∧ ∃ c, s.locals "c" = some c

/-- The table from `t`: for each of the 256 octets, eight shifts of it, stored as a word, with the
locals `i` and `c`. -/
def fillA (t : Word) : AProg σ :=
  .seq (.assign "i" (.c 0)) <|
    .while_ (Filled t) (.cmp .less (.var "i") (.c 256))
      (.seq (.assign "c" (.var "i")) <| nShifts 8 <|
        .seq (.store (.op .add (.var "t") (.mul (.var "i") (.c 8))) (.var "c"))
          (.assign "i" (.op .add (.var "i") (.c 1))))

theorem written_set {t : Word} {k : Nat} {s : PancakeState σ} (h : Written t k s) (w : Value) :
    Written t k { s with locals := setLocal s.locals "c" w } := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simp [setLocal, h1], by simp [setLocal, h2], h3, h4⟩

theorem shiftsU_succ' (n : Nat) (x : UInt32) : shiftsU n (shift x) = shiftsU (n + 1) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shiftsU] at ih ⊢; rw [ih]

theorem nShifts_wp {t : Word} {k : Nat} {rest : AProg σ} {Q : Assn σ} :
    ∀ (n : Nat) (x : UInt32) (s : PancakeState σ), Written t k s →
      s.locals "c" = some (w32 x) →
      (∀ s', Written t k s' → s'.locals "c" = some (w32 (shiftsU n x)) → wp rest Q s') →
      wp (nShifts n rest) Q s
  | 0, x, s, hw, hc, hr => hr s hw hc
  | n + 1, x, s, hw, hc, hr =>
    wp_seq (wp_assign (eval_shift hc) hc (Q := fun s' => Written t k s' ∧
        s'.locals "c" = some (w32 (shift x))) ⟨written_set hw _, by simp [setLocal]⟩)
      fun s' ⟨hw', hc'⟩ => nShifts_wp n (shift x) s' hw' hc' fun s'' hw'' hc'' =>
        hr s'' hw'' (by rw [hc'', shiftsU_succ'])

theorem addr_ne {t : Word} {j k : Nat} (hj : j < 256) (hk : k < 256) (hne : j ≠ k) :
    t + BitVec.ofNat 64 (j * 8) ≠ t + BitVec.ofNat 64 (k * 8) := by
  intro h
  rw [BitVec.add_comm t, BitVec.add_comm t] at h
  have := congrArg BitVec.toNat ((BitVec.add_left_inj t).mp h)
  simp at this
  omega

/-- The local `t` names 256 words in memory, and the locals `i` and `c` are bound. -/
def FillGiven (t : Word) (s : PancakeState σ) : Prop :=
  s.locals "t" = some t ∧ (∀ j, j < 256 → s.memaddrs (t + BitVec.ofNat 64 (j * 8)) = true) ∧
    (∃ v, s.locals "i" = some v) ∧ ∃ v, s.locals "c" = some v

theorem fill_step (t : Word) (k : Nat) (hk : k < 256) (s : PancakeState σ) (hw : Written t k s)
    (hc : ∃ c, s.locals "c" = some c) :
    wp (.seq (.assign "c" (.var "i")) <| nShifts 8 <|
        .seq (.store (.op .add (.var "t") (.mul (.var "i") (.c 8))) (.var "c"))
          (.assign "i" (.op .add (.var "i") (.c 1)))) (Filled (σ := σ) t) s := by
  obtain ⟨c, hc⟩ := hc
  have hk32 : w32 (UInt32.ofNat k) = BitVec.ofNat 64 k := w32_lit k (by omega)
  refine wp_seq (wp_assign (val := BitVec.ofNat 64 k) (by simp [eval, hw.2.1]) hc
    (Q := fun s' => Written t k s' ∧ s'.locals "c" = some (w32 (UInt32.ofNat k)))
    ⟨written_set hw _, by simp [setLocal, hk32]⟩) fun s1 ⟨hw1, hc1⟩ => ?_
  refine nShifts_wp 8 _ s1 hw1 hc1 fun s2 hw2 hc2 => ?_
  obtain ⟨ht2, hi2, hdm2, hm2⟩ := hw2
  have haddr : eval s2 (.op .add (.var "t") (.mul (.var "i") (.c 8))) =
      some (t + BitVec.ofNat 64 (k * 8)) := by
    simp only [eval, ht2, hi2, PancakeExp.c, Option.some.injEq]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul] <;> omega
  refine wp_seq (wp_store (val := w32 (shiftsU 8 (UInt32.ofNat k)))
    (m := fun x => if x = t + BitVec.ofNat 64 (k * 8) then w32 (shiftsU 8 (UInt32.ofNat k))
      else s2.memory x) haddr (by simp [eval, hc2]) (by simp [memStoreWord, hdm2 k hk])
    (Q := fun s3 => s3.locals "t" = some t ∧ s3.locals "i" = some (BitVec.ofNat 64 k) ∧
      (∃ c, s3.locals "c" = some c) ∧
      (∀ j, j < 256 → s3.memaddrs (t + BitVec.ofNat 64 (j * 8)) = true) ∧
      ∀ j, j < k + 1 → s3.memory (t + BitVec.ofNat 64 (j * 8)) = w32 (table (UInt32.ofNat j)))
    ⟨ht2, hi2, ⟨_, hc2⟩, hdm2, fun j hj => ?_⟩) fun s3 ⟨ht3, hi3, ⟨c3, hc3⟩, hdm3, hm3⟩ => ?_
  · by_cases hjk : j = k
    · subst hjk
      simp only [if_true]
      rfl
    · simp only [if_neg (addr_ne (by omega : j < 256) hk hjk)]
      exact hm2 j (by omega)
  · refine wp_assign (val := BitVec.ofNat 64 (k + 1))
      (by simp [eval, hi3, PancakeExp.c, BitVec.ofNat_add]) hi3
      ⟨k + 1, by omega, ⟨by simp [setLocal, ht3], by simp [setLocal], hdm3, hm3⟩, c3, ?_⟩
    simp [setLocal, hc3]

theorem fill_vc (t : Word) :
    vc (fillA (σ := σ) t) (fun s => s.locals "t" = some t ∧ TableAt s.memory s.memaddrs t) := by
  refine ⟨trivial, fun s k h => h, by simp only [nShifts, vc, and_self],
    fun s ⟨k, hk, hw, hc⟩ => ?_⟩
  simp only [eval, hw.2.1, PancakeExp.c,
    signedLt_small (by omega : k < 2 ^ 63) (by decide : 256 < 2 ^ 63)]
  by_cases hlt : k < 256
  · simp only [hlt, decide_true, if_true, show ((1 : Word) = 0) = False by decide, if_false]
    exact fill_step t k hlt s hw hc
  · have : k = 256 := by omega
    subst this
    obtain ⟨ht, _, hdm, hm⟩ := hw
    simp only [hlt, decide_false, Bool.false_eq_true, if_false, if_true]
    exact ⟨ht, fun j hj => ⟨hdm j hj, hm j hj⟩⟩

theorem fill_wp (t : Word) (s : PancakeState σ) (h : FillGiven t s) :
    wp (fillA t) (fun s => s.locals "t" = some t ∧ TableAt s.memory s.memaddrs t) s := by
  obtain ⟨ht, hdm, ⟨vi, hi⟩, ⟨vc, hc⟩⟩ := h
  simp only [fillA, wp, eval, PancakeExp.c, hi]
  exact ⟨0, by omega, ⟨by simp [setLocal, ht], by simp [setLocal], hdm, fun _ hj => absurd hj
    (Nat.not_lt_zero _)⟩, vc, by simp [setLocal, hc]⟩

/-- **The table is built**: from a state where `t` names 256 words in memory, a run that finishes
normally leaves in them the table `crcByte_table` reads. -/
theorem fill_safe (o : Oracle σ) (t : Word) :
    Safe.Safe o (FillGiven t) (fillA (σ := σ) t).erase
      (fun s => s.locals "t" = some t ∧ TableAt s.memory s.memaddrs t) :=
  Safe.conseq (wp_sound o _ _ (fun _ _ h => h) (fill_vc t)) (fun s h => fill_wp t s h)
    (fun _ h => h)

/-! ## The premises can hold -/

/-- A memory holding the table from `t`. -/
def tableMem (t : Word) : Word → Word := fun a => w32 (table (UInt32.ofNat ((a - t).toNat / 8)))

theorem tableAt_tableMem (t : Word) : TableAt (tableMem t) (fun _ => true) t := by
  intro j hj
  refine ⟨rfl, ?_⟩
  simp only [tableMem, BitVec.add_comm t, BitVec.add_sub_cancel]
  congr
  simp
  omega

private def crcLocals : String → Option Value :=
  setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => none) "t" 64) "p" 0) "n" 0)
    "r" 0) "i" 0) "acc" 0

/-- The loop's premise can hold: the table from 64, an empty buffer. -/
theorem crcPre_witness :
    CrcPre (σ := Unit) 64 0 [] { bareState () with locals := crcLocals, memory := tableMem 64 } :=
  ⟨⟨by simp [crcLocals, setLocal], by simp [crcLocals, setLocal], by simp [crcLocals, setLocal],
    ⟨0, by simp [crcLocals, setLocal]⟩, rfl, tableAt_tableMem 64⟩,
    ⟨0, by simp [crcLocals, setLocal]⟩, ⟨0, by simp [crcLocals, setLocal]⟩⟩

/-- The loop's premise without the locals it sets can hold. -/
theorem crcGiven_witness :
    CrcGiven (σ := Unit) 64 0 [] { bareState () with locals := crcLocals, memory := tableMem 64 } :=
  crcPre_witness.1

private def fillLocals : String → Option Value :=
  setLocal (setLocal (setLocal (fun _ => none) "t" 64) "i" 0) "c" 0

/-- The table's premise can hold, and so can its invariant's first state. -/
theorem fillGiven_witness :
    FillGiven (σ := Unit) 64 { bareState () with locals := fillLocals } ∧
      Written (σ := Unit) 64 0 { bareState () with locals := fillLocals } :=
  ⟨⟨by simp [fillLocals, setLocal], fun _ _ => rfl, ⟨0, by simp [fillLocals, setLocal]⟩,
    ⟨0, by simp [fillLocals, setLocal]⟩⟩,
   ⟨by simp [fillLocals, setLocal], by simp [fillLocals, setLocal], fun _ _ => rfl,
    fun _ hj => absurd hj (Nat.not_lt_zero _)⟩⟩

/-! ## As the gate prints them -/

open DN.News.CrcProg in
/-- The printed table is the one `fill_safe` is about. -/
theorem fill_lowering (t : Word) : Lower.lowerStmtsFold fillSrc = some (fillA (σ := σ) t).erase :=
  rfl

open DN.News.CrcProg in
/-- The printed loop is the one `crc_safe` is about. -/
theorem crc_lowering (t p : Word) (bs : List Byte) :
    Lower.lowerStmtsFold crcSrc = some (crcA (σ := σ) t p bs).erase := rfl

end DN.News.CrcCode
