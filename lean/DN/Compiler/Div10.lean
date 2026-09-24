-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Semantics

/-!
# DN.Compiler.Div10

Division by ten without a division instruction. Pancake has no `Div` or `Mod`, and its
multiplication yields only the low half of the product, so the quotient is built from two
multiplications by `3435973837`: one for each half of the word. The carry between the
halves is `2^32 = 429496729 * 10 + 6`.
-/

namespace DN.Compiler.Div10
open DN.Compiler

theorem div10_of_lt (x : Nat) (h : x < 2 ^ 34) : x * 3435973837 / 2 ^ 35 = x / 10 := by
  have hx : 10 * (x / 10) + x % 10 = x := Nat.div_add_mod x 10
  have hr : x % 10 < 10 := Nat.mod_lt _ (by decide)
  have hq : x / 10 ≤ 1717986918 := by omega
  have key : x * 3435973837 = 2 ^ 35 * (x / 10) + (2 * (x / 10) + x % 10 * 3435973837) := by
    omega
  rw [key, Nat.mul_add_div (by decide : 0 < 2 ^ 35)]
  have : 2 * (x / 10) + x % 10 * 3435973837 < 2 ^ 35 := by omega
  omega

def div10w (n : Word) : Word :=
  let hi := n >>> 32
  let lo := n &&& 4294967295
  let qh := (hi * 3435973837) >>> 35
  let rh := hi - qh * 10
  let t := rh * 6 + lo
  let qt := (t * 3435973837) >>> 35
  qh * 4294967296 + rh * 429496729 + qt

/-- Every product the quotient is built from fits in one word, which is why Pancake's
truncating multiplication loses nothing here. -/
theorem div10w_products_fit (n : Word) :
    (n >>> 32).toNat * 3435973837 < 2 ^ 64 ∧
    (((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 6 + n.toNat % 2 ^ 32) * 3435973837
      < 2 ^ 64 ∧
    (n >>> 32).toNat / 10 * 4294967296
      + ((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 429496729 < 2 ^ 64 := by
  have hn : n.toNat < 2 ^ 64 := n.isLt
  have hhi : (n >>> 32).toNat = n.toNat / 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlo : n.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  refine ⟨by omega, by omega, by omega⟩

theorem div10w_toNat (n : Word) : (div10w n).toNat = n.toNat / 10 := by
  have hn : n.toNat < 2 ^ 64 := n.isLt
  have cM : (3435973837 : Word).toNat = 3435973837 := rfl
  have cTen : (10 : Word).toNat = 10 := rfl
  have cSix : (6 : Word).toNat = 6 := rfl
  have cHi : (4294967296 : Word).toNat = 4294967296 := rfl
  have cLo : (429496729 : Word).toNat = 429496729 := rfl
  have hhi : (n >>> 32).toNat = n.toNat / 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hhiLt : (n >>> 32).toNat < 2 ^ 32 := by omega
  have hlo : (n &&& 4294967295).toNat = n.toNat % 2 ^ 32 := by
    rw [BitVec.toNat_and]
    show n.toNat &&& (2 ^ 32 - 1) = n.toNat % 2 ^ 32
    exact Nat.and_two_pow_sub_one_eq_mod n.toNat 32
  have hloLt : (n &&& 4294967295).toNat < 2 ^ 32 := by
    rw [hlo]; exact Nat.mod_lt _ (by decide)
  have hqh : ((n >>> 32 * 3435973837) >>> 35).toNat = (n >>> 32).toNat / 10 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, cM,
        Nat.mod_eq_of_lt (by omega : (n >>> 32).toNat * 3435973837 < 2 ^ 64)]
    exact div10_of_lt _ (by omega)
  have hrh : (n >>> 32 - (n >>> 32 * 3435973837) >>> 35 * 10).toNat
      = (n >>> 32).toNat - (n >>> 32).toNat / 10 * 10 := by
    rw [BitVec.toNat_sub, BitVec.toNat_mul, hqh, cTen,
        Nat.mod_eq_of_lt (by omega : (n >>> 32).toNat / 10 * 10 < 2 ^ 64)]
    omega
  have hrhLt : (n >>> 32 - (n >>> 32 * 3435973837) >>> 35 * 10).toNat < 10 := by
    rw [hrh]; omega
  have ht : ((n >>> 32 - (n >>> 32 * 3435973837) >>> 35 * 10) * 6 + (n &&& 4294967295)).toNat
      = ((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 6 + n.toNat % 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, hrh, hlo, cSix,
        Nat.mod_eq_of_lt (by omega : ((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 6 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega)]
  have hqt : ((((n >>> 32 - (n >>> 32 * 3435973837) >>> 35 * 10) * 6 + (n &&& 4294967295))
        * 3435973837) >>> 35).toNat
      = (((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 6 + n.toNat % 2 ^ 32) / 10 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, ht, cM,
        Nat.mod_eq_of_lt (by omega : (((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 6
          + n.toNat % 2 ^ 32) * 3435973837 < 2 ^ 64)]
    exact div10_of_lt _ (by omega)
  have hqhN : (n >>> 32).toNat / 10 ≤ 429496729 := by omega
  have hrhN : (n >>> 32).toNat - (n >>> 32).toNat / 10 * 10 < 10 := by omega
  have hqtN : (((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 6 + n.toNat % 2 ^ 32) / 10
      < 2 ^ 32 := by omega
  simp only [div10w]
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, hqh, hrh, hqt,
      cHi, cLo,
      Nat.mod_eq_of_lt (by omega : (n >>> 32).toNat / 10 * 4294967296 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : ((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 429496729
        < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : (n >>> 32).toNat / 10 * 4294967296
        + ((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 429496729 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : (n >>> 32).toNat / 10 * 4294967296
        + ((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 429496729
        + (((n >>> 32).toNat - (n >>> 32).toNat / 10 * 10) * 6 + n.toNat % 2 ^ 32) / 10
        < 2 ^ 64),
      hhi]
  have hsplit : 2 ^ 32 * (n.toNat / 2 ^ 32) + n.toNat % 2 ^ 32 = n.toNat := Nat.div_add_mod _ _
  have hhi10 : 10 * (n.toNat / 2 ^ 32 / 10) + n.toNat / 2 ^ 32 % 10 = n.toNat / 2 ^ 32 :=
    Nat.div_add_mod _ _
  have hq10 : 10 * (n.toNat / 10) + n.toNat % 10 = n.toNat := Nat.div_add_mod _ _
  have hlo32 : n.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hcarry : n.toNat / 2 ^ 32 - n.toNat / 2 ^ 32 / 10 * 10 = n.toNat / 2 ^ 32 % 10 := by omega
  rw [hcarry]
  have hqtNat : 10 * ((n.toNat / 2 ^ 32 % 10 * 6 + n.toNat % 2 ^ 32) / 10)
      + (n.toNat / 2 ^ 32 % 10 * 6 + n.toNat % 2 ^ 32) % 10
      = n.toNat / 2 ^ 32 % 10 * 6 + n.toNat % 2 ^ 32 := Nat.div_add_mod _ _
  omega

end DN.Compiler.Div10
