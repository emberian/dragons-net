-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.CommandSpec
import DN.Compiler.Decimal

/-!
# DN.News.DecimalRun

A number's decimal digits as `CommandSpec.decimal` gives them, digit by digit: how many there are
(`numDigits`, `numDigits_eq`), the last and the rest (`decimal_eq`), each in its place (`decimal_get`).
-/

namespace DN.News.DecimalRun

open DN.News DN.News.FrameSpec
open DN.Compiler.Decimal (digitByte)

/-- How many decimal digits a number has. -/
def numDigits (x : Nat) : Nat := (CommandSpec.decimal x).length

theorem decimal_length (x : Nat) : (CommandSpec.decimal x).length = numDigits x := rfl

theorem decimal_eq (x : Nat) : CommandSpec.decimal x =
    if x < 10 then [digitByte x] else CommandSpec.decimal (x / 10) ++ [digitByte (x % 10)] := by
  unfold CommandSpec.decimal CommandSpec.ascii
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList, Nat.toDigits_eq_if (by decide)]
  split
  · rename_i h
    simp [digitByte, Nat.toNat_digitChar_of_lt_ten h]
  · rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
    simp [digitByte, Nat.toNat_digitChar_of_lt_ten (Nat.mod_lt x (by decide : 10 > 0))]

theorem numDigits_eq (x : Nat) : numDigits x = if x < 10 then 1 else numDigits (x / 10) + 1 := by
  rw [numDigits, decimal_eq]
  split <;> simp [numDigits]

theorem numDigits_zero : numDigits 0 = 1 := rfl

theorem numDigits_pos (x : Nat) : 1 ≤ numDigits x := by
  rw [numDigits_eq]; split <;> omega

theorem lt_pow_numDigits (x : Nat) : x < 10 ^ numDigits x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [numDigits_eq]
    split
    · simpa using (by omega : x < 10)
    · have := ih (x / 10) (by omega)
      rw [Nat.pow_succ]
      omega

theorem pow_numDigits_le (x : Nat) (h : 10 ≤ x) : 10 ^ (numDigits x - 1) ≤ x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [numDigits_eq, if_neg (by omega), Nat.add_sub_cancel]
    by_cases h' : 10 ≤ x / 10
    · have := ih (x / 10) (by omega) h'
      have hp := numDigits_pos (x / 10)
      obtain ⟨k, hk⟩ : ∃ k, numDigits (x / 10) = k + 1 := ⟨numDigits (x / 10) - 1, by omega⟩
      rw [hk, Nat.pow_succ]
      rw [hk, Nat.add_sub_cancel] at this
      omega
    · rw [numDigits_eq, if_pos (by omega)]
      omega

/-- **Each digit in its place.** -/
theorem decimal_get (x : Nat) : ∀ i, i < numDigits x →
    (CommandSpec.decimal x)[i]? = some (digitByte (x / 10 ^ (numDigits x - 1 - i) % 10)) := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro i hi
    rw [decimal_eq]
    by_cases hx : x < 10
    · have hn : numDigits x = 1 := by rw [numDigits_eq, if_pos hx]
      rw [if_pos hx]
      rw [hn] at hi ⊢
      obtain rfl : i = 0 := by omega
      simp [Nat.mod_eq_of_lt hx]
    · rw [if_neg hx]
      have hn : numDigits x = numDigits (x / 10) + 1 := by rw [numDigits_eq, if_neg hx]
      rw [hn] at hi ⊢
      by_cases hlt : i < numDigits (x / 10)
      · rw [List.getElem?_append_left (by rw [decimal_length]; exact hlt), ih (x / 10) (by omega) i hlt]
        congr 3
        rw [show numDigits (x / 10) + 1 - 1 - i = (numDigits (x / 10) - 1 - i) + 1 by omega, Nat.pow_succ,
          Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      · obtain rfl : i = numDigits (x / 10) := by omega
        rw [List.getElem?_append_right (by rw [decimal_length]; exact Nat.le_refl _)]
        simp [decimal_length]

theorem numDigits_le_ten (x : Nat) (hx : x < 2 ^ 32) : numDigits x ≤ 10 := by
  have h := decimal_length x
  have := CommandSpec.decimal_length x (by omega)
  omega

/-- The count's loop: below the digits' number, the quotient is ten or more. -/
theorem quot_ge_ten {x c : Nat} (hc : 1 ≤ c) (hlt : c < numDigits x) : 10 ≤ x / 10 ^ (c - 1) := by
  have h10 : 10 ≤ x := by
    rw [numDigits_eq] at hlt; split at hlt <;> omega
  have hp := pow_numDigits_le x h10
  have : 10 ^ (c - 1) * 10 ≤ 10 ^ (numDigits x - 1) := by
    rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
  omega

/-- …and at it, below ten. -/
theorem quot_lt_ten (x : Nat) : x / 10 ^ (numDigits x - 1) < 10 := by
  have h := lt_pow_numDigits x
  have hp := numDigits_pos x
  obtain ⟨k, hk⟩ : ∃ k, numDigits x = k + 1 := ⟨numDigits x - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel]
  rw [hk, Nat.pow_succ] at h
  exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr (by rw [Nat.mul_comm]; exact h)

theorem count_exit {x c : Nat} (hc : 1 ≤ c) (hle : c ≤ numDigits x) (h : x / 10 ^ (c - 1) < 10) :
    c = numDigits x := by
  by_cases hlt : c < numDigits x
  · have := quot_ge_ten hc hlt; omega
  · omega

end DN.News.DecimalRun
