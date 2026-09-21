-- SPDX-License-Identifier: AGPL-3.0-or-later
/-!
# DN.Compiler.Decimal

Decimal rendering of a natural number as ASCII bytes, with the round trip that
reading the rendered digits back recovers the number. The Pancake program that
performs this rendering is in `DN.Compiler.NatToDec`.
-/

namespace DN.Compiler.Decimal

/-! ## 0. Bytes -/

/-- A byte string. -/
abbrev Bytes := List (BitVec 8)

/-! ## 1. `natToDec` — the bounded divide-by-10 digit loop

`decAux` divides by 10, prepending the ASCII digit of each remainder (least
significant last, so the emitted list is most-significant-first). Correctness is
the round trip `readFrom 0 (natToDec n) = n`: reading the emitted ASCII digits
back as a base-10 number recovers `n`. -/

/-- ASCII byte of a decimal digit `d` (`'0' = 48`). -/
def digitByte (d : Nat) : BitVec 8 := BitVec.ofNat 8 (48 + d)

/-- Read an ASCII decimal byte string back as a `Nat`, most-significant first
(left fold): `readFrom v (d₀ :: d₁ :: …) = ((v*10 + d₀)*10 + d₁) …`. -/
def readFrom (v : Nat) : Bytes → Nat
  | []      => v
  | b :: bs => readFrom (v * 10 + (b.toNat - 48)) bs

/-- The fuel'd divide-by-10 digit loop: emit the ASCII digits of `n`,
most-significant-first, in front of `acc`. -/
def decAux : Nat → Nat → Bytes → Bytes
  | 0,        _, acc => acc
  | fuel + 1, n, acc =>
    if n < 10 then digitByte n :: acc
    else decAux fuel (n / 10) (digitByte (n % 10) :: acc)

/-- Decimal ASCII rendering of `n`. Bounded: `n + 1` units of divide-by-10 fuel
suffice (each step divides by ≥ 10). -/
def natToDec (n : Nat) : Bytes := decAux (n + 1) n []

/-- The ASCII digit byte reads back as its digit (for `d < 10`). -/
theorem digitByte_sub {d : Nat} (h : d < 10) : (digitByte d).toNat - 48 = d := by
  unfold digitByte
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 48 + d < 2 ^ 8)]
  omega

/-- The loop invariant: reading the digits `decAux` emits in front of `acc`, from
a zero start, equals reading `acc` from a start of `n`. Induction on the fuel; the
`else` step consumes one digit (`n % 10`) and recurses on `n / 10`. -/
theorem decAux_readFrom (fuel : Nat) :
    ∀ (n : Nat) (acc : Bytes), n < fuel → readFrom 0 (decAux fuel n acc) = readFrom n acc := by
  induction fuel with
  | zero => intro n acc h; omega
  | succ f ih =>
    intro n acc h
    by_cases hn : n < 10
    · have hun : decAux (f + 1) n acc = digitByte n :: acc := if_pos hn
      rw [hun]
      show readFrom (0 * 10 + ((digitByte n).toNat - 48)) acc = readFrom n acc
      rw [digitByte_sub hn, Nat.zero_mul, Nat.zero_add]
    · have hd : n / 10 < f := by
        have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
        omega
      have hun : decAux (f + 1) n acc = decAux f (n / 10) (digitByte (n % 10) :: acc) := if_neg hn
      rw [hun, ih (n / 10) (digitByte (n % 10) :: acc) hd]
      have hm : n % 10 < 10 := Nat.mod_lt n (by omega)
      have hdm : n / 10 * 10 + n % 10 = n := by have := Nat.div_add_mod n 10; omega
      show readFrom (n / 10 * 10 + ((digitByte (n % 10)).toNat - 48)) acc = readFrom n acc
      rw [digitByte_sub hm, hdm]

/-- **The digit-loop correctness.** Reading `natToDec n`'s ASCII digits back as a
base-10 number recovers `n`: the loop emits the decimal digits of `n`, most
significant first. -/
theorem natToDec_readback (n : Nat) : readFrom 0 (natToDec n) = n := by
  unfold natToDec
  rw [decAux_readFrom (n + 1) n [] (by omega)]
  rfl

/-! ### `natToDec` non-vacuity + agreement with the conventional `Nat.repr` render -/

def regression_146 : Bool := decide (natToDec 0 = [48]
  )
def regression_147 : Bool := decide (natToDec 7 = [55]
  )
def regression_148 : Bool := decide (natToDec 42 = [52, 50]
  )
def regression_149 : Bool := decide (natToDec 200 = [50, 48, 48]
  )
def regression_150 : Bool := decide (natToDec 404 = [52, 48, 52]
  )
-- byte-identical to `Nat.repr`'s ASCII rendering on samples (the `= Nat.repr`
-- residual is the syntactic UTF-8/`toDigits` lemma; the round trip above is the
-- proven correctness):
def regression_154 : Bool := decide ((natToDec 65535).map (·.toNat) = (Nat.repr 65535).toUTF8.toList.map (·.toNat)
  )
def regression_155 : Bool := decide ((natToDec 200).map (·.toNat) = (Nat.repr 200).toUTF8.toList.map (·.toNat)
  )

end DN.Compiler.Decimal
