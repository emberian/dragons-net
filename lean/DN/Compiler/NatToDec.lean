-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Div10
import DN.Compiler.Region
import DN.Compiler.Bytes
import DN.Compiler.Decimal

/-!
# DN.Compiler.NatToDec

Rendering a natural number as decimal ASCII bytes, as a Pancake program. A digit costs no
clock: the quotient comes from `Div10`, so the only clocked step is the loop that walks the
digits, and the whole render fits in a budget that does not depend on the number.
-/

namespace DN.Compiler.NatToDec

open DN.Compiler DN.Compiler.Region DN.Compiler.Decimal
open DN.Compiler.Div10 DN.Compiler.Bytes

variable {σ : Type}

/-! ## 0. Word-address algebra (64-bit, no wrap side-conditions needed for
subtraction cancellation) -/

theorem ofNat64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  omega

theorem ofNat64_ne_zero {m : Nat} (h0 : m ≠ 0) (hlt : m < 2 ^ 64) :
    BitVec.ofNat 64 m ≠ (0 : Word) := by
  intro h
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at h'
  omega

/-- The descending address walk, one step: `p - (j+1) = (p - 1) - j`. -/
theorem sub_ofNat_succ (p : Word) (j : Nat) :
    p - BitVec.ofNat 64 (j + 1) = (p - BitVec.ofNat 64 1) - BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- Left-cancellation for word subtraction (exact — no non-wrap condition). -/
theorem sub_left_cancel {p x y : Word} (h : p - x = p - y) : x = y := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_sub] at h'
  have hx := x.isLt
  have hy := y.isLt
  have hp := p.isLt
  apply BitVec.eq_of_toNat_eq
  omega

/-! ## 1. `decAux`/`natToDec` structural lemmas (the spec side of the loop) -/

/-- `decAux` ignores surplus fuel. -/
theorem decAux_fuel_irrel :
    ∀ (f g n : Nat) (acc : Bytes), n < f → n < g → decAux f n acc = decAux g n acc := by
  intro f
  induction f with
  | zero => intro g n acc hf _; omega
  | succ f ih =>
    intro g n acc hf hg
    cases g with
    | zero => omega
    | succ g =>
      by_cases hn : n < 10
      · have h1 : decAux (f + 1) n acc = digitByte n :: acc := if_pos hn
        have h2 : decAux (g + 1) n acc = digitByte n :: acc := if_pos hn
        rw [h1, h2]
      · have h1 : decAux (f + 1) n acc = decAux f (n / 10) (digitByte (n % 10) :: acc) :=
          if_neg hn
        have h2 : decAux (g + 1) n acc = decAux g (n / 10) (digitByte (n % 10) :: acc) :=
          if_neg hn
        have hd : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
        rw [h1, h2]
        exact ih g (n / 10) _ (by omega) (by omega)

/-- The accumulator is an append: `decAux f n acc = decAux f n [] ++ acc`. -/
theorem decAux_append :
    ∀ (f n : Nat) (acc : Bytes), n < f → decAux f n acc = decAux f n [] ++ acc := by
  intro f
  induction f with
  | zero => intro n acc h; omega
  | succ f ih =>
    intro n acc h
    by_cases hn : n < 10
    · have h1 : decAux (f + 1) n acc = digitByte n :: acc := if_pos hn
      have h2 : decAux (f + 1) n ([] : Bytes) = digitByte n :: [] := if_pos hn
      rw [h1, h2]
      rfl
    · have h1 : decAux (f + 1) n acc = decAux f (n / 10) (digitByte (n % 10) :: acc) :=
        if_neg hn
      have h2 : decAux (f + 1) n ([] : Bytes)
          = decAux f (n / 10) (digitByte (n % 10) :: []) := if_neg hn
      have hd : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have hdf : n / 10 < f := by omega
      rw [h1, h2, ih (n / 10) _ hdf, ih (n / 10) (digitByte (n % 10) :: []) hdf,
          List.append_assoc]
      rfl

/-- One digit: `natToDec m = [digitByte m]` for `m < 10`. -/
theorem natToDec_lt10 {m : Nat} (hm : m < 10) : natToDec m = [digitByte m] := by
  show decAux (m + 1) m [] = [digitByte m]
  exact if_pos hm

/-- The peel: for `m ≥ 10` the render is the quotient's render with the low
digit appended — EXACTLY what one digit step plus the recursion realises. -/
theorem natToDec_split {m : Nat} (hm : 10 ≤ m) :
    natToDec m = natToDec (m / 10) ++ [digitByte (m % 10)] := by
  have hdiv : m / 10 < m := Nat.div_lt_self (by omega) (by omega)
  have h1 : natToDec m = decAux m (m / 10) (digitByte (m % 10) :: []) := if_neg (by omega)
  rw [h1, decAux_append m (m / 10) _ hdiv,
      decAux_fuel_irrel m (m / 10 + 1) (m / 10) [] hdiv (by omega)]
  rfl

theorem natToDec_length_pos (m : Nat) : 0 < (natToDec m).length := by
  by_cases hm : m < 10
  · rw [natToDec_lt10 hm]; simp
  · rw [natToDec_split (by omega)]; simp

theorem natToDec_length_le (m : Nat) : (natToDec m).length ≤ m + 1 := by
  by_cases hm : m < 10
  · rw [natToDec_lt10 hm]; simp
  · rw [natToDec_split (by omega)]
    have ih := natToDec_length_le (m / 10)
    have hd : m / 10 < m := Nat.div_lt_self (by omega) (by omega)
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-! ## 2. Control-flow helpers over `PancakeSem` -/

/-- One `While` iteration for ANY true guard word and a body consuming any
number of ticks: guard `w ≠ 0`, body runs on `dec_clock` to `(NONE, sb)`,
`fix_clock` collapses since `sb.clock ≤ s.clock - 1`. -/
theorem while_iter_le (o : Oracle σ) {e : PancakeExp} {c : PancakeProg}
    {s sb : PancakeState σ} {w : Word}
    (hg : eval s e = some w) (hw : w ≠ 0) (hclk : s.clock ≠ 0)
    (hbody : PancakeSem o c (decClock s) = (none, sb))
    (hsbclk : sb.clock ≤ s.clock - 1) :
    PancakeSem o (.while_ e c) s = PancakeSem o (.while_ e c) sb := by
  have hcollapse : ({ sb with clock := min (s.clock - 1) sb.clock } : PancakeState σ) = sb := by
    have hm : min (s.clock - 1) sb.clock = sb.clock := by omega
    rw [hm]
  rw [PancakeSem]
  simp only [hg, ne_eq, eq_false hw, not_false_eq_true, if_true, hclk, if_false,
             clampClock, hbody, hcollapse]

/-- The `While` exit: guard false (`= 0`) leaves the state untouched. -/
theorem while_exit (o : Oracle σ) {e : PancakeExp} {c : PancakeProg}
    {s : PancakeState σ} (hg : eval s e = some 0) :
    PancakeSem o (.while_ e c) s = (none, s) := by
  rw [PancakeSem, hg]; simp



/-! ## 3. One digit, without a division loop -/

/-- The working names of the digit step. They are declared once, ahead of the loop, and
assigned inside it: Pancake rejects a second declaration of a name already in scope. -/
def scratch : List String := ["hi", "lo", "qh", "rh", "t", "qt", "q"]

/-- The three statements that place a digit: step the pointer back, store the digit, and
carry the quotient into `n`. No clock is spent. -/
def digitTail : PancakeProg :=
  .seq (.assign "p" (.op .sub (.var "p") (.const 1)))
  (.seq (.storeByte (.var "p")
          (.op .add (.op .sub (.var "n") (.mul (.var "q") (.const 10))) (.const 48)))
        (.assign "n" (.var "q")))

/-- The same three statements with the rest of the block after them: the shape the block
takes when the loop follows the first digit. -/
def digitTailK (rest : PancakeProg) : PancakeProg :=
  .seq (.assign "p" (.op .sub (.var "p") (.const 1)))
  (.seq (.storeByte (.var "p")
          (.op .add (.op .sub (.var "n") (.mul (.var "q") (.const 10))) (.const 48)))
  (.seq (.assign "n" (.var "q")) rest))

/-- The seven working values, declared around `cont`. A declaration scopes over the rest of
its block, so everything the loop does happens inside these seven. -/
def digitPrefix (cont : PancakeProg) : PancakeProg :=
  .dec "hi" (.shiftR (.var "n") (.const 32))
  (.dec "lo" (.op .and_ (.var "n") (.const 4294967295))
  (.dec "qh" (.shiftR (.mul (.var "hi") (.const 3435973837)) (.const 35))
  (.dec "rh" (.op .sub (.var "hi") (.mul (.var "qh") (.const 10)))
  (.dec "t" (.op .add (.mul (.var "rh") (.const 6)) (.var "lo"))
  (.dec "qt" (.shiftR (.mul (.var "t") (.const 3435973837)) (.const 35))
  (.dec "q" (.op .add (.op .add (.mul (.var "qh") (.const 4294967296))
                                (.mul (.var "rh") (.const 429496729))) (.var "qt"))
  cont))))))

/-- One decimal digit inside the loop: the same arithmetic as the declarations, assigning
the names they introduced. The quotient comes from a multiplication, so no statement here
costs clock. -/
def digitBodyAssign : PancakeProg :=
  .seq (.assign "hi" (.shiftR (.var "n") (.const 32)))
  (.seq (.assign "lo" (.op .and_ (.var "n") (.const 4294967295)))
  (.seq (.assign "qh" (.shiftR (.mul (.var "hi") (.const 3435973837)) (.const 35)))
  (.seq (.assign "rh" (.op .sub (.var "hi") (.mul (.var "qh") (.const 10))))
  (.seq (.assign "t" (.op .add (.mul (.var "rh") (.const 6)) (.var "lo")))
  (.seq (.assign "qt" (.shiftR (.mul (.var "t") (.const 3435973837)) (.const 35)))
  (.seq (.assign "q" (.op .add (.op .add (.mul (.var "qh") (.const 4294967296))
                                         (.mul (.var "rh") (.const 429496729))) (.var "qt")))
        digitTail))))))

/-- What the seven names hold once they are bound: the halves of `w`, the two partial
quotients, and `w / 10` in `q`. -/
def scratchLocals (lc : String → Option Value) (w : Word) : String → Option Value :=
  setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal lc
    "hi" (w >>> 32))
    "lo" (w &&& 4294967295))
    "qh" (((w >>> 32) * 3435973837) >>> 35))
    "rh" ((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10))
    "t" (((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10) * 6 + (w &&& 4294967295)))
    "qt" (((((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10) * 6
             + (w &&& 4294967295)) * 3435973837) >>> 35))
    "q" (div10w w)

/-- Leaving the declarations puts back what they shadowed — `res_var`, once per name. -/
def restoreScratch (lc old : String → Option Value) : String → Option Value :=
  fun k => if k ∈ scratch then old k else lc k

theorem restoreScratch_ne (lc old : String → Option Value) {k : String} (hk : k ∉ scratch) :
    restoreScratch lc old k = lc k := by
  simp [restoreScratch, hk]

theorem restoreScratch_mem (lc old : String → Option Value) {k : String} (hk : k ∈ scratch) :
    restoreScratch lc old k = old k := by
  simp [restoreScratch, hk]

theorem scratchLocals_ne (lc : String → Option Value) (w : Word) {k : String}
    (hk : k ∉ scratch) : scratchLocals lc w k = lc k := by
  simp only [scratch, List.mem_cons, not_or] at hk
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hk
  simp [scratchLocals, setLocal, h1, h2, h3, h4, h5, h6, h7]

theorem scratchLocals_bound (lc : String → Option Value) (w : Word) {k : String}
    (hk : k ∈ scratch) : (scratchLocals lc w k).isSome = true := by
  simp only [scratch] at hk
  rcases List.mem_cons.mp hk with h | hk1
  · subst h; simp [scratchLocals, setLocal]
  rcases List.mem_cons.mp hk1 with h | hk2
  · subst h; simp [scratchLocals, setLocal]
  rcases List.mem_cons.mp hk2 with h | hk3
  · subst h; simp [scratchLocals, setLocal]
  rcases List.mem_cons.mp hk3 with h | hk4
  · subst h; simp [scratchLocals, setLocal]
  rcases List.mem_cons.mp hk4 with h | hk5
  · subst h; simp [scratchLocals, setLocal]
  rcases List.mem_cons.mp hk5 with h | hk6
  · subst h; simp [scratchLocals, setLocal]
  rcases List.mem_cons.mp hk6 with h | hk7
  · subst h; simp [scratchLocals, setLocal]
  simp at hk7

theorem scratchLocals_q (lc : String → Option Value) (w : Word) :
    scratchLocals lc w "q" = some (div10w w) := by
  simp [scratchLocals, setLocal]

/-- The pointer step and the byte store, whatever follows them: neither costs clock, so the
run continues from the state that has the digit in memory. -/
theorem digitStore_sem (o : Oracle σ) {w q p0 : Word} {s : PancakeState σ} {rest : PancakeProg}
    (hn : s.locals "n" = some w) (hp : s.locals "p" = some p0) (hq : s.locals "q" = some q)
    (hdm : s.memaddrs (byteAlign (p0 - 1)) = true) :
    PancakeSem o (.seq (.assign "p" (.op .sub (.var "p") (.const 1)))
        (.seq (.storeByte (.var "p")
          (.op .add (.op .sub (.var "n") (.mul (.var "q") (.const 10))) (.const 48))) rest)) s
      = PancakeSem o rest
          { s with locals := setLocal s.locals "p" (p0 - 1),
                   memory := putByte s.memory s.be (p0 - 1) ((w - q * 10 + 48).setWidth 8) } := by
  have ep : eval s (.op .sub (.var "p") (.const 1)) = some (p0 - 1) := by simp [eval, hp]
  rw [seq_step o (sem_assign (oracle := o) ep hp) (by simp)]
  have hp1 : (setLocal s.locals "p" (p0 - 1)) "p" = some (p0 - 1) := setLocal_same _ _ _
  have ed : eval ({ s with locals := setLocal s.locals "p" (p0 - 1) } : PancakeState σ)
      (.op .add (.op .sub (.var "n") (.mul (.var "q") (.const 10))) (.const 48))
      = some (w - q * 10 + 48) := by
    simp [eval, setLocal, hn, hq]
  have ea : eval ({ s with locals := setLocal s.locals "p" (p0 - 1) } : PancakeState σ)
      (.var "p") = some (p0 - 1) := hp1
  have h2 : PancakeSem o (.storeByte (.var "p")
        (.op .add (.op .sub (.var "n") (.mul (.var "q") (.const 10))) (.const 48)))
      ({ s with locals := setLocal s.locals "p" (p0 - 1) } : PancakeState σ)
      = (none, { s with locals := setLocal s.locals "p" (p0 - 1),
                        memory := putByte s.memory s.be (p0 - 1)
                          ((w - q * 10 + 48).setWidth 8) }) := by
    rw [PancakeSem]
    simp only [ea, ed, memStore_eq _ _ _ _ _ hdm]
  exact seq_step o h2 (by simp)

theorem digitTail_sem (o : Oracle σ) {w q p0 : Word} {s : PancakeState σ}
    (hn : s.locals "n" = some w) (hp : s.locals "p" = some p0) (hq : s.locals "q" = some q)
    (hdm : s.memaddrs (byteAlign (p0 - 1)) = true) :
    PancakeSem o digitTail s
      = (none, { s with locals := setLocal (setLocal s.locals "p" (p0 - 1)) "n" q,
                        memory := putByte s.memory s.be (p0 - 1)
                          ((w - q * 10 + 48).setWidth 8) }) := by
  simp only [digitTail]
  rw [digitStore_sem o hn hp hq hdm]
  have hq1 : (setLocal s.locals "p" (p0 - 1)) "q" = some q := by
    rw [setLocal_ne _ _ _ (by decide)]; exact hq
  have hn1 : (setLocal s.locals "p" (p0 - 1)) "n" = some w := by
    rw [setLocal_ne _ _ _ (by decide)]; exact hn
  exact sem_assign (oracle := o) hq1 hn1

theorem digitTailK_sem (o : Oracle σ) {w q p0 : Word} {s : PancakeState σ} {rest : PancakeProg}
    (hn : s.locals "n" = some w) (hp : s.locals "p" = some p0) (hq : s.locals "q" = some q)
    (hdm : s.memaddrs (byteAlign (p0 - 1)) = true) :
    PancakeSem o (digitTailK rest) s
      = PancakeSem o rest { s with locals := setLocal (setLocal s.locals "p" (p0 - 1)) "n" q,
                                   memory := putByte s.memory s.be (p0 - 1)
                                     ((w - q * 10 + 48).setWidth 8) } := by
  simp only [digitTailK]
  rw [digitStore_sem o hn hp hq hdm]
  have hq1 : (setLocal s.locals "p" (p0 - 1)) "q" = some q := by
    rw [setLocal_ne _ _ _ (by decide)]; exact hq
  have hn1 : (setLocal s.locals "p" (p0 - 1)) "n" = some w := by
    rw [setLocal_ne _ _ _ (by decide)]; exact hn
  exact seq_step o (sem_assign (oracle := o) hq1 hn1) (by simp)

/-- **The declarations.** They bind the seven names to the digit arithmetic of `w`, run
`cont` in that scope, and put the shadowed bindings back on the way out. -/
theorem digitPrefix_sem (o : Oracle σ) {cont : PancakeProg} {w : Word} {res : Option Result}
    {s s2 : PancakeState σ} (hn : s.locals "n" = some w)
    (hcont : PancakeSem o cont { s with locals := scratchLocals s.locals w } = (res, s2)) :
    PancakeSem o (digitPrefix cont) s
      = (res, { s2 with locals := restoreScratch s2.locals s.locals }) := by
  have e1 : eval (s : PancakeState σ) (.shiftR (.var "n") (.const 32)) = some (w >>> 32) := by
    simp [eval, hn, BitVec.toNat_ofNat]
  have e2 : eval ({ s with locals := setLocal (s.locals) "hi" (w >>> 32) } : PancakeState σ) (.op .and_ (.var "n") (.const 4294967295)) = some (w &&& 4294967295) := by
    simp [eval, setLocal, hn]
  have e3 : eval ({ s with locals := setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295) } : PancakeState σ) (.shiftR (.mul (.var "hi") (.const 3435973837)) (.const 35)) = some (((w >>> 32) * 3435973837) >>> 35) := by
    simp [eval, setLocal, BitVec.toNat_ofNat]
  have e4 : eval ({ s with locals := setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35) } : PancakeState σ) (.op .sub (.var "hi") (.mul (.var "qh") (.const 10))) = some ((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10) := by
    simp [eval, setLocal]
  have e5 : eval ({ s with locals := setLocal (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" ((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10) } : PancakeState σ) (.op .add (.mul (.var "rh") (.const 6)) (.var "lo")) = some (((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10) * 6 + (w &&& 4294967295)) := by
    simp [eval, setLocal]
  have e6 : eval ({ s with locals := setLocal (setLocal (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" ((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10)) "t" (((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10) * 6 + (w &&& 4294967295)) } : PancakeState σ) (.shiftR (.mul (.var "t") (.const 3435973837)) (.const 35)) = some (((((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10) * 6 + (w &&& 4294967295)) * 3435973837) >>> 35) := by
    simp [eval, setLocal, BitVec.toNat_ofNat]
  have e7 : eval ({ s with locals := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" ((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10)) "t" (((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10) * 6 + (w &&& 4294967295))) "qt" (((((w >>> 32) - (((w >>> 32) * 3435973837) >>> 35) * 10) * 6 + (w &&& 4294967295)) * 3435973837) >>> 35) } : PancakeState σ)
      (.op .add (.op .add (.mul (.var "qh") (.const 4294967296))
                          (.mul (.var "rh") (.const 429496729))) (.var "qt"))
      = some (div10w w) := by
    simp [eval, setLocal, div10w]
  have hrun := sem_dec (oracle := o) e1 (sem_dec (oracle := o) e2 (sem_dec (oracle := o) e3
    (sem_dec (oracle := o) e4 (sem_dec (oracle := o) e5 (sem_dec (oracle := o) e6
      (sem_dec (oracle := o) e7 hcont))))))
  refine hrun.trans ?_
  have hpair : ∀ a b : String → Option Value, a = b →
      ((res, { s2 with locals := a }) : Option Result × PancakeState σ)
        = (res, { s2 with locals := b }) := by
    intro a b h; rw [h]
  apply hpair
  funext k
  by_cases h1 : k = "hi" <;> by_cases h2 : k = "lo" <;> by_cases h3 : k = "qh" <;>
    by_cases h4 : k = "rh" <;> by_cases h5 : k = "t" <;> by_cases h6 : k = "qt" <;>
    by_cases h7 : k = "q" <;>
    simp [resVar, setLocal, restoreScratch, scratch, h1, h2, h3, h4, h5, h6, h7]

/-- **The first digit**, rendered in the scope the declarations opened: the loop continues
from a state with the quotient in `n`, the digit in memory, and the seven names bound. -/
theorem digitFirst_sem (o : Oracle σ) {w p0 : Word} {s : PancakeState σ} {loop : PancakeProg}
    (hn : s.locals "n" = some w) (hp : s.locals "p" = some p0)
    (hdm : s.memaddrs (byteAlign (p0 - 1)) = true) :
    ∃ sb, PancakeSem o (digitTailK loop) { s with locals := scratchLocals s.locals w }
        = PancakeSem o loop sb ∧
      sb.locals "n" = some (div10w w) ∧
      sb.locals "p" = some (p0 - 1) ∧
      sb.clock = s.clock ∧
      sb.memory = putByte s.memory s.be (p0 - 1)
        (BitVec.setWidth 8 (w - div10w w * 10 + 48)) ∧
      sb.memaddrs = s.memaddrs ∧ sb.be = s.be ∧ sb.baseAddr = s.baseAddr ∧
      (∀ x, x ∈ scratch → (sb.locals x).isSome = true) ∧
      (∀ key, key ≠ "n" → key ≠ "p" → key ∉ scratch → sb.locals key = s.locals key) := by
  have hn' : (scratchLocals s.locals w) "n" = some w := by
    rw [scratchLocals_ne _ _ (by decide)]; exact hn
  have hp' : (scratchLocals s.locals w) "p" = some p0 := by
    rw [scratchLocals_ne _ _ (by decide)]; exact hp
  refine ⟨_, digitTailK_sem o (s := { s with locals := scratchLocals s.locals w })
    hn' hp' (scratchLocals_q s.locals w) hdm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setLocal]
  · simp [setLocal]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro x hx
    have hxn : x ≠ "n" := by intro h; subst h; simp [scratch] at hx
    have hxp : x ≠ "p" := by intro h; subst h; simp [scratch] at hx
    simpa [setLocal, hxn, hxp] using scratchLocals_bound s.locals w hx
  · intro key hkn hkp hks
    simpa [setLocal, hkn, hkp] using scratchLocals_ne s.locals w hks

/-- **One loop iteration.** The seven names are already in scope; the body assigns them,
writes the digit, and leaves `w / 10` in `n`. -/
theorem digitBodyAssign_sem (o : Oracle σ) {w p0 : Word} {s : PancakeState σ}
    (hn : s.locals "n" = some w) (hp : s.locals "p" = some p0)
    (bound : ∀ x, x ∈ scratch → (s.locals x).isSome = true)
    (hdm : s.memaddrs (byteAlign (p0 - 1)) = true) :
    ∃ s', PancakeSem o digitBodyAssign s = (none, s') ∧
      s'.locals "n" = some (div10w w) ∧
      s'.locals "p" = some (p0 - 1) ∧
      s'.clock = s.clock ∧
      s'.memory = putByte s.memory s.be (p0 - 1)
        (BitVec.setWidth 8 (w - div10w w * 10 + 48)) ∧
      s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.baseAddr = s.baseAddr ∧
      (∀ x, x ∈ scratch → (s'.locals x).isSome = true) ∧
      (∀ key, key ≠ "n" → key ≠ "p" → key ∉ scratch → s'.locals key = s.locals key) := by
  simp only [digitBodyAssign]
  obtain ⟨old1, b1⟩ : ∃ v, (s.locals) "hi" = some v :=
    Option.isSome_iff_exists.mp (by simpa [setLocal] using bound "hi" (by decide))
  have e1 : eval s (.shiftR (.var "n") (.const 32)) = some (w >>> 32) := by
    simp [eval, hn]
  obtain ⟨old2, b2⟩ : ∃ v, (setLocal (s.locals) "hi" (w >>> 32)) "lo" = some v :=
    Option.isSome_iff_exists.mp (by simpa [setLocal] using bound "lo" (by decide))
  have e2 : eval ({ s with locals := setLocal (s.locals) "hi" (w >>> 32) } : PancakeState σ) (.op .and_ (.var "n") (.const 4294967295)) = some (w &&& 4294967295) := by
    simp [eval, setLocal, hn]
  obtain ⟨old3, b3⟩ : ∃ v, (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" = some v :=
    Option.isSome_iff_exists.mp (by simpa [setLocal] using bound "qh" (by decide))
  have e3 : eval ({ s with locals := setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295) } : PancakeState σ) (.shiftR (.mul (.var "hi") (.const 3435973837)) (.const 35)) = some (((w >>> 32) * 3435973837) >>> 35) := by
    simp [eval, setLocal]
  obtain ⟨old4, b4⟩ : ∃ v, (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" = some v :=
    Option.isSome_iff_exists.mp (by simpa [setLocal] using bound "rh" (by decide))
  have e4 : eval ({ s with locals := setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35) } : PancakeState σ) (.op .sub (.var "hi") (.mul (.var "qh") (.const 10))) = some ((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) := by
    simp [eval, setLocal]
  obtain ⟨old5, b5⟩ : ∃ v, (setLocal (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" ((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10)) "t" = some v :=
    Option.isSome_iff_exists.mp (by simpa [setLocal] using bound "t" (by decide))
  have e5 : eval ({ s with locals := setLocal (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" ((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) } : PancakeState σ) (.op .add (.mul (.var "rh") (.const 6)) (.var "lo")) = some (((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) * 6 + (w &&& 4294967295)) := by
    simp [eval, setLocal]
  obtain ⟨old6, b6⟩ : ∃ v, (setLocal (setLocal (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" ((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10)) "t" (((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) * 6 + (w &&& 4294967295))) "qt" = some v :=
    Option.isSome_iff_exists.mp (by simpa [setLocal] using bound "qt" (by decide))
  have e6 : eval ({ s with locals := setLocal (setLocal (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" ((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10)) "t" (((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) * 6 + (w &&& 4294967295)) } : PancakeState σ) (.shiftR (.mul (.var "t") (.const 3435973837)) (.const 35)) = some ((((((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) * 6 + (w &&& 4294967295))) * 3435973837) >>> 35) := by
    simp [eval, setLocal]
  obtain ⟨old7, b7⟩ : ∃ v, (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" ((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10)) "t" (((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) * 6 + (w &&& 4294967295))) "qt" ((((((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) * 6 + (w &&& 4294967295))) * 3435973837) >>> 35)) "q" = some v :=
    Option.isSome_iff_exists.mp (by simpa [setLocal] using bound "q" (by decide))
  have e7 : eval ({ s with locals := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (s.locals) "hi" (w >>> 32)) "lo" (w &&& 4294967295)) "qh" (((w >>> 32) * 3435973837) >>> 35)) "rh" ((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10)) "t" (((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) * 6 + (w &&& 4294967295))) "qt" ((((((w >>> 32) - ((((w >>> 32) * 3435973837) >>> 35)) * 10) * 6 + (w &&& 4294967295))) * 3435973837) >>> 35) } : PancakeState σ) (.op .add (.op .add (.mul (.var "qh") (.const 4294967296)) (.mul (.var "rh") (.const 429496729))) (.var "qt")) = some (div10w w) := by
    simp [eval, setLocal, div10w]
  rw [seq_step o (sem_assign (oracle := o) e1 b1) (by simp),
      seq_step o (sem_assign (oracle := o) e2 b2) (by simp),
      seq_step o (sem_assign (oracle := o) e3 b3) (by simp),
      seq_step o (sem_assign (oracle := o) e4 b4) (by simp),
      seq_step o (sem_assign (oracle := o) e5 b5) (by simp),
      seq_step o (sem_assign (oracle := o) e6 b6) (by simp),
      seq_step o (sem_assign (oracle := o) e7 b7) (by simp)]
  have hnf : (scratchLocals s.locals w) "n" = some w := by
    rw [scratchLocals_ne _ _ (by decide)]; exact hn
  have hpf : (scratchLocals s.locals w) "p" = some p0 := by
    rw [scratchLocals_ne _ _ (by decide)]; exact hp
  have htail := digitTail_sem (w := w) (q := div10w w) (p0 := p0) (o := o)
    (s := { s with locals := scratchLocals s.locals w })
    hnf hpf (scratchLocals_q s.locals w) hdm
  refine ⟨_, htail, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setLocal]
  · simp [setLocal]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro x hx
    have hxn : x ≠ "n" := by intro h; subst h; simp [scratch] at hx
    have hxp : x ≠ "p" := by intro h; subst h; simp [scratch] at hx
    simpa [setLocal, hxn, hxp] using scratchLocals_bound s.locals w hx
  · intro key hkn hkp hks
    simpa [setLocal, hkn, hkp] using scratchLocals_ne s.locals w hks

theorem div10w_ofNat {m : Nat} (h : m < 2 ^ 64) :
    div10w (BitVec.ofNat 64 m) = BitVec.ofNat 64 (m / 10) := by
  have ht : (div10w (BitVec.ofNat 64 m)).toNat = m / 10 := by
    rw [div10w_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  have : (div10w (BitVec.ofNat 64 m)).toNat = (BitVec.ofNat 64 (m / 10)).toNat := by
    rw [ht, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact BitVec.eq_of_toNat_eq this

theorem digit_byte_eq {m : Nat} (h : m < 2 ^ 64) :
    ((BitVec.ofNat 64 m - div10w (BitVec.ofNat 64 m) * 10 + 48).setWidth 8)
      = digitByte (m % 10) := by
  rw [div10w_ofNat h]
  have hq : (BitVec.ofNat 64 (m / 10) * 10 : Word).toNat = m / 10 * 10 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m / 10 < 2 ^ 64)]
    show m / 10 * (10 % 2 ^ 64) % 2 ^ 64 = m / 10 * 10
    rw [Nat.mod_eq_of_lt (by omega : (10 : Nat) < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have hsub : (BitVec.ofNat 64 m - BitVec.ofNat 64 (m / 10) * 10 + 48 : Word).toNat
      = m % 10 + 48 := by
    rw [BitVec.toNat_add, BitVec.toNat_sub, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
    have c48 : (48 : Word).toNat = 48 := rfl
    rw [c48]
    have hinner : (2 ^ 64 - m / 10 * 10 + m) % 2 ^ 64 = m % 10 := by omega
    rw [hinner]
    omega
  have : ((BitVec.ofNat 64 m - BitVec.ofNat 64 (m / 10) * 10 + 48 : Word).setWidth 8).toNat
      = (digitByte (m % 10)).toNat := by
    rw [BitVec.toNat_setWidth, hsub]
    show (m % 10 + 48) % 2 ^ 8 = (BitVec.ofNat 8 (48 + m % 10)).toNat
    rw [BitVec.toNat_ofNat]
    omega
  exact BitVec.eq_of_toNat_eq this

/-- The first digit in terms of the number it renders. -/
theorem digitFirst_nat (o : Oracle σ) {m : Nat} {p0 : Word} {s : PancakeState σ}
    {loop : PancakeProg}
    (hn : s.locals "n" = some (BitVec.ofNat 64 m)) (hp : s.locals "p" = some p0)
    (hm : m < 2 ^ 64) (hdm : s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 1)) = true) :
    ∃ sb, PancakeSem o (digitTailK loop)
          { s with locals := scratchLocals s.locals (BitVec.ofNat 64 m) }
        = PancakeSem o loop sb ∧
      sb.locals "n" = some (BitVec.ofNat 64 (m / 10)) ∧
      sb.locals "p" = some (p0 - BitVec.ofNat 64 1) ∧
      sb.clock = s.clock ∧
      sb.memory = putByte s.memory s.be (p0 - BitVec.ofNat 64 1) (digitByte (m % 10)) ∧
      sb.memaddrs = s.memaddrs ∧ sb.be = s.be ∧ sb.baseAddr = s.baseAddr ∧
      (∀ x, x ∈ scratch → (sb.locals x).isSome = true) ∧
      (∀ key, key ≠ "n" → key ≠ "p" → key ∉ scratch → sb.locals key = s.locals key) := by
  obtain ⟨sb, hrun, hbn, hbp, hbclk, hbmem, hbma, hbbe, hbba, hbb, hbfr⟩ :=
    digitFirst_sem o (loop := loop) hn hp hdm
  refine ⟨sb, hrun, ?_, hbp, hbclk, ?_, hbma, hbbe, hbba, hbb, hbfr⟩
  · rw [hbn, div10w_ofNat hm]
  · rw [hbmem, digit_byte_eq hm]
    rfl

/-- One loop iteration in terms of the number it renders. -/
theorem digitBodyAssign_nat (o : Oracle σ) {m : Nat} {p0 : Word} {s : PancakeState σ}
    (hn : s.locals "n" = some (BitVec.ofNat 64 m)) (hp : s.locals "p" = some p0)
    (bound : ∀ x, x ∈ scratch → (s.locals x).isSome = true)
    (hm : m < 2 ^ 64) (hdm : s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 1)) = true) :
    ∃ s', PancakeSem o digitBodyAssign s = (none, s') ∧
      s'.locals "n" = some (BitVec.ofNat 64 (m / 10)) ∧
      s'.locals "p" = some (p0 - BitVec.ofNat 64 1) ∧
      s'.clock = s.clock ∧
      s'.memory = putByte s.memory s.be (p0 - BitVec.ofNat 64 1) (digitByte (m % 10)) ∧
      s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.baseAddr = s.baseAddr ∧
      (∀ x, x ∈ scratch → (s'.locals x).isSome = true) ∧
      (∀ key, key ≠ "n" → key ≠ "p" → key ∉ scratch → s'.locals key = s.locals key) := by
  obtain ⟨s', hrun, hn', hp', hclk', hmem', hma', hbe', hba', hb', hfr'⟩ :=
    digitBodyAssign_sem o hn hp bound hdm
  refine ⟨s', hrun, ?_, hp', hclk', ?_, hma', hbe', hba', hb', hfr'⟩
  · rw [hn', div10w_ofNat hm]
  · rw [hmem', digit_byte_eq hm]
    rfl

/-! ## 4. The digit-render postcondition -/

/-- Postcondition of rendering `m`'s decimal digits with end-pointer `p0`:
`n = 0`, `p = p0 - L`, the `L = (natToDec m).length` ASCII digit bytes laid at
`[p0 - L, p0)` most-significant first, every OTHER byte (read through
`mem_load_byte`) and every other state field / local framed. `skip` names the
locals left out of the frame — the loop's working names, which the declarations
around it put back. -/
abbrev RenderPostFrame (skip : List String) (m : Nat) (p0 : Word)
    (s0 s' : PancakeState σ) : Prop :=
  s'.locals "n" = some (0 : Word) ∧
  s'.locals "p" = some (p0 - BitVec.ofNat 64 (natToDec m).length) ∧
  (∀ j b, (natToDec m)[j]? = some b →
    memLoadByte s'.memory s'.memaddrs s'.be
      (p0 - BitVec.ofNat 64 ((natToDec m).length - j)) = some b) ∧
  (∀ a, (∀ j, j < (natToDec m).length → a ≠ p0 - BitVec.ofNat 64 (j + 1)) →
    memLoadByte s'.memory s'.memaddrs s'.be a
      = memLoadByte s0.memory s0.memaddrs s0.be a) ∧
  s'.memaddrs = s0.memaddrs ∧ s'.be = s0.be ∧ s'.baseAddr = s0.baseAddr ∧
  (∀ key, key ≠ "n" → key ≠ "p" → key ∉ skip → s'.locals key = s0.locals key)

/-- The render's postcondition with every local framed. -/
abbrev RenderPost (m : Nat) (p0 : Word) (s0 s' : PancakeState σ) : Prop :=
  RenderPostFrame [] m p0 s0 s'

/-- The `m < 10` case: ONE digit step (already run, post-state `sb`) IS the
whole render. -/
theorem single_digit_post {skip : List String} {m : Nat} {p0 : Word}
    {s0 sb : PancakeState σ} (hm10 : m < 10)
    (hsbn : sb.locals "n" = some (BitVec.ofNat 64 (m / 10)))
    (hsbp : sb.locals "p" = some (p0 - BitVec.ofNat 64 1))
    (hsbmem : sb.memory = putByte s0.memory s0.be (p0 - BitVec.ofNat 64 1)
      (digitByte (m % 10)))
    (hsbma : sb.memaddrs = s0.memaddrs) (hsbbe : sb.be = s0.be)
    (hsbba : sb.baseAddr = s0.baseAddr)
    (hsbfr : ∀ key, key ≠ "n" → key ≠ "p" → key ∉ skip → sb.locals key = s0.locals key)
    (hdm1 : s0.memaddrs (byteAlign (p0 - BitVec.ofNat 64 1)) = true) :
    RenderPostFrame skip m p0 s0 sb := by
  have hL : natToDec m = [digitByte m] := natToDec_lt10 hm10
  have hLen : (natToDec m).length = 1 := by rw [hL]; rfl
  have hmod : m % 10 = m := Nat.mod_eq_of_lt hm10
  refine ⟨?_, ?_, ?_, ?_, hsbma, hsbbe, hsbba, hsbfr⟩
  · rw [hsbn, Nat.div_eq_of_lt hm10]
    rfl
  · rw [hLen]
    exact hsbp
  · intro j b hjb
    rw [hL] at hjb
    cases j with
    | zero =>
      have hb : b = digitByte m := by
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hjb
        exact hjb.symm
      rw [hLen, hb, hsbmem, hsbma, hsbbe, hmod]
      exact load_putByte_same s0.memory s0.memaddrs s0.be _ _ hdm1
    | succ j =>
      simp at hjb
  · intro a ha
    have ha0 : a ≠ p0 - BitVec.ofNat 64 1 := ha 0 (by rw [hLen]; omega)
    rw [hsbmem, hsbma, hsbbe]
    exact load_putByte_diff s0.memory s0.memaddrs s0.be _ _ a ha0

/-- The `m ≥ 10` composition: one digit step peeled the low digit into
`p0 - 1` (post-state `sb`), and the recursive render of `m / 10` from `sb`
with end-pointer `p0 - 1` reached `s'`. Together they render `m`. The peeled
byte at `p0 - 1` SURVIVES the recursive run because the recursion writes only
strictly below it (its frame clause + subtraction cancellation). -/
theorem multi_digit_post {skip : List String} {m : Nat} {p0 : Word}
    {s0 sb s' : PancakeState σ} (hm10 : 10 ≤ m) (hm64 : m < 2 ^ 64)
    (hsbmem : sb.memory = putByte s0.memory s0.be (p0 - BitVec.ofNat 64 1)
      (digitByte (m % 10)))
    (hsbma : sb.memaddrs = s0.memaddrs) (hsbbe : sb.be = s0.be)
    (hsbba : sb.baseAddr = s0.baseAddr)
    (hsbfr : ∀ key, key ≠ "n" → key ≠ "p" → key ∉ skip → sb.locals key = s0.locals key)
    (hdm1 : s0.memaddrs (byteAlign (p0 - BitVec.ofNat 64 1)) = true)
    (hpost : RenderPostFrame skip (m / 10) (p0 - BitVec.ofNat 64 1) sb s') :
    RenderPostFrame skip m p0 s0 s' := by
  obtain ⟨hn', hp', hbytes, hfr, hma', hbe', hba', hlfr⟩ := hpost
  have hsplit : natToDec m = natToDec (m / 10) ++ [digitByte (m % 10)] :=
    natToDec_split hm10
  have hL'le : (natToDec (m / 10)).length ≤ m / 10 + 1 := natToDec_length_le _
  have hLm : (natToDec m).length = (natToDec (m / 10)).length + 1 := by
    rw [hsplit]
    simp
  refine ⟨hn', ?_, ?_, ?_, hma'.trans hsbma, hbe'.trans hsbbe, hba'.trans hsbba,
          fun key h1 h2 h3 => (hlfr key h1 h2 h3).trans (hsbfr key h1 h2 h3)⟩
  · rw [hLm, sub_ofNat_succ]
    exact hp'
  · -- the byte clause
    intro j b hjb
    rw [hsplit] at hjb
    by_cases hjL : j < (natToDec (m / 10)).length
    · -- an upper digit: rendered by the recursion, one address-step down
      have hjb' : (natToDec (m / 10))[j]? = some b := by
        rw [List.getElem?_append_left hjL] at hjb
        exact hjb
      have haddr : p0 - BitVec.ofNat 64 ((natToDec m).length - j)
          = (p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 ((natToDec (m / 10)).length - j) := by
        rw [hLm, show (natToDec (m / 10)).length + 1 - j
              = ((natToDec (m / 10)).length - j) + 1 from by omega,
            sub_ofNat_succ]
      rw [haddr]
      exact hbytes j b hjb'
    · -- the low digit at `p0 - 1`: stored by the digit step, framed by the recursion
      have hjlt : j < (natToDec (m / 10)).length + 1 := by
        refine (Nat.lt_or_ge j ((natToDec (m / 10)).length + 1)).elim (fun h => h)
          (fun hge => ?_)
        have hnone : (natToDec (m / 10) ++ [digitByte (m % 10)])[j]? = none := by
          apply List.getElem?_eq_none
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [hnone] at hjb
        exact absurd hjb (by simp)
      have hjeq : j = (natToDec (m / 10)).length := by omega
      subst hjeq
      have hb : b = digitByte (m % 10) := by
        rw [List.getElem?_append_right (Nat.le_refl _)] at hjb
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hjb
        exact hjb.symm
      have haddr : (natToDec m).length - (natToDec (m / 10)).length = 1 := by
        rw [hLm]
        omega
      rw [haddr, hb]
      have hane : ∀ j', j' < (natToDec (m / 10)).length →
          p0 - BitVec.ofNat 64 1 ≠ (p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 (j' + 1) := by
        intro j' hj' heq
        rw [← sub_ofNat_succ] at heq
        have h1 : (1 : Nat) = j' + 1 + 1 :=
          ofNat64_inj (by omega) (by omega) (sub_left_cancel heq)
        omega
      rw [hfr _ hane, hsbmem, hsbma, hsbbe]
      exact load_putByte_same s0.memory s0.memaddrs s0.be _ _ hdm1
  · -- the frame clause
    intro a ha
    have ha0 : a ≠ p0 - BitVec.ofNat 64 1 := ha 0 (by rw [hLm]; omega)
    have ha' : ∀ j', j' < (natToDec (m / 10)).length →
        a ≠ (p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 (j' + 1) := by
      intro j' hj'
      rw [← sub_ofNat_succ]
      exact ha (j' + 1) (by rw [hLm]; omega)
    rw [hfr a ha', hsbmem, hsbma, hsbbe]
    exact load_putByte_diff s0.memory s0.memaddrs s0.be _ _ a ha0

/-! ## 5. The digit loop and the whole render -/


/-- Twenty digits hold every machine word: `2^64 < 10^20`. -/
theorem natToDec_length_bound : ∀ (k m : Nat), m < 10 ^ (k + 1) → (natToDec m).length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro m hm
    rw [natToDec_lt10 (by omega)]
    simp
  | succ k ih =>
    intro m hm
    by_cases h10 : m < 10
    · rw [natToDec_lt10 h10]
      simp
    · have hsplit : (natToDec m).length = (natToDec (m / 10)).length + 1 := by
        rw [natToDec_split (by omega : 10 ≤ m)]
        simp
      have hq : m / 10 < 10 ^ (k + 1) := by
        have hp : 10 ^ (k + 1 + 1) = 10 ^ (k + 1) * 10 := Nat.pow_succ 10 (k + 1)
        omega
      have := ih (m / 10) hq
      omega

theorem natToDec_length_le_twenty {m : Nat} (h : m < 2 ^ 64) : (natToDec m).length ≤ 20 :=
  natToDec_length_bound 19 m (by omega)

/-- Ticks of the render: one per digit after the first, so never more than nineteen. -/
def renderFuel (m : Nat) : Nat := (natToDec m).length - 1

theorem renderFuel_le_nineteen {m : Nat} (h : m < 2 ^ 64) : renderFuel m ≤ 19 := by
  have := natToDec_length_le_twenty h
  unfold renderFuel
  omega
/-- **The digit loop, executed.** Each iteration costs one tick and renders one digit, so
the loop spends exactly as many ticks as `m` has digits. The working names are in scope
throughout, assigned rather than declared, so the loop frames every local but those. -/
theorem digitLoop_sem (o : Oracle σ) : ∀ (k m : Nat) (p0 : Word) (s : PancakeState σ),
    (natToDec m).length ≤ k + 1 → m ≠ 0 → m < 2 ^ 64 →
    s.locals "n" = some (BitVec.ofNat 64 m) → s.locals "p" = some p0 →
    (∀ x, x ∈ scratch → (s.locals x).isSome = true) →
    (∀ j, j < (natToDec m).length →
      s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 (j + 1))) = true) →
    (natToDec m).length ≤ s.clock →
    ∃ s', PancakeSem o (.while_ (.var "n") digitBodyAssign) s = (none, s') ∧
      s'.clock = s.clock - (natToDec m).length ∧ RenderPostFrame scratch m p0 s s' := by
  intro k
  induction k with
  | zero =>
    intro m p0 s hlen hm0 hm hn hp hb hdm hclk
    have h10 : m < 10 := by
      rcases Nat.lt_or_ge m 10 with h | hge
      · exact h
      exfalso
      have hsplit : (natToDec m).length = (natToDec (m / 10)).length + 1 := by
        rw [natToDec_split hge]
        simp
      have hpos := natToDec_length_pos (m / 10)
      omega
    have hLpos := natToDec_length_pos m
    have hgW : eval s (.var "n") = some (BitVec.ofNat 64 m) := hn
    have hwne : (BitVec.ofNat 64 m : Word) ≠ 0 := ofNat64_ne_zero hm0 (by omega)
    obtain ⟨sb, hbody, hbn, hbp, hbclk, hbmem, hbma, hbbe, hbba, hbb, hbfr⟩ :=
      digitBodyAssign_nat o (m := m) (p0 := p0) (s := decClock s) hn hp hb (by omega)
        (hdm 0 hLpos)
    have hclk0 : s.clock ≠ 0 := by omega
    have hsbclk : sb.clock ≤ s.clock - 1 := by rw [hbclk]; exact Nat.le_refl _
    have hstep := while_iter_le o hgW hwne hclk0 hbody hsbclk
    have hq0 : m / 10 = 0 := Nat.div_eq_of_lt h10
    have hexitg : eval sb (.var "n") = some (0 : Word) := by
      show sb.locals "n" = some (0 : Word)
      rw [hbn, hq0]; rfl
    refine ⟨sb, ?_, ?_, ?_⟩
    · rw [hstep]; exact while_exit o hexitg
    · have : (natToDec m).length = 1 := by rw [natToDec_lt10 h10]; rfl
      rw [this, hbclk]
      show s.clock - 1 = s.clock - 1
      rfl
    · exact single_digit_post h10 hbn hbp hbmem hbma hbbe hbba hbfr (hdm 0 hLpos)
  | succ k ih =>
    intro m p0 s hlen hm0 hm hn hp hb hdm hclk
    have hLpos := natToDec_length_pos m
    have hgW : eval s (.var "n") = some (BitVec.ofNat 64 m) := hn
    have hwne : (BitVec.ofNat 64 m : Word) ≠ 0 := ofNat64_ne_zero hm0 (by omega)
    obtain ⟨sb, hbody, hbn, hbp, hbclk, hbmem, hbma, hbbe, hbba, hbb, hbfr⟩ :=
      digitBodyAssign_nat o (m := m) (p0 := p0) (s := decClock s) hn hp hb (by omega)
        (hdm 0 hLpos)
    have hclk0 : s.clock ≠ 0 := by omega
    have hsbclk : sb.clock ≤ s.clock - 1 := by rw [hbclk]; exact Nat.le_refl _
    have hstep := while_iter_le o hgW hwne hclk0 hbody hsbclk
    by_cases h10 : m < 10
    · have hq0 : m / 10 = 0 := Nat.div_eq_of_lt h10
      have hexitg : eval sb (.var "n") = some (0 : Word) := by
        show sb.locals "n" = some (0 : Word)
        rw [hbn, hq0]; rfl
      refine ⟨sb, ?_, ?_, ?_⟩
      · rw [hstep]; exact while_exit o hexitg
      · have hone : (natToDec m).length = 1 := by rw [natToDec_lt10 h10]; rfl
        rw [hone, hbclk]
        show s.clock - 1 = s.clock - 1
        rfl
      · exact single_digit_post h10 hbn hbp hbmem hbma hbbe hbba hbfr (hdm 0 hLpos)
    · have hmq0 : m / 10 ≠ 0 := by omega
      have hLm : (natToDec m).length = (natToDec (m / 10)).length + 1 := by
        rw [natToDec_split (by omega : 10 ≤ m)]
        simp
      have hdm' : ∀ j, j < (natToDec (m / 10)).length →
          sb.memaddrs (byteAlign ((p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 (j + 1)))
            = true := by
        intro j hj
        rw [hbma, ← sub_ofNat_succ]
        exact hdm (j + 1) (by omega)
      obtain ⟨s', hrun, hclk', hpost⟩ :=
        ih (m / 10) (p0 - BitVec.ofNat 64 1) sb (by omega) hmq0 (by omega) hbn hbp hbb hdm'
          (by rw [hbclk]; show (natToDec (m / 10)).length ≤ s.clock - 1; omega)
      refine ⟨s', ?_, ?_, ?_⟩
      · rw [hstep]; exact hrun
      · rw [hclk', hbclk, hLm]
        show s.clock - 1 - (natToDec (m / 10)).length = s.clock - ((natToDec (m / 10)).length + 1)
        omega
      · exact multi_digit_post (by omega) (by omega) hbmem hbma hbbe hbba hbfr (hdm 0 hLpos)
          hpost

/-- The whole render, as the emitted block runs it: the working names declared once, the
first digit, then the loop for the rest. -/
def natToDecProg : PancakeProg :=
  digitPrefix (digitTailK (.while_ (.var "n") digitBodyAssign))

/-- Leaving the declarations puts the seven names back, so the whole render frames every
local except `n` and `p`. -/
theorem renderPost_restore {m : Nat} {p0 : Word} {s s2 : PancakeState σ}
    (h : RenderPostFrame scratch m p0 s s2) :
    RenderPost m p0 s { s2 with locals := restoreScratch s2.locals s.locals } := by
  obtain ⟨hn, hp, hbytes, hfr, hma, hbe, hba, hlfr⟩ := h
  refine ⟨?_, ?_, hbytes, hfr, hma, hbe, hba, ?_⟩
  · show restoreScratch s2.locals s.locals "n" = _
    rw [restoreScratch_ne _ _ (by decide)]
    exact hn
  · show restoreScratch s2.locals s.locals "p" = _
    rw [restoreScratch_ne _ _ (by decide)]
    exact hp
  · intro key h1 h2 _
    show restoreScratch s2.locals s.locals key = _
    by_cases hk : key ∈ scratch
    · rw [restoreScratch_mem _ _ hk]
    · rw [restoreScratch_ne _ _ hk]
      exact hlfr key h1 h2 hk

/-- **The render, executed.** Every digit is written below `p0`, and the clock it spends is
one tick per digit after the first — at most nineteen, whatever the number. -/
theorem natToDecProg_sem (o : Oracle σ) (m : Nat) (p0 : Word) (s : PancakeState σ)
    (hm64 : m < 2 ^ 64)
    (hn : s.locals "n" = some (BitVec.ofNat 64 m))
    (hp : s.locals "p" = some p0)
    (hdm : ∀ j, j < (natToDec m).length →
      s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 (j + 1))) = true)
    (hclk : renderFuel m ≤ s.clock) :
    ∃ s', PancakeSem o natToDecProg s = (none, s') ∧
      s'.clock = s.clock - renderFuel m ∧ RenderPost m p0 s s' := by
  have hLpos := natToDec_length_pos m
  obtain ⟨sb, hstep, hbn, hbp, hbclk, hbmem, hbma, hbbe, hbba, hbb, hbfr⟩ :=
    digitFirst_nat o (m := m) (p0 := p0) (s := s)
      (loop := .while_ (.var "n") digitBodyAssign) hn hp hm64 (hdm 0 hLpos)
  by_cases h10 : m < 10
  · have hq0 : m / 10 = 0 := Nat.div_eq_of_lt h10
    have hexitg : eval sb (.var "n") = some (0 : Word) := by
      show sb.locals "n" = some (0 : Word)
      rw [hbn, hq0]; rfl
    refine ⟨_, digitPrefix_sem o hn (hstep.trans (while_exit o hexitg)), ?_, ?_⟩
    · show sb.clock = _
      have hone : renderFuel m = 0 := by
        unfold renderFuel
        rw [natToDec_lt10 h10]
        rfl
      rw [hone, hbclk]
      omega
    · exact renderPost_restore
        (single_digit_post h10 hbn hbp hbmem hbma hbbe hbba hbfr (hdm 0 hLpos))
  · have hmq0 : m / 10 ≠ 0 := by omega
    have hLm : (natToDec m).length = (natToDec (m / 10)).length + 1 := by
      rw [natToDec_split (by omega : 10 ≤ m)]
      simp
    have hdm' : ∀ j, j < (natToDec (m / 10)).length →
        sb.memaddrs (byteAlign ((p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 (j + 1))) = true := by
      intro j hj
      rw [hbma, ← sub_ofNat_succ]
      exact hdm (j + 1) (by omega)
    obtain ⟨s2, hrun, hclk2, hpost⟩ :=
      digitLoop_sem o (natToDec (m / 10)).length (m / 10) (p0 - BitVec.ofNat 64 1) sb
        (by omega) hmq0 (by omega) hbn hbp hbb hdm'
        (by rw [hbclk]; unfold renderFuel at hclk; omega)
    refine ⟨_, digitPrefix_sem o hn (hstep.trans hrun), ?_, ?_⟩
    · show s2.clock = _
      rw [hclk2, hbclk]
      unfold renderFuel
      omega
    · exact renderPost_restore
        (multi_digit_post (by omega) hm64 hbmem hbma hbbe hbba hbfr (hdm 0 hLpos) hpost)

/-- A state with a writable window of `len` bytes below `p0`, and nothing else in range. -/
def window (ffi : σ) (p0 : Word) (len : Nat) (m : Nat) : PancakeState σ :=
  { locals := fun x => if x = "n" then some (BitVec.ofNat 64 m)
                       else if x = "p" then some p0 else none,
    memory := fun _ => 0,
    memaddrs := fun a => decide (∃ j, j < len ∧ a = byteAlign (p0 - BitVec.ofNat 64 (j + 1))),
    be := false, clock := 32, ffi := ffi, baseAddr := 0 }

/-- The render theorem applied to a concrete state: its premises are satisfiable, and the
run leaves the digits of 404 below the pointer. -/
theorem render_404 (o : Oracle Unit) :
    ∃ s', PancakeSem o natToDecProg (window () 4096 3 404) = (none, s') ∧
      RenderPost 404 4096 (window () 4096 3 404) s' :=
  have h := natToDecProg_sem o 404 4096 (window () 4096 3 404) (by decide) rfl rfl
    (by intro j hj
        have : j < 3 := by
          have : (natToDec 404).length = 3 := by decide
          omega
        show decide (∃ i, i < 3 ∧ _) = true
        simp only [decide_eq_true_eq]
        exact ⟨j, this, rfl⟩)
    (by decide)
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.2⟩

/-- Zero renders as one digit, which the loop reaches without spending a tick. -/
theorem render_zero (o : Oracle Unit) :
    ∃ s', PancakeSem o natToDecProg (window () 4096 1 0) = (none, s') ∧
      RenderPost 0 4096 (window () 4096 1 0) s' :=
  have h := natToDecProg_sem o 0 4096 (window () 4096 1 0) (by decide) rfl rfl
    (by intro j hj
        have : j < 1 := by
          have : (natToDec 0).length = 1 := by decide
          omega
        show decide (∃ i, i < 1 ∧ _) = true
        simp only [decide_eq_true_eq]
        exact ⟨j, this, rfl⟩)
    (by decide)
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.2⟩

-- The render matches the conventional `Nat.repr` byte for byte on the corpus, and the
-- quotient built by multiplication agrees with division at the range boundaries.
def regression_523 : Bool := decide (natToDec 200 = [50, 48, 48])
def regression_524 : Bool := decide (natToDec 404 = [52, 48, 52])
def regression_525 : Bool := decide (natToDec 48 = [52, 56])
def regression_526 : Bool :=
  decide ((natToDec 200).map (·.toNat) = (Nat.repr 200).toUTF8.toList.map (·.toNat))
def regression_527 : Bool :=
  decide ((natToDec 404).map (·.toNat) = (Nat.repr 404).toUTF8.toList.map (·.toNat))
def regression_538 : Bool :=
  decide ((natToDec 48).map (·.toNat) = (Nat.repr 48).toUTF8.toList.map (·.toNat))
def regression_539 : Bool := decide (div10w 0 = 0 && div10w 9 = 0 && div10w 10 = 1)
def regression_530 : Bool :=
  decide (div10w 2147483647 = 214748364 && div10w 4294967295 = 429496729)
def regression_531 : Bool :=
  decide (div10w 18446744073709551615 = 1844674407370955161
    && div10w 17179869189 = 1717986918)
def regression_532 : Bool := decide (renderFuel 2147483647 = 9 && renderFuel 0 = 0)
def regression_533 : Bool := decide ((natToDec 18446744073709551615).length = 20)

/-- Witness: the render's frame is satisfiable — the run of 404 above leaves it,
with the oracle fixed so that the statement is closed. -/
theorem RenderPostFrame_witness :
    ∃ s', RenderPostFrame [] 404 4096 (window () 4096 3 404) s' :=
  let h := render_404 ⟨fun st _ _ array => .ret st array⟩
  ⟨h.choose, h.choose_spec.2⟩

end DN.Compiler.NatToDec
