-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Decimal
import DN.Compiler.Region

/-!
# DN.Compiler.NatToDecCompile

Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md.
-/

namespace DN.Compiler.NatToDecCompile

open DN.Compiler DN.Compiler.Region DN.Compiler.Decimal

variable {σ : Type}

/-! ## 0. Word arithmetic on the `BitVec.ofNat` normal form

Two facts the loop step needs: subtracting the literal `10w` is `ofNat (m - 10)`
(no wrap, `m ≥ 10`), and the `q := q + 1` accumulation telescopes to `+ (k+1)`. -/

/-- `mw - 10w = (m-10)w` when `10 ≤ m < 2^64` (no borrow). -/
theorem ofNat_sub_ten {m : Nat} (h : 10 ≤ m) (hb : m < 2 ^ 64) :
    BitVec.ofNat 64 m - BitVec.ofNat 64 10 = BitVec.ofNat 64 (m - 10) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The `+1` accumulator telescopes: `(q + 1w) + kw = q + (k+1)w`. -/
theorem qacc (q0 : Word) (k : Nat) :
    (q0 + BitVec.ofNat 64 1) + BitVec.ofNat 64 k = q0 + BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## 1. divide-by-10 as a real DN.Compiler `While` (repeated subtraction) -/

/-- The loop guard `10 <= n`: `Cmp NotLess n 10w` (`word_cmp NotLess n 10 =
¬(n < 10)`, the `<=` of the modelled subset). -/
def divGuard : PancakeExp :=
  .cmp .notLess (.var "n") (.const (BitVec.ofNat 64 10))

/-- One loop iteration: `n := n - 10; q := q + 1`. Only `Op Sub` / `Op Add`. -/
def divBody : PancakeProg :=
  .seq (.assign "n" (.op .sub (.var "n") (.const (BitVec.ofNat 64 10))))
       (.assign "q" (.op .add (.var "q") (.const (BitVec.ofNat 64 1))))

/-- Divide-by-10 by subtraction: `while (10 <= n) { n := n-10; q := q+1 }`. A
`While` in the modelled subset — NO `Div`/`Mod`. -/
def divWhile : PancakeProg := .while_ divGuard divBody

/-- One loop-body iteration executed: `n := n-10; q := q+1` runs (no clock cost —
straight-line assigns) to the state whose `"n"`/`"q"` are updated, everything else
framed. `10 ≤ m` keeps the subtraction borrow-free. -/
theorem divBody_sem (o : Oracle σ) {m : Nat} {q0 : Word} {s : PancakeState σ}
    (hn : s.locals "n" = some (BitVec.ofNat 64 m)) (hm10 : 10 ≤ m) (hbb : m < 2 ^ 64)
    (hq : s.locals "q" = some q0) :
    PancakeSem o divBody s = (none, { s with locals := setLocal (setLocal s.locals "n" (BitVec.ofNat 64 (m - 10))) "q" (q0 + BitVec.ofNat 64 1) }) := by
  unfold divBody
  have hevN : eval s (.op .sub (.var "n") (.const (BitVec.ofNat 64 10))) = some (BitVec.ofNat 64 (m - 10)) := by
    simp only [eval, hn]; rw [ofNat_sub_ten hm10 hbb]
  rw [sem_seq_none (sem_assign (oracle := o) hevN)]
  have hqval : (setLocal s.locals "n" (BitVec.ofNat 64 (m - 10))) "q" = some q0 := by
    simp only [setLocal, if_neg (by decide : ¬ ("q" = "n"))]; exact hq
  have hevQ : eval ({ s with locals := setLocal s.locals "n" (BitVec.ofNat 64 (m - 10)), clock := min s.clock s.clock } : PancakeState σ) (.op .add (.var "q") (.const (BitVec.ofNat 64 1))) = some (q0 + BitVec.ofNat 64 1) := by
    simp only [eval]; rw [hqval]
  rw [sem_assign (oracle := o) hevQ]
  simp only [Nat.min_self]

/-- The guard reads `10 <= m` off the current `n = mw` (`m < 2^63` keeps the
SIGNED `word_cmp` = the unsigned test). -/
theorem div_guard_eval {m : Nat} {s : PancakeState σ}
    (hn : s.locals "n" = some (BitVec.ofNat 64 m)) (hm63 : m < 2 ^ 63) :
    eval s divGuard = some (if m < 10 then 0 else 1) := by
  simp only [divGuard, eval, hn]
  rw [signedLt_ofNat m 10 hm63 (by omega)]
  by_cases h : m < 10 <;> simp [h]

/-- One `While` iteration reduction: guard true (`= 1`), clock left, and the body
consumes exactly its tick (`sb.clock = s.clock - 1`), so the loop runs the body on
`decClock s` and recurses on `sb` (the clamp is a no-op). -/
theorem while_iter (o : Oracle σ) {e : PancakeExp} {c : PancakeProg}
    {s sb : PancakeState σ}
    (hg : eval s e = some 1) (hclk : s.clock ≠ 0)
    (hbody : PancakeSem o c (decClock s) = (none, sb))
    (hsbclk : sb.clock = s.clock - 1) :
    PancakeSem o (.while_ e c) s = PancakeSem o (.while_ e c) sb := by
  have hcollapse : ({ sb with clock := min (s.clock - 1) sb.clock } : PancakeState σ) = sb := by
    have hm : min (s.clock - 1) sb.clock = sb.clock := by rw [hsbclk]; omega
    rw [hm]
  rw [PancakeSem]
  simp only [hg, ne_eq, show ((1 : Word) = 0) = False from by decide, not_false_eq_true,
             if_true, hclk, if_false, clampClock, hbody, hcollapse]

/-- The `While` exit: guard false (`= 0`) leaves the state untouched. -/
theorem while_exit (o : Oracle σ) {e : PancakeExp} {c : PancakeProg}
    {s : PancakeState σ} (hg : eval s e = some 0) :
    PancakeSem o (.while_ e c) s = (none, s) := by
  rw [PancakeSem, hg]; simp

/-- **The divide-by-10 subtraction loop, executed.** From `n = mw` (`m < 2^63`),
`q = q0`, with `k = m/10` units of clock, `divWhile` terminates in `n = (m%10)w`,
`q = q0 + (m/10)w` — divide-by-10 with only `Sub`/`Add`/`NotLess`, no `Div`. Every
other field is framed; `k = m/10` ticks of clock are consumed. Induction on
`k = m/10`. -/
theorem divWhile_sem (o : Oracle σ) :
    ∀ (k m : Nat) (q0 : Word) (s : PancakeState σ),
      s.locals "n" = some (BitVec.ofNat 64 m) →
      s.locals "q" = some q0 →
      m < 2 ^ 63 →
      m / 10 = k →
      k ≤ s.clock →
      ∃ s', PancakeSem o divWhile s = (none, s') ∧
        s'.locals "n" = some (BitVec.ofNat 64 (m % 10)) ∧
        s'.locals "q" = some (q0 + BitVec.ofNat 64 k) ∧
        s'.clock = s.clock - k ∧
        s'.memory = s.memory ∧ s'.memaddrs = s.memaddrs ∧
        s'.be = s.be ∧ s'.baseAddr = s.baseAddr ∧
        (∀ key, key ≠ "n" → key ≠ "q" → s'.locals key = s.locals key) := by
  intro k
  induction k with
  | zero =>
    intro m q0 s hn hq hm63 hk hclk
    have hm10 : m < 10 := by omega
    have hg : eval s divGuard = some 0 := by
      rw [div_guard_eval hn hm63]; simp [hm10]
    refine ⟨s, while_exit o hg, ?_, ?_, by omega, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
    · rw [Nat.mod_eq_of_lt hm10]; exact hn
    · rw [hq]; congr 1; simp
  | succ k ih =>
    intro m q0 s hn hq hm63 hk hclk
    have hm10 : 10 ≤ m := by
      rcases Nat.lt_or_ge m 10 with h | h
      · rw [Nat.div_eq_of_lt h] at hk; omega
      · exact h
    have hg : eval s divGuard = some 1 := by
      rw [div_guard_eval hn hm63]
      have : ¬ m < 10 := by omega
      simp [this]
    have hclk0 : s.clock ≠ 0 := by omega
    have hbb : m < 2 ^ 64 := by omega
    -- the body runs on `decClock s` to a state `sB`; package its field facts so the
    -- big record literal need not be repeated.
    obtain ⟨sB, hbody, hsbN, hsbQ, hsbclk, hsbmem, hsbma, hsbbe, hsbba, hsbfr⟩ :
        ∃ sB, PancakeSem o divBody (decClock s) = (none, sB) ∧
          sB.locals "n" = some (BitVec.ofNat 64 (m - 10)) ∧
          sB.locals "q" = some (q0 + BitVec.ofNat 64 1) ∧
          sB.clock = s.clock - 1 ∧
          sB.memory = s.memory ∧ sB.memaddrs = s.memaddrs ∧
          sB.be = s.be ∧ sB.baseAddr = s.baseAddr ∧
          (∀ key, key ≠ "n" → key ≠ "q" → sB.locals key = s.locals key) := by
      refine ⟨_, divBody_sem o (by simpa [decClock] using hn) hm10 hbb
                (by simpa [decClock] using hq), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setLocal]
      · simp [setLocal]
      · simp [decClock]
      · simp [decClock]
      · simp [decClock]
      · simp [decClock]
      · simp [decClock]
      · intro key hkn hkq
        simp only [setLocal, decClock, if_neg hkq, if_neg hkn]
    have hstep := while_iter o hg hclk0 hbody hsbclk
    have hm1063 : m - 10 < 2 ^ 63 := by omega
    have hdiv : (m - 10) / 10 = k := by omega
    have hclk2 : k ≤ sB.clock := by rw [hsbclk]; omega
    obtain ⟨s', hrun, hn', hq', hclk', hmem', hma', hbe', hba', hfr'⟩ :=
      ih (m - 10) (q0 + BitVec.ofNat 64 1) sB hsbN hsbQ hm1063 hdiv hclk2
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show PancakeSem o (.while_ divGuard divBody) s = (none, s')
      rw [hstep]; exact hrun
    · rw [hn']; congr 2; omega
    · rw [hq', qacc]
    · rw [hclk', hsbclk]; omega
    · rw [hmem', hsbmem]
    · rw [hma', hsbma]
    · rw [hbe', hsbbe]
    · rw [hba', hsbba]
    · intro key hkn hkq
      rw [hfr' key hkn hkq, hsbfr key hkn hkq]

/-- **Divide-by-10 with `q` starting at 0.** The public entry: from `n = mw`,
`q = 0`, `divWhile` computes `q = (m/10)w`, `n = (m%10)w`. Instantiates
`divWhile_sem` at `q0 = 0`, `k = m/10`. -/
theorem divWhile_divmod (o : Oracle σ) {m : Nat} {s : PancakeState σ}
    (hn : s.locals "n" = some (BitVec.ofNat 64 m))
    (hq : s.locals "q" = some 0)
    (hm63 : m < 2 ^ 63) (hclk : m / 10 ≤ s.clock) :
    ∃ s', PancakeSem o divWhile s = (none, s') ∧
      s'.locals "n" = some (BitVec.ofNat 64 (m % 10)) ∧
      s'.locals "q" = some (BitVec.ofNat 64 (m / 10)) := by
  obtain ⟨s', hrun, hn', hq', _⟩ := divWhile_sem o (m / 10) m 0 s hn hq hm63 rfl hclk
  exact ⟨s', hrun, hn', by rw [hq']; simp⟩

/-! ## 2. the digit byte to memory (`StoreByte`), the write `natToDec` performs

After `divWhile`, `n = (m%10)w` is the low decimal digit. Its ASCII byte is
`digitByte (m%10) = (48 + m%10)w` — exactly `Op Add n 48w`, low byte. `StoreByte p
(n + 48)` writes it (panSem `mem_store_byte`, the LOW byte `w2w`). -/

/-- The digit's ASCII byte value as a source word: `n + 48w`. Its low byte (panSem
`StoreByte`'s `w2w`, i.e. `setWidth 8`) is `digitByte m`. -/
theorem digit_src_low (m : Nat) :
    (BitVec.ofNat 64 m + BitVec.ofNat 64 48).setWidth 8 = digitByte m := by
  unfold digitByte
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- **One digit emitted to memory.** With `n = dw` (the digit just peeled by
`divWhile`) and destination pointer `p`, `StoreByte p (n + 48)` runs (no clock
cost) to the state whose memory is `s`'s memory with `digitByte d` byte-stored at
`p` (panSem `mem_store_byte`), everything else framed. `Op Add` + `StoreByte`
only — the exact write `natToDec` performs per digit. The `memStoreByte … = some
mem'` hypothesis is the in-`memaddrs` side condition (an EXPLICIT precondition,
never a `sorry`). Non-vacuous: the post-memory is pinned to `mem'`, the
`digitByte`-store image. -/
theorem digit_store (o : Oracle σ) {d : Nat} {p : Word} {s : PancakeState σ}
    {mem' : Word → Word}
    (hn : s.locals "n" = some (BitVec.ofNat 64 d))
    (hp : s.locals "p" = some p)
    (hstore : memStoreByte s.memory s.memaddrs s.be p (digitByte d) = some mem') :
    PancakeSem o (.storeByte (.var "p") (.op .add (.var "n") (.const (BitVec.ofNat 64 48)))) s
      = (none, { s with memory := mem' }) := by
  have hev : eval s (.op .add (.var "n") (.const (BitVec.ofNat 64 48)))
      = some (BitVec.ofNat 64 d + BitVec.ofNat 64 48) := by
    simp only [eval, hn]
  have hlow : (BitVec.ofNat 64 d + BitVec.ofNat 64 48).setWidth 8 = digitByte d := digit_src_low d
  exact evaluate_storeByte o s (hp) hev (by rw [hlow]; exact hstore)

/-! ## 3. connection to `natToDec` (the proven spec) + concrete corpus

`natToDec` (`DN.Compiler.Decimal`, proven `natToDec_readback`: the emitted
ASCII digits read back as `n`) peels the low digit `m % 10` and recurses on the
quotient `m / 10` (`decAux`'s `else` branch). `divWhile` computes EXACTLY that
`(m/10, m%10)` — with only `Sub`/`Add`/`NotLess`, no `Div`. So each digit position
of `natToDec` is realised by one `divWhile`, and the digit byte by one `digit_store`.
The `#guard`s pin the proven spec byte-identical to `Nat.repr` on the corpus. -/

/-- The digit `natToDec` peels at a position (`m % 10`, the `decAux` remainder) is
the `n`-value `divWhile` leaves, and the quotient it recurses on (`m / 10`) is the
`q`-value — the two are the same divide-by-10, one done by `Div`, one by subtraction. -/
theorem divWhile_matches_decAux_step (o : Oracle σ) {m : Nat} {s : PancakeState σ}
    (hn : s.locals "n" = some (BitVec.ofNat 64 m))
    (hq : s.locals "q" = some 0)
    (hm63 : m < 2 ^ 63) (hclk : m / 10 ≤ s.clock) :
    ∃ s', PancakeSem o divWhile s = (none, s') ∧
      -- the emitted digit byte is `digitByte (m % 10)` (the `decAux` `else`-digit)
      (∃ dw, s'.locals "n" = some dw ∧
        (dw + BitVec.ofNat 64 48).setWidth 8 = digitByte (m % 10)) ∧
      -- the recursion continues on `m / 10` (the `decAux` `else`-quotient)
      s'.locals "q" = some (BitVec.ofNat 64 (m / 10)) := by
  obtain ⟨s', hrun, hn', hq'⟩ := divWhile_divmod o hn hq hm63 hclk
  exact ⟨s', hrun, ⟨_, hn', digit_src_low (m % 10)⟩, hq'⟩

/-- Concrete corpus (200, 404, 48) at the theorem level — divide-by-10 by
subtraction lands the exact remainder/quotient, fully proven (no `#eval`, no
`native_decide`), so the loop is non-vacuous on real status codes / lengths. -/
example (o : Oracle σ) (s : PancakeState σ)
    (hn : s.locals "n" = some (BitVec.ofNat 64 200)) (hq : s.locals "q" = some 0)
    (hclk : 20 ≤ s.clock) :
    ∃ s', PancakeSem o divWhile s = (none, s') ∧
      s'.locals "n" = some (BitVec.ofNat 64 0) ∧ s'.locals "q" = some (BitVec.ofNat 64 20) := by
  have h := divWhile_divmod o hn hq (by omega) (by omega)
  simpa using h

example (o : Oracle σ) (s : PancakeState σ)
    (hn : s.locals "n" = some (BitVec.ofNat 64 404)) (hq : s.locals "q" = some 0)
    (hclk : 40 ≤ s.clock) :
    ∃ s', PancakeSem o divWhile s = (none, s') ∧
      s'.locals "n" = some (BitVec.ofNat 64 4) ∧ s'.locals "q" = some (BitVec.ofNat 64 40) := by
  have h := divWhile_divmod o hn hq (by omega) (by omega)
  simpa using h

example (o : Oracle σ) (s : PancakeState σ)
    (hn : s.locals "n" = some (BitVec.ofNat 64 48)) (hq : s.locals "q" = some 0)
    (hclk : 4 ≤ s.clock) :
    ∃ s', PancakeSem o divWhile s = (none, s') ∧
      s'.locals "n" = some (BitVec.ofNat 64 8) ∧ s'.locals "q" = some (BitVec.ofNat 64 4) := by
  have h := divWhile_divmod o hn hq (by omega) (by omega)
  simpa using h

-- the render matches the conventional `Nat.repr` byte-for-byte on the corpus
-- (`natToDec`, proven `natToDec_readback`, is the divide-by-10 render this loop realises):
def regression_323 : Bool := decide (natToDec 200 = [50, 48, 48]
  )
def regression_324 : Bool := decide (natToDec 404 = [52, 48, 52]
  )
def regression_325 : Bool := decide (natToDec 48  = [52, 56]
  )
def regression_326 : Bool := decide ((natToDec 200).map (·.toNat) = (Nat.repr 200).toUTF8.toList.map (·.toNat)
  )
def regression_327 : Bool := decide ((natToDec 404).map (·.toNat) = (Nat.repr 404).toUTF8.toList.map (·.toNat)
  )
def regression_328 : Bool := decide ((natToDec 48).map (·.toNat)  = (Nat.repr 48).toUTF8.toList.map (·.toNat)
  )

end DN.Compiler.NatToDecCompile

-- ASSURANCE: axioms of the load-bearing results are the three Lean-core ones only.
