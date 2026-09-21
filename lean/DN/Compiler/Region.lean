-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.Region

Adapted from the compiler extraction recorded in docs/provenance.json.
These definitions and theorems concern the Lean model. Correspondence to the
HOL4 backend, pretty-printer/parser, ABI and executable is tracked separately
in docs/assurance.md. The model is a restricted 64-bit Pancake fragment.
-/
import DN.Compiler.Semantics
import DN.Compiler.Lower

namespace DN.Compiler.Region

open DN.Compiler DN.Compiler.Lower

/-! ## 0. The Lean SPEC (byte-identical to C1's HOL re-declaration) -/

/-- `step acc b = (acc * 31 + b) MOD 16777216` (C1 `step_def`). digestMul = 31,
digestMask = 2^24-1, so `& mask = MOD 2^24`. -/
def step (acc b : Nat) : Nat := (acc * 31 + b) % 16777216

/-- `scanFrom a off len acc` (C1 `scanFrom_def`): fold `step` over `a[off]`,
`a[off+1]`, …, `len` bytes. -/
def scanFrom (a : List (BitVec 8)) (off : Nat) : Nat → Nat → Nat
  | 0,     acc => acc
  | n + 1, acc => scanFrom a (off + 1) n (step acc (a[off]!.toNat))

/-- `boundScan a off len` (C1 `boundScan_def`): the view digest iff in-bounds. -/
def boundScan (a : List (BitVec 8)) (off len : Nat) : Option Nat :=
  if off + len ≤ a.length then some (scanFrom a off len 0) else none

/-- `c0_encode` (C1 `c0_encode_def`): out-of-bounds sentinel `NONE ↦ 0xFFFFFFFF`. -/
def c0Encode : Option Nat → Nat
  | none => 4294967295
  | some k => k

/-! ## 1. Word-convention lemmas (the P2 §4.2 seam, C1's trap) -/

/-- `(ofNat x).toInt = x` on the non-negative signed range (`x < 2^63`). -/
theorem toInt_ofNat_small (x : Nat) (hx : x < 2 ^ 63) :
    (BitVec.ofNat 64 x).toInt = (x : Int) := by
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)]
  simp only [Int.bmod]
  split <;> omega

/-- The convention lemma = C1's `signed_lt_n2w64`: on the non-negative signed
range the SIGNED word order agrees with `Nat` order. This is where an
off-by-a-sign-bit bug would live (C1 §2). -/
theorem signedLt_ofNat (x y : Nat) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    signedLt (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  unfold signedLt BitVec.slt
  rw [toInt_ofNat_small x hx, toInt_ofNat_small y hy]
  simp [Int.ofNat_lt]

/-- `ofNat a + ofNat b = ofNat (a+b)` when the sum is in range (`word_add_n2w`). -/
theorem ofNat_add_small (a b : Nat) (h : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
      Nat.mod_eq_of_lt h]

/-! ## 2. The bounds `If` fragment (C1 analogue) -/

/-- The `.pnk` bounds `If`, isolated as a `PancakeProg` — the exact analogue of
C1's `boundsChk_def` (`Cmp Less` SIGNED; else-arm `Skip` = the scan-loop stub). -/
def boundsChk : PancakeProg :=
  .cond (.cmp .less (.var "alen") (.op .add (.var "off") (.var "len")))
        (.assign "result" (.const (BitVec.ofNat 64 4294967295)))
        .skip

/-- The state relation = C1's `stRel_def`: locals encode `(a,off,len)` as words,
`result` is a declared word slot, and the sizes fit the non-negative signed
range (the side condition the SIGNED test forces). -/
def stRel {σ : Type} (a : List (BitVec 8)) (off len : Nat) (r0 : Word)
    (s : PancakeState σ) : Prop :=
  s.locals "alen"   = some (BitVec.ofNat 64 a.length) ∧
  s.locals "off"    = some (BitVec.ofNat 64 off) ∧
  s.locals "len"    = some (BitVec.ofNat 64 len) ∧
  s.locals "result" = some r0 ∧
  a.length < 2 ^ 63 ∧ off + len < 2 ^ 63

variable {σ : Type}

/-- LINK A, the refinement core = C1's `eval_bounds_expr`: real model `eval` of
the bounds expression = `1w` EXACTLY when the Lean SPEC says out-of-bounds
(`boundScan = none`). -/
theorem eval_bounds_expr {a off len r0} {s : PancakeState σ}
    (h : stRel a off len r0 s) :
    eval s (.cmp .less (.var "alen") (.op .add (.var "off") (.var "len")))
      = some (if boundScan a off len = none then 1 else 0) := by
  obtain ⟨halen, hoff, hlen, _, ha63, hol63⟩ := h
  show (match eval s (.var "alen"), eval s (.op .add (.var "off") (.var "len")) with
        | some x, some y => some (if signedLt x y then (1 : Word) else 0)
        | _, _ => none) = _
  simp only [eval, halen, hoff, hlen]
  rw [ofNat_add_small off len (by omega)]
  rw [signedLt_ofNat a.length (off + len) ha63 hol63]
  have : boundScan a off len = none ↔ a.length < off + len := by
    unfold boundScan; split <;> simp_all <;> omega
  by_cases hb : a.length < off + len <;> simp [this, hb]

/-- LINK A end-to-end for the bounds fragment = C1's `evaluate_boundsChk`:
running the model `PancakeSem` on the bounds `If` writes `c0Encode none` into
`result` exactly on the out-of-bounds inputs, and leaves the state untouched
otherwise. RHS `ofNat (c0Encode (boundScan …))` is the SPEC's own encoded word. -/
theorem evaluate_boundsChk (oracle : Oracle σ) {a off len r0} {s : PancakeState σ}
    (h : stRel a off len r0 s) :
    PancakeSem oracle boundsChk s =
      (none,
       if boundScan a off len = none
       then { s with locals := setLocal s.locals "result" (BitVec.ofNat 64 (c0Encode (boundScan a off len))) }
       else s) := by
  have he := eval_bounds_expr (σ := σ) (r0 := r0) (s := s) h
  have hres : s.locals "result" = some r0 := h.2.2.2.1
  rw [boundsChk]
  by_cases hb : boundScan a off len = none
  · rw [PancakeSem, he]
    simp only [hb, if_true, ne_eq, show ((1 : Word) = 0) = False from by decide,
               not_false_eq_true, if_true, PancakeSem, eval, c0Encode, hres]
  · rw [PancakeSem, he]
    simp only [hb, if_false, ne_eq, not_true, if_false, PancakeSem]

/-- C1's `boundsChk_encodes_spec` restated in the report's vocabulary. -/
theorem boundsChk_encodes_spec (oracle : Oracle σ) {a off len r0} {s : PancakeState σ}
    (h : stRel a off len r0 s) :
    ∃ s', PancakeSem oracle boundsChk s = (none, s') ∧
      (boundScan a off len = none →
        s'.locals "result" = some (BitVec.ofNat 64 (c0Encode (boundScan a off len)))) ∧
      (boundScan a off len ≠ none → s' = s) := by
  refine ⟨_, evaluate_boundsChk oracle h, ?_, ?_⟩
  · intro hb; simp [hb, setLocal]
  · intro hb; simp [hb]

/-! ## 3. The scan `While` (C1 §4-A-2/3, the deferred loop) -/

/-- More word-convention lemmas for the loop body arithmetic. -/
theorem ofNat_mul_small (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a * b < 2 ^ 64) :
    BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h]

theorem setWidth8_64 (b : BitVec 8) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-- The `& 16777215` mask is exactly `MOD 16777216` — the digest reduction. -/
theorem ofNat_and_mask (m : Nat) (h : m < 2 ^ 64) :
    BitVec.ofNat 64 m &&& BitVec.ofNat 64 16777215 = BitVec.ofNat 64 (m % 16777216) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h, show (16777215 % 2 ^ 64 : Nat) = 2 ^ 24 - 1 from by omega,
      Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `scanFrom` as a LEFT fold: one more byte = `step` on the tail. Proven by
induction on the count; lets the loop invariant advance one iteration. -/
theorem scanFrom_succ (a : List (BitVec 8)) (off n acc : Nat) :
    scanFrom a off (n + 1) acc = step (scanFrom a off n acc) ((a[off + n]!).toNat) := by
  induction n generalizing off acc with
  | zero => simp [scanFrom]
  | succ n ih =>
    have e1 : scanFrom a off (n + 1 + 1) acc
        = scanFrom a (off + 1) (n + 1) (step acc ((a[off]!).toNat)) := by rw [scanFrom]
    have e2 : scanFrom a off (n + 1) acc
        = scanFrom a (off + 1) n (step acc ((a[off]!).toNat)) := by rw [scanFrom]
    rw [e1, ih (off + 1) (step acc ((a[off]!).toNat)), ← e2, show off + 1 + n = off + (n + 1) from by omega]

/-- The digest is always in the `2^24` range (each `step` reduces mod `2^24`). -/
theorem scanFrom_lt (a : List (BitVec 8)) (off n : Nat) : scanFrom a off n 0 < 16777216 := by
  cases n with
  | zero => simp [scanFrom]
  | succ n => rw [scanFrom_succ]; unfold step; omega

/-- The byte-memory relation the loop reads over — `ViewBytes s a buf off len`
says the `len` bytes of the view sit in the model memory at `buf + off + i` and
equal `a[off+i]`. This is the load_vec FFI postcondition = A0, threaded as an
EXPLICIT hypothesis (never a `sorry`). -/
def ViewBytes (s : PancakeState σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat) : Prop :=
  ∀ i, i < len →
    memLoadByte s.memory s.memaddrs s.be (buf + BitVec.ofNat 64 off + BitVec.ofNat 64 i)
      = some (a[off + i]!)

/-- The scan loop body (Seq of the digest update + the index bump). -/
def scanBody : PancakeProg :=
  .seq
    (.assign "acc"
      (.op .and_
        (.op .add (.mul (.var "acc") (.const (BitVec.ofNat 64 31)))
                  (.loadByte (.op .add (.op .add (.var "buf") (.var "off")) (.var "i"))))
        (.const (BitVec.ofNat 64 16777215))))
    (.assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1))))

/-- The scan `While` of the region program: the rolling digest over the view. -/
def scanWhile : PancakeProg :=
  .while_ (.cmp .less (.var "i") (.var "len")) scanBody

/-- The emitted region program lowers: every construct it uses is modelled. -/
theorem regionProg_lowers : Lower.regionProg.isSome := by decide

/-! ### PancakeSem control-flow reduction lemmas -/

/-- `Assign`: run the assignment given the RHS value and the variable's binding. -/
theorem sem_assign {oracle : Oracle σ} {x e v old} {s : PancakeState σ} (h : eval s e = some v)
    (hbound : s.locals x = some old) :
    PancakeSem oracle (.assign x e) s = (none, { s with locals := setLocal s.locals x v }) := by
  rw [PancakeSem, h, hbound]

/-- `Seq` with a normally-terminating head: run the tail on the clamped state. -/
theorem sem_seq_none {oracle : Oracle σ} {c1 c2} {s s1 : PancakeState σ}
    (h : PancakeSem oracle c1 s = (none, s1)) :
    PancakeSem oracle (.seq c1 c2) s
      = PancakeSem oracle c2 { s1 with clock := min s.clock s1.clock } := by
  rw [PancakeSem, h]; simp only [clampClock]


/-- ONE loop-body iteration: evaluate the digest-update expression to the SPEC's
next digest word. This isolates all the word-convention algebra (`*`,`+`,`&`,
byte-load) so the induction below stays about control flow. -/
theorem eval_body_acc {a : List (BitVec 8)} {buf : Word} {off len k : Nat}
    {s : PancakeState σ}
    (hk : k < len)
    (hacc : s.locals "acc" = some (BitVec.ofNat 64 (scanFrom a off k 0)))
    (hi : s.locals "i" = some (BitVec.ofNat 64 k))
    (hbuf : s.locals "buf" = some buf)
    (hoff : s.locals "off" = some (BitVec.ofNat 64 off))
    (hview : ViewBytes s a buf off len) :
    eval s
        (.op .and_
          (.op .add (.mul (.var "acc") (.const (BitVec.ofNat 64 31)))
                    (.loadByte (.op .add (.op .add (.var "buf") (.var "off")) (.var "i"))))
          (.const (BitVec.ofNat 64 16777215)))
      = some (BitVec.ofNat 64 (scanFrom a off (k + 1) 0)) := by
  have haccLt : scanFrom a off k 0 < 16777216 := scanFrom_lt a off k
  have hbyte : (a[off + k]!).toNat < 256 := by
    have := (a[off + k]!).isLt; omega
  -- the byte load
  have hload := hview k hk
  -- reduce eval structurally
  show (match
          (match eval s (.mul (.var "acc") (.const (BitVec.ofNat 64 31))),
                 eval s (.loadByte (.op .add (.op .add (.var "buf") (.var "off")) (.var "i"))) with
           | some x, some y => some (x + y)
           | _, _ => none),
          eval s (.const (BitVec.ofNat 64 16777215)) with
        | some x, some y => some (x &&& y)
        | _, _ => none) = _
  have hmul : eval s (.mul (.var "acc") (.const (BitVec.ofNat 64 31)))
      = some (BitVec.ofNat 64 (scanFrom a off k 0 * 31)) := by
    show (match eval s (.var "acc"), eval s (.const (BitVec.ofNat 64 31)) with
          | some x, some y => some (x * y) | _, _ => none) = _
    simp only [eval, hacc]
    rw [ofNat_mul_small _ _ (by omega) (by omega) (by omega)]
  have haddr : eval s (.op .add (.op .add (.var "buf") (.var "off")) (.var "i"))
      = some (buf + BitVec.ofNat 64 off + BitVec.ofNat 64 k) := by
    simp only [eval, hbuf, hoff, hi]
  have hldb : eval s (.loadByte (.op .add (.op .add (.var "buf") (.var "off")) (.var "i")))
      = some (BitVec.ofNat 64 ((a[off + k]!).toNat)) := by
    show (match eval s (.op .add (.op .add (.var "buf") (.var "off")) (.var "i")) with
          | some w => (match memLoadByte s.memory s.memaddrs s.be w with
                       | some b => some (b.setWidth 64) | none => none)
          | none => none) = _
    rw [haddr]; simp only [hload, setWidth8_64]
  rw [hmul, hldb]
  simp only [eval]
  rw [ofNat_add_small _ _ (by omega), ofNat_and_mask _ (by omega), scanFrom_succ]
  rfl

variable (oracle : Oracle σ)

/-- The scan-`While` FUEL INDUCTION (C1 §4-A-2/3, paid down in Lean). Running the
model `PancakeSem` on `scanWhile` from index `k` with `rem = len - k` iterations
of fuel computes the SPEC digest `scanFrom a off len 0` into `acc`, sets `i =
len`, and preserves memory and the other locals. The loop invariant is the
accumulator relation (`acc = scanFrom a off k 0`) + index monotonicity + the
`ViewBytes` byte-memory relation. -/
theorem scan_loop (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) :
    ∀ (rem k : Nat) (s : PancakeState σ),
      k + rem = len →
      rem ≤ s.clock →
      s.locals "acc" = some (BitVec.ofNat 64 (scanFrom a off k 0)) →
      s.locals "i"   = some (BitVec.ofNat 64 k) →
      s.locals "len" = some (BitVec.ofNat 64 len) →
      s.locals "buf" = some buf →
      s.locals "off" = some (BitVec.ofNat 64 off) →
      ViewBytes s a buf off len →
      ∃ s', PancakeSem oracle scanWhile s = (none, s') ∧
        s'.locals "acc" = some (BitVec.ofNat 64 (scanFrom a off len 0)) ∧
        s'.locals "i" = some (BitVec.ofNat 64 len) ∧
        s'.locals "len" = s.locals "len" ∧
        s'.locals "buf" = s.locals "buf" ∧
        s'.locals "off" = s.locals "off" ∧
        s'.memory = s.memory ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧
        s'.baseAddr = s.baseAddr ∧ s'.ffi = s.ffi ∧
        (∀ x, x ≠ "acc" → x ≠ "i" → s'.locals x = s.locals x) := by
  intro rem
  induction rem with
  | zero =>
    intro k s hk _ hacc hi hlen hbuf hoff _
    have hkl : k = len := by omega
    subst hkl
    refine ⟨s, ?_, hacc, hi, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
    rw [scanWhile, PancakeSem]
    have hcnd : eval s (.cmp .less (.var "i") (.var "len"))
        = some (if signedLt (BitVec.ofNat 64 k) (BitVec.ofNat 64 k) then 1 else 0) := by
      simp only [eval, hi, hlen]
    rw [hcnd, signedLt_ofNat _ _ (by omega) (by omega)]
    simp
  | succ m ih =>
    intro k s hk hclock hacc hi hlen hbuf hoff hview
    have hkl : k < len := by omega
    have hkl63 : k < 2 ^ 63 := by omega
    have hclock0 : s.clock ≠ 0 := by omega
    have hdl : (decClock s).locals = s.locals := rfl
    -- (1) the digest-update expression evaluates to the next digest word
    have haccE :
        eval (decClock s)
          (.op .and_
            (.op .add (.mul (.var "acc") (.const (BitVec.ofNat 64 31)))
                      (.loadByte (.op .add (.op .add (.var "buf") (.var "off")) (.var "i"))))
            (.const (BitVec.ofNat 64 16777215)))
          = some (BitVec.ofNat 64 (scanFrom a off (k + 1) 0)) :=
      eval_body_acc hkl (by rw [hdl]; exact hacc) (by rw [hdl]; exact hi)
        (by rw [hdl]; exact hbuf) (by rw [hdl]; exact hoff)
        (by intro i hi'; have := hview i hi'; simpa [decClock] using this)
    -- (2) the acc-assignment
    obtain ⟨sA, hsA⟩ : ∃ sA : PancakeState σ,
        sA = { decClock s with
               locals := setLocal (decClock s).locals "acc"
                          (BitVec.ofNat 64 (scanFrom a off (k + 1) 0)) } := ⟨_, rfl⟩
    have hA := sem_assign (oracle := oracle) (x := "acc") haccE (by rw [hdl]; exact hacc)
    rw [← hsA] at hA
    -- (3) the index-bump on sA
    have hsAi : sA.locals "i" = some (BitVec.ofNat 64 k) := by
      rw [hsA]; simp only [setLocal, decClock]; rw [if_neg (by decide)]; exact hi
    have hiE : eval sA (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))
        = some (BitVec.ofNat 64 (k + 1)) := by
      show (match eval sA (.var "i"), eval sA (.const (BitVec.ofNat 64 1)) with
            | some x, some y => some (x + y) | _, _ => none) = _
      simp only [eval, hsAi]
      rw [ofNat_add_small _ _ (by omega)]
    obtain ⟨sB, hsB⟩ : ∃ sB : PancakeState σ,
        sB = { sA with locals := setLocal sA.locals "i" (BitVec.ofNat 64 (k + 1)) } := ⟨_, rfl⟩
    have hB := sem_assign (oracle := oracle) (x := "i") hiE hsAi
    rw [← hsB] at hB
    -- (4) the whole body (Seq); clamp is a no-op since assigns keep the clock
    have hclkSA : sA.clock = (decClock s).clock := by rw [hsA]
    have hclampSA : ({ sA with clock := min (decClock s).clock sA.clock } : PancakeState σ) = sA := by
      rw [hclkSA, Nat.min_self, ← hclkSA]
    have hbody : PancakeSem oracle scanBody (decClock s) = (none, sB) := by
      rw [scanBody, sem_seq_none hA, hclampSA, hB]
    -- (5) take the loop once, then the induction hypothesis on sB
    have hcond : eval s (.cmp .less (.var "i") (.var "len")) = some (1 : Word) := by
      have : eval s (.cmp .less (.var "i") (.var "len"))
          = some (if signedLt (BitVec.ofNat 64 k) (BitVec.ofNat 64 len) then 1 else 0) := by
        simp only [eval, hi, hlen]
      rw [this, signedLt_ofNat _ _ hkl63 hlen63]; simp only [hkl, decide_true, if_true]
    have hclkSB : sB.clock = s.clock - 1 := by simp only [hsB, hsA, decClock]
    have hSBclamp : ({ sB with clock := min (s.clock - 1) sB.clock } : PancakeState σ) = sB := by
      rw [hclkSB, Nat.min_self, ← hclkSB]
    -- read back the invariant locals on sB
    have hne1 : ("i" = "acc") = False := by decide
    have hne2 : ("acc" = "i") = False := by decide
    have hne3 : ("len" = "i") = False := by decide
    have hne4 : ("len" = "acc") = False := by decide
    have hne5 : ("buf" = "i") = False := by decide
    have hne6 : ("buf" = "acc") = False := by decide
    have hne7 : ("off" = "i") = False := by decide
    have hne8 : ("off" = "acc") = False := by decide
    have hBacc : sB.locals "acc" = some (BitVec.ofNat 64 (scanFrom a off (k + 1) 0)) := by
      rw [hsB, hsA]; simp only [setLocal, decClock, hne2, if_false, if_true]
    have hBi : sB.locals "i" = some (BitVec.ofNat 64 (k + 1)) := by
      rw [hsB]; simp only [setLocal, if_true]
    have hBlen : sB.locals "len" = some (BitVec.ofNat 64 len) := by
      rw [hsB, hsA]; simp only [setLocal, decClock, hne3, hne4, if_false]; exact hlen
    have hBbuf : sB.locals "buf" = some buf := by
      rw [hsB, hsA]; simp only [setLocal, decClock, hne5, hne6, if_false]; exact hbuf
    have hBoff : sB.locals "off" = some (BitVec.ofNat 64 off) := by
      rw [hsB, hsA]; simp only [setLocal, decClock, hne7, hne8, if_false]; exact hoff
    have hBmem : sB.memory = s.memory ∧ sB.memaddrs = s.memaddrs ∧ sB.be = s.be ∧
                 sB.baseAddr = s.baseAddr ∧ sB.ffi = s.ffi := by
      rw [hsB, hsA]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hBview : ViewBytes sB a buf off len := by
      intro i hi'; have := hview i hi'
      rw [hsB, hsA]; simpa [decClock] using this
    obtain ⟨s', hs'eq, hs'acc, hs'i, hs'len, hs'buf, hs'off,
            hs'mem, hs'ma, hs'be, hs'ba, hs'ffi, hs'frame⟩ :=
      ih (k + 1) sB (by omega) (by rw [hclkSB]; omega) hBacc hBi hBlen hBbuf hBoff hBview
    refine ⟨s', ?_, hs'acc, hs'i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- one loop iteration reduces to the recursive call on sB, closed by ih
      rw [scanWhile, PancakeSem]
      simp only [hcond, hbody, clampClock, ne_eq, show ((1 : Word) = 0) = False from by decide,
                 not_false_eq_true, if_true, hclock0, if_false]
      rw [hSBclamp, ← scanWhile, hs'eq]
    · rw [hs'len, hBlen, hlen]
    · rw [hs'buf, hBbuf, hbuf]
    · rw [hs'off, hBoff, hoff]
    · rw [hs'mem, hBmem.1]
    · rw [hs'ma, hBmem.2.1]
    · rw [hs'be, hBmem.2.2.1]
    · rw [hs'ba, hBmem.2.2.2.1]
    · rw [hs'ffi, hBmem.2.2.2.2]
    · intro x hxa hxi
      rw [hs'frame x hxa hxi, hsB, hsA]
      simp only [setLocal, decClock, if_neg hxi, if_neg hxa]

/-- `set_var` reads back what it wrote. -/
theorem setLocal_same (lc : String → Option Value) (v : String) (val : Value) :
    setLocal lc v val v = some val := by
  simp [setLocal]

/-- `set_var` leaves other variables alone. -/
theorem setLocal_ne (lc : String → Option Value) (v : String) (val : Value)
    {k : String} (h : k ≠ v) : setLocal lc v val k = lc k := by
  simp [setLocal, h]

/-- `Seq` step with a non-increasing clock: the inlined `fix_clock` clamp
collapses (`min s.clock s1.clock = s1.clock`). -/
theorem seq_step (o : Oracle σ) {c1 c2 : PancakeProg} {s s1 : PancakeState σ}
    (h : PancakeSem o c1 s = (none, s1)) (hclk : s1.clock ≤ s.clock) :
    PancakeSem o (.seq c1 c2) s = PancakeSem o c2 s1 := by
  rw [sem_seq_none (oracle := o) h]
  have hm : min s.clock s1.clock = s1.clock := by omega
  rw [hm]

/-- The premises of `region_scan_correct` are satisfiable: a state that declares the
four locals the scan reads and writes, over a one-byte view. -/
theorem region_scan_premises_hold (ffi : σ) :
    ∃ (s : PancakeState σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat),
      len < 2 ^ 63 ∧ len ≤ s.clock ∧
      s.locals "len" = some (BitVec.ofNat 64 len) ∧ s.locals "buf" = some buf ∧
      s.locals "off" = some (BitVec.ofNat 64 off) ∧ s.locals "result" = some 0 ∧
      ViewBytes s a buf off len := by
  refine ⟨{ locals := fun k => if k = "len" then some 1 else if k = "buf" then some 0
                        else if k = "off" then some 0 else if k = "result" then some 0 else none,
            memory := fun _ => 0, memaddrs := fun _ => true, be := false, clock := 4,
            ffi := ffi, baseAddr := 0 },
          [0], 0, 0, 1, by decide, (by decide : (1 : Nat) ≤ 4), rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have h0 : i = 0 := by omega
  subst h0
  show memLoadByte (fun _ => 0) (fun _ => true) false (0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 0)
      = some (([0] : List (BitVec 8))[0 + 0]!)
  decide

/-! ## 4. Composition: the region's in-bounds (digest) branch, end to end -/

/-- `Dec`: run the continuation on the extended scope, then restore the shadowed
binding (`res_var`). -/
theorem sem_dec {v e val cont res} {s s2 : PancakeState σ}
    (hval : eval s e = some val)
    (hcont : PancakeSem oracle cont { s with locals := setLocal s.locals v val } = (res, s2)) :
    PancakeSem oracle (.dec v e cont) s
      = (res, { s2 with locals := resVar s2.locals v (s.locals v) }) := by
  rw [PancakeSem]; simp only [hval]; rw [hcont]

/-- The region's else-branch (in-bounds path), exactly as lowered from the `.pnk`:
declare the digest accumulator + index, run the scan loop, publish `result`. -/
def scanElse : PancakeProg :=
  .dec "acc" (.const (BitVec.ofNat 64 0))
    (.dec "i" (.const (BitVec.ofNat 64 0))
      (.seq scanWhile (.assign "result" (.var "acc"))))

/-- END-TO-END for the digest branch: from a state with the arena view loaded
(`ViewBytes` = the load_vec FFI postcondition A0) and the control decoded, running
the emitted `scanElse` publishes `result = scanFrom a off len 0` — the SPEC
digest. Composes `sem_dec` (scope), `scan_loop` (the fuel induction), and
`sem_assign`. -/
theorem region_scan_correct {a : List (BitVec 8)} {buf : Word} {off len : Nat} {r0 : Word}
    {s : PancakeState σ}
    (hlen63 : len < 2 ^ 63) (hclock : len ≤ s.clock)
    (hlen : s.locals "len" = some (BitVec.ofNat 64 len))
    (hbuf : s.locals "buf" = some buf)
    (hoff : s.locals "off" = some (BitVec.ofNat 64 off))
    (hres : s.locals "result" = some r0)
    (hview : ViewBytes s a buf off len) :
    ∃ s', PancakeSem oracle scanElse s = (none, s') ∧
      s'.locals "result" = some (BitVec.ofNat 64 (scanFrom a off len 0)) := by
  -- string distinctness facts
  have da : ("acc" = "i") = False := by decide
  have dl1 : ("len" = "acc") = False := by decide
  have dl2 : ("len" = "i") = False := by decide
  have db1 : ("buf" = "acc") = False := by decide
  have db2 : ("buf" = "i") = False := by decide
  have do1 : ("off" = "acc") = False := by decide
  have do2 : ("off" = "i") = False := by decide
  have dr1 : ("result" = "acc") = False := by decide
  have dr2 : ("result" = "i") = False := by decide
  -- the two nested Dec scopes
  obtain ⟨s2, hs2⟩ : ∃ s2 : PancakeState σ, s2 = { s with locals := setLocal (setLocal s.locals "acc" (BitVec.ofNat 64 0)) "i" (BitVec.ofNat 64 0) } := ⟨_, rfl⟩
  -- feed scan_loop from index 0 (acc = scanFrom a off 0 0 = 0)
  have h2acc : s2.locals "acc" = some (BitVec.ofNat 64 (scanFrom a off 0 0)) := by
    rw [hs2]; simp only [setLocal, da, if_false, if_true, scanFrom]
  have h2i : s2.locals "i" = some (BitVec.ofNat 64 0) := by rw [hs2]; simp only [setLocal, if_true]
  have h2len : s2.locals "len" = some (BitVec.ofNat 64 len) := by
    rw [hs2]; simp only [setLocal, dl1, dl2, if_false]; exact hlen
  have h2buf : s2.locals "buf" = some buf := by
    rw [hs2]; simp only [setLocal, db1, db2, if_false]; exact hbuf
  have h2off : s2.locals "off" = some (BitVec.ofNat 64 off) := by
    rw [hs2]; simp only [setLocal, do1, do2, if_false]; exact hoff
  have h2clock : len ≤ s2.clock := by rw [hs2]; exact hclock
  have h2view : ViewBytes s2 a buf off len := by
    intro i hi'; have := hview i hi'; rw [hs2]; simpa using this
  obtain ⟨sW, hWeq, hWacc, hWi, hWlen, hWbuf, hWoff, hWmem, hWma, hWbe, hWba, hWffi, hWframe⟩ :=
    scan_loop oracle a buf off len hlen63 len 0 s2 (by omega) h2clock h2acc h2i h2len h2buf h2off h2view
  -- Seq: scanWhile then `result := acc` (on the clock-clamped post-loop state)
  obtain ⟨sWc, hsWc⟩ : ∃ sWc : PancakeState σ, sWc = { sW with clock := min s2.clock sW.clock } := ⟨_, rfl⟩
  have hAssign : eval sWc (.var "acc") = some (BitVec.ofNat 64 (scanFrom a off len 0)) := by
    rw [hsWc]; exact hWacc
  have hWres : sWc.locals "result" = some r0 := by
    rw [hsWc]
    show sW.locals "result" = some r0
    rw [hWframe "result" (by decide) (by decide), hs2]
    simp only [setLocal, dr1, dr2, if_false]
    exact hres
  obtain ⟨sV, hsV⟩ : ∃ sV : PancakeState σ, sV = { sWc with locals := setLocal sWc.locals "result" (BitVec.ofNat 64 (scanFrom a off len 0)) } := ⟨_, rfl⟩
  have hseq : PancakeSem oracle (.seq scanWhile (.assign "result" (.var "acc"))) s2 = (none, sV) := by
    rw [sem_seq_none hWeq, ← hsWc]
    have := sem_assign (oracle := oracle) (x := "result") hAssign hWres
    rw [← hsV] at this; exact this
  -- close the two Dec scopes (transport hseq across s2 = the scope literal)
  have hci := sem_dec (oracle := oracle)
      (s := { s with locals := setLocal s.locals "acc" (BitVec.ofNat 64 0) }) (v := "i")
      (e := .const (BitVec.ofNat 64 0)) (val := BitVec.ofNat 64 0) (by rfl) (hs2 ▸ hseq)
  have hfull := sem_dec (oracle := oracle) (s := s) (v := "acc")
      (e := .const (BitVec.ofNat 64 0)) (val := BitVec.ofNat 64 0) (by rfl) hci
  refine ⟨_, hfull, ?_⟩
  -- read `result` through the two scope-restores (result ∉ {acc,i})
  simp only [resVar, dr1, dr2, if_false, hsV, setLocal, if_true]

end DN.Compiler.Region
