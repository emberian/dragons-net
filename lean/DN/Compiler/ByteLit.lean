-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Bytes
import DN.Compiler.Region

/-!
# DN.Compiler.ByteLit

Straight-line materialization of a literal byte string into memory: the program,
its correctness at byte addresses (every byte lands, every other byte address is
preserved), and the byte-region predicate it establishes.
-/

namespace DN.Compiler.ByteLit

open DN.Compiler DN.Compiler.Region DN.Compiler.Bytes

variable {σ : Type}

/-! ## 1. The byte-addressed literal materializer

`byteLit base bs` writes `bs` at consecutive BYTE addresses `base + i` with the
model's `StoreByte` (`mem_store_byte` = `byteAlign`+`setByte`, the packed-byte
primitive), read back by the faithful `mem_load_byte`. The bytes are packed, one
per byte address, which is the memory the compiler theorem provides. -/

/-- One literal byte store: `StoreByte (const a) (const (b widened))`. -/
def byteStore (a : Word) (b : BitVec 8) : PancakeProg :=
  .storeByte (.const a) (.const (b.setWidth 64))

/-- Straight-line literal materialization of `bs` at `base + off`, wire order. -/
def byteLitFrom (base : Word) (off : Nat) : List (BitVec 8) → PancakeProg
  | []      => .skip
  | b :: bs => .seq (byteStore (base + BitVec.ofNat 64 off) b) (byteLitFrom base (off + 1) bs)

/-- The literal materializer: lay `bs` at `base`. -/
def byteLit (base : Word) (bs : List (BitVec 8)) : PancakeProg := byteLitFrom base 0 bs

/-- One byte store lands `putByte` (the `mem_store_byte` image). -/
theorem byteStore_run (o : Oracle σ) (s : PancakeState σ) (a : Word) (b : BitVec 8)
    (hdm : s.memaddrs (byteAlign a) = true) :
    PancakeSem o (byteStore a b) s
      = (none, { s with memory := putByte s.memory s.be a b }) := by
  have hd : eval s (.const a) = some a := rfl
  have hs : eval s (.const (b.setWidth 64)) = some (b.setWidth 64) := rfl
  have hm : memStoreByte s.memory s.memaddrs s.be a ((b.setWidth 64).setWidth 8)
      = some (putByte s.memory s.be a b) := by
    rw [setWidth64_8]; exact memStore_eq s.memory s.memaddrs s.be a b hdm
  rw [byteStore, evaluate_storeByte o s hd hs hm]

/-- **THE MATERIALIZATION IS CORRECT.** For ALL `bs` and offsets: the straight-line
`StoreByte`s land every byte at its BYTE address (read back by `memLoadByte`),
preserve every un-written byte address (byte-level frame — survives sub-word
packing, unlike a cell frame), and preserve `memaddrs`, `be`, locals and clock.
Nothing about the CONTENT of memory is assumed; the bytes come from the program.
Injectivity on `[0, N)` is the standard "output region does not alias itself". -/
theorem byteLitFrom_correct (o : Oracle σ) (base : Word) (N : Nat)
    (hinj : ∀ p q, p < N → q < N → p ≠ q →
      base + BitVec.ofNat 64 p ≠ base + BitVec.ofNat 64 q) :
    ∀ (bs : List (BitVec 8)) (off : Nat) (s : PancakeState σ), off + bs.length ≤ N →
      (∀ j, j < bs.length →
        s.memaddrs (byteAlign (base + BitVec.ofNat 64 (off + j))) = true) →
      ∃ s', PancakeSem o (byteLitFrom base off bs) s = (none, s')
        ∧ (∀ j, j < bs.length →
            memLoadByte s'.memory s.memaddrs s.be (base + BitVec.ofNat 64 (off + j))
              = some bs[j]!)
        ∧ (∀ a, (∀ j, j < bs.length → a ≠ base + BitVec.ofNat 64 (off + j)) →
            memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a)
        ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.locals = s.locals ∧ s'.clock = s.clock := by
  intro bs
  induction bs with
  | nil =>
    intro off s _ _
    refine ⟨s, ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · show PancakeSem o PancakeProg.skip s = (none, s); rw [PancakeSem]
    · intro j hj; simp at hj
  | cons b bs ih =>
    intro off s hle haddr
    have hlen : off + bs.length + 1 ≤ N := by simp only [List.length_cons] at hle; omega
    have hoff : off < N := by omega
    have haddr0 : s.memaddrs (byteAlign (base + BitVec.ofNat 64 off)) = true := by
      have := haddr 0 (by simp); simpa using this
    let s1 : PancakeState σ := { s with memory := putByte s.memory s.be (base + BitVec.ofNat 64 off) b }
    have h1 : PancakeSem o (byteStore (base + BitVec.ofNat 64 off) b) s = (none, s1) :=
      byteStore_run o s (base + BitVec.ofNat 64 off) b haddr0
    -- tail addressability from `s1`
    have haddr' : ∀ j, j < bs.length →
        s1.memaddrs (byteAlign (base + BitVec.ofNat 64 (off + 1 + j))) = true := by
      intro j hj
      show s.memaddrs _ = true
      have := haddr (j + 1) (by simp only [List.length_cons]; omega)
      rwa [show off + (j + 1) = off + 1 + j from by omega] at this
    obtain ⟨s', hrun, hval, hframe, hma, hbe, hloc, hclk⟩ := ih (off + 1) s1 (by omega) haddr'
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show PancakeSem o (.seq (byteStore (base + BitVec.ofNat 64 off) b)
            (byteLitFrom base (off + 1) bs)) s = (none, s')
      rw [seq_step o h1 (Nat.le_of_eq (rfl : s1.clock = s.clock))]; exact hrun
    · -- landing
      intro j hj
      cases j with
      | zero =>
        have hcond : ∀ k, k < bs.length →
            base + BitVec.ofNat 64 off ≠ base + BitVec.ofNat 64 (off + 1 + k) := by
          intro k hk; exact hinj off (off + 1 + k) hoff (by omega) (by omega)
        have hstep1 : memLoadByte s'.memory s.memaddrs s.be (base + BitVec.ofNat 64 off)
            = memLoadByte s1.memory s.memaddrs s.be (base + BitVec.ofNat 64 off) :=
          hframe (base + BitVec.ofNat 64 off) hcond
        have hstep2 : memLoadByte s1.memory s.memaddrs s.be (base + BitVec.ofNat 64 off)
            = some b :=
          load_putByte_same s.memory s.memaddrs s.be (base + BitVec.ofNat 64 off) b haddr0
        show memLoadByte s'.memory s.memaddrs s.be (base + BitVec.ofNat 64 (off + 0)) = _
        rw [show off + 0 = off from rfl, hstep1, hstep2]
        rw [show (b :: bs)[0]! = b from rfl]
      | succ j' =>
        have hj' : j' < bs.length := by simp only [List.length_cons] at hj; omega
        have hv := hval j' hj'
        show memLoadByte s'.memory s.memaddrs s.be (base + BitVec.ofNat 64 (off + (j' + 1))) = _
        rw [show off + (j' + 1) = off + 1 + j' from by omega,
            show (b :: bs)[j' + 1]! = bs[j']! from rfl]
        exact hv
    · -- frame
      intro a ha
      have haTail : ∀ j, j < bs.length → a ≠ base + BitVec.ofNat 64 (off + 1 + j) := by
        intro j hj
        have := ha (j + 1) (by simp only [List.length_cons]; omega)
        rwa [show off + (j + 1) = off + 1 + j from by omega] at this
      have hHead : a ≠ base + BitVec.ofNat 64 off := by
        have := ha 0 (by simp); simpa using this
      have hs1 : memLoadByte s'.memory s.memaddrs s.be a
          = memLoadByte s1.memory s.memaddrs s.be a := hframe a haTail
      rw [hs1]
      exact load_putByte_diff s.memory s.memaddrs s.be (base + BitVec.ofNat 64 off) b a hHead
    · exact hma
    · exact hbe
    · exact hloc
    · exact hclk

/-! ## 2. Where the literal lands. -/

/-- **`byteLit` lands the byte string byte-addressed.** -/
theorem byteLit_landsB (o : Oracle σ) (base : Word) (bs : List (BitVec 8)) (s : PancakeState σ)
    (hinj : ∀ p q, p < bs.length → q < bs.length → p ≠ q →
      base + BitVec.ofNat 64 p ≠ base + BitVec.ofNat 64 q)
    (haddr : ∀ j, j < bs.length → s.memaddrs (byteAlign (base + BitVec.ofNat 64 j)) = true) :
    ∃ s', PancakeSem o (byteLit base bs) s = (none, s')
      ∧ memBytesAt s'.memory s.memaddrs s.be base bs
      ∧ (∀ a, (∀ j, j < bs.length → a ≠ base + BitVec.ofNat 64 j) →
          memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a)
      ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.locals = s.locals ∧ s'.clock = s.clock := by
  obtain ⟨s', hrun, hval, hframe, hma, hbe, hloc, hclk⟩ :=
    byteLitFrom_correct o base bs.length hinj bs 0 s (by omega)
      (by intro j hj; simpa using haddr j hj)
  refine ⟨s', hrun, ?_, ?_, hma, hbe, hloc, hclk⟩
  · intro i hi; have := hval i hi; simpa using this
  · intro a ha; exact hframe a (by intro j hj; simpa using ha j hj)

/-! ## 3. The premises are satisfiable. -/

/-- A state to write into: the memory domain has the shape the CakeML compiler theorem
gives (word-aligned addresses below a bound), and the target bytes start out different. -/
def demoState (ffi : σ) : PancakeState σ :=
  { locals := fun _ => none, memory := fun _ => 0#64,
    memaddrs := fun a => decide (a.toNat % 8 = 0 ∧ a.toNat < 128),
    be := false, clock := 4, ffi := ffi, baseAddr := 0 }

/-- Two literal bytes land at 8 and 9 on `demoState`. -/
theorem byteLit_two_bytes (o : Oracle σ) (ffi : σ) :
    ∃ s', PancakeSem o (byteLit 8#64 [1#8, 2#8]) (demoState ffi) = (none, s')
      ∧ memBytesAt s'.memory (demoState ffi).memaddrs (demoState ffi).be 8#64 [1#8, 2#8] := by
  obtain ⟨s', hrun, hland, -, -, -, -, -⟩ :=
    byteLit_landsB (o := o) 8#64 [1#8, 2#8] (demoState ffi)
      (by
        intro p q hp hq hpq heq
        simp only [List.length_cons, List.length_nil] at hp hq
        have := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
        omega)
      (fun j hj => by
        have : j = 0 ∨ j = 1 := by simp only [List.length_cons, List.length_nil] at hj; omega
        simp only [demoState]
        rcases this with rfl | rfl <;> decide)
  exact ⟨s', hrun, hland⟩

/-- …and the write is what makes that true: before it runs, byte 8 is zero. -/
theorem demoState_before_write (ffi : σ) :
    ¬ memBytesAt (demoState (σ := σ) ffi).memory (demoState (σ := σ) ffi).memaddrs
        (demoState (σ := σ) ffi).be 8#64 [1#8, 2#8] := by
  intro h
  have := h 0 (by decide)
  simp only [demoState] at this
  exact absurd this (by decide)

end DN.Compiler.ByteLit
