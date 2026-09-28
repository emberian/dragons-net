-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Bytes
import DN.Compiler.Clock
import DN.Compiler.Region

/-!
# DN.Compiler.ByteCopy

Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md.
-/

namespace DN.Compiler.ByteCopy

open DN.Compiler DN.Compiler.Region DN.Compiler.Bytes DN.Compiler.Clock

variable {σ : Type}

/-! ## 1. The byte-addressed copy program. -/

/-- The copy body: `storeByte (dst+i) (loadByte (src+i)); i := i+1`.
`LoadByte`/`StoreByte` are the PACKED byte-access primitives (`memLoadByte`/
`putByte`), 8 bytes per word — not the word-slot `.loadWord`/`.store`. -/
def copyByteBody : PancakeProg :=
  .seq
    (.storeByte (.op .add (.var "dst") (.var "i"))
                (.loadByte (.op .add (.var "src") (.var "i"))))
    (.assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1))))

/-- The write `While`: `while (i < len) copyByteBody`. -/
def copyByteWhile : PancakeProg :=
  .while_ (.cmp .less (.var "i") (.var "len")) copyByteBody

/-- The byte-addressed write invariant, indexed by remaining iterations `n`
(current index `k = len - n`): the loop frame locals; the SOURCE region holds the
intended bytes `val` (read back by `memLoadByte`); the DESTINATION region is byte-
addressable; the first `k` destination bytes already carry `val`; and a FRAME
against the entry memory `m0` — every byte address not yet written reads exactly as
it did at entry (this is what a later program's already-written bytes ride on). -/
def copyInvB (dm : Word → Bool) (be : Bool) (m0 : Word → Word)
    (dst src : Word) (val : Nat → BitVec 8) (len : Nat)
    (n : Nat) (s : PancakeState σ) : Prop :=
  ∃ k, k + n = len ∧
    s.memaddrs = dm ∧ s.be = be ∧
    s.locals "dst" = some dst ∧
    s.locals "src" = some src ∧
    s.locals "i"   = some (BitVec.ofNat 64 k) ∧
    s.locals "len" = some (BitVec.ofNat 64 len) ∧
    (∀ j, j < len → memLoadByte s.memory dm be (src + BitVec.ofNat 64 j) = some (val j)) ∧
    (∀ j, j < len → dm (byteAlign (dst + BitVec.ofNat 64 j)) = true) ∧
    (∀ j, j < k → memLoadByte s.memory dm be (dst + BitVec.ofNat 64 j) = some (val j)) ∧
    (∀ a, (∀ j, j < k → a ≠ dst + BitVec.ofNat 64 j) →
        memLoadByte s.memory dm be a = memLoadByte m0 dm be a)

/-- What a copy leaves alone between an earlier state `t0` and a later one `t`: the frame with
every local but the index, and the external world's state. The frame lets every byte change,
since the invariant holds the memory. A step gives it against the state the step started in,
and `copyKeeps_trans` carries it back to the loop's start. -/
def copyKeeps (t0 t : PancakeState σ) : Prop :=
  Frame (· = "i") (fun _ => True) t0 t ∧ t.ffi = t0.ffi

theorem copyKeeps_trans {t0 t1 t2 : PancakeState σ} (h01 : copyKeeps t0 t1)
    (h12 : copyKeeps t1 t2) : copyKeeps t0 t2 :=
  ⟨h01.1.trans h12.1, h12.2.trans h01.2⟩

/-- The copy guard `i < len` evaluates to `0` exactly when the budget is spent. -/
theorem copyByte_guard (dm : Word → Bool) (be : Bool) (m0 : Word → Word)
    (dst src : Word) (val : Nat → BitVec 8) (len : Nat) (hlen63 : len < 2 ^ 63)
    (n : Nat) (s : PancakeState σ)
    (hI : copyInvB dm be m0 dst src val len n s) :
    eval s (.cmp .less (.var "i") (.var "len")) = some (if n = 0 then (0 : Word) else 1) := by
  obtain ⟨k, hkn, _, _, _, _, hi, hlen, _, _, _, _⟩ := hI
  have hk63 : k < 2 ^ 63 := by omega
  have hev : eval s (.cmp .less (.var "i") (.var "len"))
      = some (if signedLt (BitVec.ofNat 64 k) (BitVec.ofNat 64 len) then 1 else 0) := by
    simp only [eval, hi, hlen]
  rw [hev, signedLt_ofNat _ _ hk63 hlen63]
  by_cases hn : n = 0
  · have : k = len := by omega
    subst this; simp [hn]
  · have : k < len := by omega
    simp [hn, this]

/-- **ONE byte-copy iteration advances the invariant.** The `LoadByte` reads
`val k` at `src+k` (`memLoadByte`), the `StoreByte` lays it at the byte address
`dst+k` (`putByte`); source region and the earlier destination prefix survive
because `dst+k` is a distinct BYTE address from every source byte (`hdisj`) and
every earlier destination byte (`hinj`), and `load_putByte_diff` says a byte-store
disturbs reads at no other byte address. -/
theorem copyByte_step (o : Oracle σ) (dm : Word → Bool) (be : Bool) (m0 : Word → Word)
    (dst src : Word) (val : Nat → BitVec 8) (len : Nat)
    (hlen63 : len < 2 ^ 63)
    (hdisj : ∀ i j, i < len → j < len →
      dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < len → j < len → i ≠ j →
      dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (n : Nat) (s : PancakeState σ) (hI : copyInvB dm be m0 dst src val len (n + 1) s) :
    ∃ s2, PancakeSem o copyByteBody (decClock s) = (none, s2) ∧
      copyInvB dm be m0 dst src val len n s2 ∧ s2.clock = s.clock - 1 ∧ copyKeeps s s2 := by
  obtain ⟨k, hkn, hma, hbe, hdst, hsrc, hi, hlen, hsrcR, hdstA, hprog, hfr⟩ := hI
  have hklt : k < len := by omega
  have hdl : (decClock s).locals = s.locals := rfl
  have hdmem : (decClock s).memory = s.memory := rfl
  have hdma : (decClock s).memaddrs = dm := by rw [show (decClock s).memaddrs = s.memaddrs from rfl]; exact hma
  have hdbe : (decClock s).be = be := by rw [show (decClock s).be = s.be from rfl]; exact hbe
  -- store address and the loaded byte
  have haddr : eval (decClock s) (.op .add (.var "dst") (.var "i"))
      = some (dst + BitVec.ofNat 64 k) := by
    simp only [eval, hdl, hdst, hi]
  have hsrcAddr : eval (decClock s) (.op .add (.var "src") (.var "i"))
      = some (src + BitVec.ofNat 64 k) := by
    simp only [eval, hdl, hsrc, hi]
  have hloadB : memLoadByte (decClock s).memory (decClock s).memaddrs (decClock s).be
      (src + BitVec.ofNat 64 k) = some (val k) := by
    rw [hdmem, hdma, hdbe]; exact hsrcR k hklt
  have hload : eval (decClock s) (.loadByte (.op .add (.var "src") (.var "i")))
      = some ((val k).setWidth 64) := by
    show (match eval (decClock s) (.op .add (.var "src") (.var "i")) with
          | some w =>
            (match memLoadByte (decClock s).memory (decClock s).memaddrs (decClock s).be w with
             | some b => some (b.setWidth 64)
             | none => none)
          | none => none) = _
    simp only [hsrcAddr, hloadB]
  -- the byte store into `dst+k`
  have hdmk : dm (byteAlign (dst + BitVec.ofNat 64 k)) = true := hdstA k hklt
  have hstoreEq : memStoreByte (decClock s).memory (decClock s).memaddrs (decClock s).be
      (dst + BitVec.ofNat 64 k) (((val k).setWidth 64).setWidth 8)
      = some (putByte (decClock s).memory (decClock s).be (dst + BitVec.ofNat 64 k) (val k)) := by
    rw [setWidth64_8, hdma, hdbe]
    exact memStore_eq (decClock s).memory dm be (dst + BitVec.ofNat 64 k) (val k) hdmk
  obtain ⟨sS, hsSdef⟩ : ∃ sS : PancakeState σ, sS =
      { (decClock s) with memory := putByte (decClock s).memory (decClock s).be (dst + BitVec.ofNat 64 k) (val k) } := ⟨_, rfl⟩
  have hstore : PancakeSem o (.storeByte (.op .add (.var "dst") (.var "i"))
        (.loadByte (.op .add (.var "src") (.var "i")))) (decClock s) = (none, sS) := by
    rw [hsSdef]; exact evaluate_storeByte o (decClock s) haddr hload hstoreEq
  -- the index bump on sS
  have hsSi : sS.locals "i" = some (BitVec.ofNat 64 k) := by rw [hsSdef]; exact hi
  have hiE : eval sS (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))
      = some (BitVec.ofNat 64 (k + 1)) := by
    show (match eval sS (.var "i"), eval sS (.const (BitVec.ofNat 64 1)) with
          | some x, some y => some (x + y) | _, _ => none) = _
    simp only [eval, hsSi]
    rw [ofNat_add_small _ _ (by omega)]
  obtain ⟨sB, hsBdef⟩ : ∃ sB : PancakeState σ, sB =
      { sS with locals := setLocal sS.locals "i" (BitVec.ofNat 64 (k + 1)) } := ⟨_, rfl⟩
  have hbump : PancakeSem o (.assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))) sS
      = (none, sB) := by rw [hsBdef]; exact sem_assign (oracle := o) (x := "i") hiE hsSi
  -- body = seq (storeByte) (bump); the clock clamp collapses (store is clock-neutral)
  have hclkSS : sS.clock = (decClock s).clock := by rw [hsSdef]
  have hbody : PancakeSem o copyByteBody (decClock s) = (none, sB) := by
    rw [copyByteBody, sem_seq_none (oracle := o) hstore]
    have hm : min (decClock s).clock sS.clock = sS.clock := by rw [hclkSS]; omega
    rw [hm]
    have : ({ sS with clock := sS.clock } : PancakeState σ) = sS := rfl
    rw [this]; exact hbump
  -- memory / field facts for sB
  have hBmem : sB.memory = putByte s.memory be (dst + BitVec.ofNat 64 k) (val k) := by
    rw [hsBdef]; show sS.memory = _
    rw [hsSdef]; rw [hdmem, hdbe]
  have hBma : sB.memaddrs = dm := by
    rw [hsBdef]; show sS.memaddrs = dm; rw [hsSdef]; exact hdma
  have hBbe : sB.be = be := by
    rw [hsBdef]; show sS.be = be; rw [hsSdef]; exact hdbe
  have hBclk : sB.clock = s.clock - 1 := by
    rw [hsBdef]; show sS.clock = s.clock - 1; rw [hclkSS]; rfl
  -- locals for sB
  have dne1 : ("dst" = "i") = False := by decide
  have dne2 : ("src" = "i") = False := by decide
  have dne3 : ("len" = "i") = False := by decide
  have hBdst : sB.locals "dst" = some dst := by
    rw [hsBdef]; simp only [setLocal, dne1, if_false]; rw [hsSdef]; exact hdst
  have hBsrc : sB.locals "src" = some src := by
    rw [hsBdef]; simp only [setLocal, dne2, if_false]; rw [hsSdef]; exact hsrc
  have hBi : sB.locals "i" = some (BitVec.ofNat 64 (k + 1)) := by
    rw [hsBdef]; simp only [setLocal, if_true]
  have hBlen : sB.locals "len" = some (BitVec.ofNat 64 len) := by
    rw [hsBdef]; simp only [setLocal, dne3, if_false]; rw [hsSdef]; exact hlen
  -- source region survives (write at dst+k is a distinct byte address from src+j)
  have hBsrcR : ∀ j, j < len →
      memLoadByte sB.memory dm be (src + BitVec.ofNat 64 j) = some (val j) := by
    intro j hj
    rw [hBmem]
    rw [load_putByte_diff s.memory dm be (dst + BitVec.ofNat 64 k) (val k)
          (src + BitVec.ofNat 64 j) (fun h => hdisj k j hklt hj h.symm)]
    exact hsrcR j hj
  -- destination prefix now covers k+1
  have hBprog : ∀ j, j < k + 1 →
      memLoadByte sB.memory dm be (dst + BitVec.ofNat 64 j) = some (val j) := by
    intro j hj
    rw [hBmem]
    by_cases hjk : j = k
    · subst hjk
      exact load_putByte_same s.memory dm be (dst + BitVec.ofNat 64 j) (val j) (hdstA j hklt)
    · rw [load_putByte_diff s.memory dm be (dst + BitVec.ofNat 64 k) (val k)
            (dst + BitVec.ofNat 64 j) (hinj j k (by omega) hklt hjk)]
      exact hprog j (by omega)
  -- frame against m0 extends to k+1
  have hBfr : ∀ a, (∀ j, j < k + 1 → a ≠ dst + BitVec.ofNat 64 j) →
      memLoadByte sB.memory dm be a = memLoadByte m0 dm be a := by
    intro a ha
    rw [hBmem]
    rw [load_putByte_diff s.memory dm be (dst + BitVec.ofNat 64 k) (val k) a
          (ha k (by omega))]
    exact hfr a (fun j hj => ha j (by omega))
  -- everything but the index and the memory is as it was
  have hBkeeps : copyKeeps s sB := by
    refine ⟨⟨by rw [hBma, hma], by rw [hBbe, hbe], ?_, fun x hx => ?_,
      fun _ h => absurd trivial h⟩, ?_⟩
    · rw [hsBdef]; show sS.baseAddr = s.baseAddr; rw [hsSdef]; rfl
    · rw [hsBdef]; simp only [setLocal, hx, if_false]; rw [hsSdef]; rfl
    · rw [hsBdef]; show sS.ffi = s.ffi; rw [hsSdef]; rfl
  refine ⟨sB, hbody, ⟨k + 1, by omega, hBma, hBbe, hBdst, hBsrc, hBi, hBlen,
    hBsrcR, ?_, hBprog, hBfr⟩, hBclk, hBkeeps⟩
  intro j hj; exact hdstA j hj

/-! ## 2. `copySeg` — set the frame, run the loop, land the bytes. -/

/-- Declare the `dst/src/i/len` frame from constants, then run `copyByteWhile`. -/
def copySeg (dst src : Word) (len : Nat) : PancakeProg :=
  .dec "dst" (.const dst)
  (.dec "src" (.const src)
  (.dec "i"   (.const (BitVec.ofNat 64 0))
  (.dec "len" (.const (BitVec.ofNat 64 len))
        copyByteWhile)))

/-- **THE BYTE-ADDRESSED BODY COPY.** For a source region holding the bytes `val`
at `[src, src+len)` (`memLoadByte`) and an addressable, non-aliasing destination
region disjoint from the source, running `copySeg dst src len` lays those `len`
bytes at consecutive BYTE addresses `[dst, dst+len)` (read back by `memLoadByte`),
preserving every byte OUTSIDE `[dst, dst+len)` (the frame — so a previously-written
region survives) and `memaddrs`/`be`. This is the packed-byte body copy, the last
word-slot residual of the serialize chain, reproved in the faithful model.

`copySeg` declares its scratch variables, so their previous bindings are restored
on exit, and it assigns nothing else: its frame keeps every local, and the external
world's state is unchanged. The contract does not state the exact clock consumed, and its
memory frame is byte by byte rather than word by word; see
`docs/reviews/compiler-assurance.md`. -/
theorem copySeg_landsB (o : Oracle σ) (dst src : Word) (val : Nat → BitVec 8) (len : Nat)
    (hlen63 : len < 2 ^ 63)
    (hdisj : ∀ i j, i < len → j < len →
      dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < len → j < len → i ≠ j →
      dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (s : PancakeState σ)
    (hclk : len ≤ s.clock)
    (hsrcR : ∀ j, j < len →
      memLoadByte s.memory s.memaddrs s.be (src + BitVec.ofNat 64 j) = some (val j))
    (hdstA : ∀ j, j < len → s.memaddrs (byteAlign (dst + BitVec.ofNat 64 j)) = true) :
    ∃ s', PancakeSem o (copySeg dst src len) s = (none, s')
      ∧ (∀ j, j < len →
          memLoadByte s'.memory s.memaddrs s.be (dst + BitVec.ofNat 64 j) = some (val j))
      ∧ Frame (fun _ => False) (bytesFrom dst len) s s' ∧ s'.ffi = s.ffi := by
  -- the state inside the four declarations
  let s1 : PancakeState σ := { s with locals := setLocal s.locals "dst" dst }
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "src" src }
  let s3 : PancakeState σ := { s2 with locals := setLocal s2.locals "i" (BitVec.ofNat 64 0) }
  let s4 : PancakeState σ := { s3 with locals := setLocal s3.locals "len" (BitVec.ofNat 64 len) }
  -- field facts for s4
  have hmem4 : s4.memory = s.memory := rfl
  have hma4 : s4.memaddrs = s.memaddrs := rfl
  have hbe4 : s4.be = s.be := rfl
  have hclk4 : s4.clock = s.clock := rfl
  -- locals of s4
  have hdst4 : s4.locals "dst" = some dst := by
    show setLocal (setLocal (setLocal (setLocal s.locals "dst" dst) "src" src) "i"
      (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 len) "dst" = some dst
    rw [setLocal_ne _ _ _ (by decide), setLocal_ne _ _ _ (by decide),
        setLocal_ne _ _ _ (by decide), setLocal_same]
  have hsrc4 : s4.locals "src" = some src := by
    show setLocal (setLocal (setLocal (setLocal s.locals "dst" dst) "src" src) "i"
      (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 len) "src" = some src
    rw [setLocal_ne _ _ _ (by decide), setLocal_ne _ _ _ (by decide), setLocal_same]
  have hi4 : s4.locals "i" = some (BitVec.ofNat 64 0) := by
    show setLocal (setLocal (setLocal (setLocal s.locals "dst" dst) "src" src) "i"
      (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 len) "i" = some (BitVec.ofNat 64 0)
    rw [setLocal_ne _ _ _ (by decide), setLocal_same]
  have hlen4 : s4.locals "len" = some (BitVec.ofNat 64 len) := by
    show setLocal (setLocal (setLocal (setLocal s.locals "dst" dst) "src" src) "i"
      (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 len) "len" = some (BitVec.ofNat 64 len)
    rw [setLocal_same]
  -- the entry invariant at index 0 (k = 0)
  have hEntry : copyInvB s.memaddrs s.be s.memory dst src val len len s4 := by
    refine ⟨0, by omega, hma4, hbe4, hdst4, hsrc4, hi4, hlen4, ?_, ?_,
      by intro j hj; omega, ?_⟩
    · intro j hj; rw [hmem4, hma4, hbe4]; exact hsrcR j hj
    · intro j hj; rw [hma4]; exact hdstA j hj
    · intro a _; rw [hmem4, hma4, hbe4]
  -- run the loop, with the rest of the state held against its entry
  obtain ⟨s', hs'eq, ⟨hs'I, hs'keeps⟩, _hs'clk⟩ :=
    while_inv_cond_clk o (.cmp .less (.var "i") (.var "len")) copyByteBody
      (fun n t => copyInvB s.memaddrs s.be s.memory dst src val len n t ∧ copyKeeps s4 t)
      (fun n t hJ => copyByte_guard s.memaddrs s.be s.memory dst src val len hlen63 n t hJ.1)
      (fun n t hJ => by
        obtain ⟨t2, ht2, hI2, hclk2, hk2⟩ :=
          copyByte_step o s.memaddrs s.be s.memory dst src val len hlen63 hdisj hinj n t hJ.1
        exact ⟨t2, ht2, ⟨hI2, copyKeeps_trans hJ.2 hk2⟩, hclk2⟩)
      len s4 ⟨hEntry, Frame.refl _ _ s4, rfl⟩ (by rw [hclk4]; exact hclk)
  obtain ⟨k, hk0, hma', hbe', _, _, _, _, _, _, hprog', hfr'⟩ := hs'I
  obtain ⟨hfr4, hffi'⟩ := hs'keeps
  have hkl : k = len := by omega
  rw [hkl] at hprog' hfr'
  -- assemble copySeg's run
  have hrun : PancakeSem o (copySeg dst src len) s = (none, _) :=
    sem_dec (oracle := o) rfl
      (sem_dec (oracle := o) rfl (sem_dec (oracle := o) rfl (sem_dec (oracle := o) rfl hs'eq)))
  refine ⟨_, hrun, fun j hj => hprog' j hj, ⟨hma', hbe', hfr4.baseAddr, ?_,
    fun a ha => hfr' a (not_bytesFrom.1 ha)⟩, hffi'⟩
  -- the four declarations restore what they shadowed; the loop touched no other local
  intro x _
  simp only [resVar]
  by_cases hd : x = "dst"
  · simp [hd]
  by_cases hs : x = "src"
  · simp [hs, setLocal]
  by_cases hi : x = "i"
  · simp [hi, setLocal]
  by_cases hl : x = "len"
  · simp [hl, setLocal]
  simp only [hd, hs, hi, hl, if_false]
  rw [hfr4.locals x hi]
  simp [s4, s3, s2, s1, setLocal, hd, hs, hi, hl]

/-! ## 3. Non-vacuity: the loop is `len` byte stores, and a concrete 4-byte copy. -/

-- the body copy is a genuine `While` over `StoreByte`/`LoadByte`, not a stub:
example : copyByteWhile = .while_ (.cmp .less (.var "i") (.var "len"))
  (.seq (.storeByte (.op .add (.var "dst") (.var "i"))
                    (.loadByte (.op .add (.var "src") (.var "i"))))
        (.assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1))))) := rfl

/-- A state to copy in: the memory domain has the shape the CakeML compiler theorem
gives (word-aligned addresses below a bound), not every address, and the destination
word holds other bytes than the source, so a copy is observable. -/
def demoState (ffi : σ) : PancakeState σ :=
  { locals := fun _ => none,
    memory := fun k => if k = 8#64 then 0xffffffffffffffff#64 else 0x0706050403020100#64,
    memaddrs := fun a => decide (a.toNat % 8 = 0 ∧ a.toNat < 128),
    be := false, clock := 8, ffi := ffi, baseAddr := 0 }

/-- The entry state of a four-byte copy from address 64 to address 8: the loop's
working locals are bound and nothing has been written yet. -/
private def copyEntry : PancakeState Unit :=
  { demoState () with
    locals := fun k => if k = "dst" then some 8#64
                else if k = "src" then some 64#64
                else if k = "i" then some 0#64
                else if k = "len" then some 4#64 else none }

/-- Witness: the copy invariant is satisfiable. It holds at the entry state of
that copy, with no byte written yet — so the theorems that assume it are about a
state the program really reaches, not about a condition nothing meets. At this
state its written prefix is empty and its frame compares the memory with itself;
`copyInvB_after_one_step` is the witness where neither is so. -/
theorem copyInvB_witness :
    copyInvB (demoState ()).memaddrs (demoState ()).be copyEntry.memory 8#64 64#64
      (fun j => BitVec.ofNat 8 j) 4 4 copyEntry := by
  refine ⟨0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  · intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  · intro j hj
    exact absurd hj (by omega)
  · intro a _
    rfl

/-- Small sums are different words when they are different numbers. -/
private theorem small_sums_ne : ∀ (a b c d : Nat), a < 128 → b < 128 → c < 128 → d < 128 →
    a + b ≠ c + d →
      (BitVec.ofNat 64 a + BitVec.ofNat 64 b : Word) ≠ BitVec.ofNat 64 c + BitVec.ofNat 64 d := by
  have hsmall : ∀ (a b : Nat), a < 128 → b < 128 →
      ((BitVec.ofNat 64 a + BitVec.ofNat 64 b : Word)).toNat = a + b := by
    intro a b ha hb
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  intro a b c d ha hb hc hd hsum heq
  exact hsum (by rw [← hsmall a b ha hb, ← hsmall c d hc hd, heq])

/-- The four-byte copy from 64 to 8 writes no source byte and no destination byte twice. -/
private theorem demo_apart :
    (∀ i j, i < 4 → j < 4 →
      (8#64 : Word) + BitVec.ofNat 64 i ≠ 64#64 + BitVec.ofNat 64 j) ∧
    (∀ i j, i < 4 → j < 4 → i ≠ j →
      (8#64 : Word) + BitVec.ofNat 64 i ≠ 8#64 + BitVec.ofNat 64 j) :=
  ⟨fun i j _ _ => small_sums_ne 8 i 64 j (by omega) (by omega) (by omega) (by omega) (by omega),
   fun i j _ _ hij =>
     small_sums_ne 8 i 8 j (by omega) (by omega) (by omega) (by omega) (by omega)⟩

/-- A state like `demoState` whose caller has locals of its own: `x`, which the copy never names,
and `i`, which the copy uses for its index. -/
private def callerState (ffi : σ) : PancakeState σ :=
  { demoState ffi with
    locals := fun k => if k = "x" then some 42#64 else if k = "i" then some 7#64 else none }

/-- The premises of `copySeg_landsB` on any state with `demoState`'s memory and clock. -/
private theorem demo_copy (o : Oracle σ) (s : PancakeState σ)
    (hmem : s.memory = (demoState ()).memory) (hma : s.memaddrs = (demoState ()).memaddrs)
    (hbe : s.be = false) (hclk : s.clock = 8) :
    ∃ s', PancakeSem o (copySeg 8#64 64#64 4) s = (none, s')
      ∧ (∀ j, j < 4 →
          memLoadByte s'.memory s.memaddrs s.be (8#64 + BitVec.ofNat 64 j)
            = some (BitVec.ofNat 8 j))
      ∧ Frame (fun _ => False) (bytesFrom 8#64 4) s s' ∧ s'.ffi = s.ffi :=
  copySeg_landsB (o := o) 8#64 64#64 (fun j => BitVec.ofNat 8 j) 4 (by decide)
    demo_apart.1 demo_apart.2 s (by rw [hclk]; decide)
    (fun j hj => by
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rw [hmem, hma, hbe]
      rcases this with rfl | rfl | rfl | rfl <;> decide)
    (fun j hj => by
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rw [hma]
      rcases this with rfl | rfl | rfl | rfl <;> decide)

/-- The invariant also holds where it claims something: after one step of the same copy, the
written prefix holds the first byte, and the memory its frame compares against the entry memory
differs from that memory at the byte written; and the step kept every local but the index, the
memory domain, the byte order, the base address and the external world's state. -/
theorem copyInvB_after_one_step :
    ∃ s2, PancakeSem (Oracle.failing (σ := Unit)) copyByteBody (decClock copyEntry) = (none, s2)
      ∧ copyInvB (demoState ()).memaddrs (demoState ()).be copyEntry.memory 8#64 64#64
          (fun j => BitVec.ofNat 8 j) 4 3 s2
      ∧ copyKeeps copyEntry s2
      ∧ memLoadByte s2.memory (demoState ()).memaddrs (demoState ()).be (8#64 + BitVec.ofNat 64 0)
          ≠ memLoadByte copyEntry.memory (demoState ()).memaddrs (demoState ()).be
              (8#64 + BitVec.ofNat 64 0) := by
  obtain ⟨s2, hrun, hI, -, hkeeps⟩ :=
    copyByte_step Oracle.failing (demoState ()).memaddrs (demoState ()).be copyEntry.memory
      8#64 64#64 (fun j => BitVec.ofNat 8 j) 4 (by decide) demo_apart.1 demo_apart.2 3 copyEntry
      copyInvB_witness
  refine ⟨s2, hrun, hI, hkeeps, ?_⟩
  obtain ⟨k, hk, -, -, -, -, -, -, -, -, hprog, -⟩ := hI
  rw [hprog 0 (by omega)]
  show some (BitVec.ofNat 8 0) ≠ _
  decide

/-- **The premises of `copySeg_landsB` are satisfiable.** On `demoState`, copying
four bytes from address 64 to address 8 runs to completion, and the destination
bytes read back as the source bytes `0, 1, 2, 3`. -/
theorem copySeg_four_bytes (o : Oracle σ) (ffi : σ) :
    ∃ s', PancakeSem o (copySeg 8#64 64#64 4) (demoState ffi) = (none, s')
      ∧ ∀ j, j < 4 →
          memLoadByte s'.memory (demoState ffi).memaddrs (demoState ffi).be
              (8#64 + BitVec.ofNat 64 j)
            = some (BitVec.ofNat 8 j) := by
  obtain ⟨s', hrun, hland, -⟩ := demo_copy o (demoState ffi) rfl rfl rfl rfl
  exact ⟨s', hrun, hland⟩

/-- **A caller's locals survive the copy**: `x`, which the copy never names, and `i`, which it
declares for its own index and restores. -/
theorem copySeg_keeps_callers_locals (o : Oracle σ) (ffi : σ) :
    ∃ s', PancakeSem o (copySeg 8#64 64#64 4) (callerState ffi) = (none, s')
      ∧ s'.locals "x" = some 42#64 ∧ s'.locals "i" = some 7#64 := by
  obtain ⟨s', hrun, -, hfr, -⟩ := demo_copy o (callerState ffi) rfl rfl rfl rfl
  refine ⟨s', hrun, ?_, ?_⟩ <;> rw [hfr.locals _ id] <;> rfl

/-- …and the copy is what makes that true: before it runs, the destination holds
other bytes. -/
theorem demoState_before_copy (ffi : σ) :
    memLoadByte (demoState ffi).memory (demoState ffi).memaddrs (demoState ffi).be
        (8#64 + BitVec.ofNat 64 0)
      ≠ some (BitVec.ofNat 8 0) := by
  simp only [demoState]
  decide



end DN.Compiler.ByteCopy
