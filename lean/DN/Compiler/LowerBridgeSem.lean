-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Bytes
import DN.Compiler.LowerBridge
import DN.Compiler.Region

/-!
# DN.Compiler.LowerBridgeSem

Running the lowered store-list model: the bytes land at their byte addresses and
every other byte address is preserved.
-/

namespace DN.Compiler.LowerBridgeSem
open DN.Compiler DN.Compiler.Bytes DN.Compiler.Region
open DN.Compiler.LowerBridge (addrModel storesModel storesInto)
open DN.Compiler.Lower (lowerStmtsFold)

variable {σ : Type}



/-! ## eval of the emitted store address -/

theorem eval_addrModel {σ : Type} (s : PancakeState σ) (dst : String) (base : Word) (k : Nat)
    (hbase : s.locals dst = some base) :
    eval s (addrModel dst k) = some (base + BitVec.ofNat 64 k) := by
  unfold addrModel
  by_cases hk : k = 0
  · subst hk
    simp only [beq_self_eq_true, if_true]
    show s.locals dst = some (base + BitVec.ofNat 64 0)
    rw [hbase]; simp
  · rw [if_neg (by simpa using hk)]
    show (match eval s (.var dst), eval s (.const (BitVec.ofNat 64 k)) with
          | some a, some b => some (a + b) | _, _ => none) = _
    simp only [eval, hbase]

/-! ## the byte-store post-state and its read-back -/


/-- The state after one `st8 adr := bt`: the memory of `putByte`, everything else kept. -/
def afterStore (s : PancakeState σ) (adr : Word) (bt : BitVec 8) : PancakeState σ :=
  { s with memory := putByte s.memory s.be adr bt }

/-- Running one emitted byte store from a state whose `dst` holds `base` lands `afterStore`. -/
theorem run_headStore (o : Oracle σ) (s : PancakeState σ) (dst : String) (base : Word)
    (k b : Nat) (hbase : s.locals dst = some base)
    (haddr : s.memaddrs (byteAlign (base + BitVec.ofNat 64 k)) = true) :
    PancakeSem o (.storeByte (addrModel dst k) (.const (BitVec.ofNat 64 b))) s
      = (none, afterStore s (base + BitVec.ofNat 64 k) ((BitVec.ofNat 64 b).setWidth 8)) := by
  have hd : eval s (addrModel dst k) = some (base + BitVec.ofNat 64 k) :=
    eval_addrModel s dst base k hbase
  have hs : eval s (.const (BitVec.ofNat 64 b)) = some (BitVec.ofNat 64 b) := rfl
  have hm : memStoreByte s.memory s.memaddrs s.be (base + BitVec.ofNat 64 k)
              ((BitVec.ofNat 64 b).setWidth 8)
            = some (afterStore s (base + BitVec.ofNat 64 k) ((BitVec.ofNat 64 b).setWidth 8)).memory :=
    memStore_eq s.memory s.memaddrs s.be _ _ haddr
  rw [evaluate_storeByte o s hd hs hm]
  rfl

/-! ## read-back of the stored byte, and non-interference for other addresses -/

theorem load_afterStore_same (s : PancakeState σ) (adr : Word) (bt : BitVec 8)
    (haddr : s.memaddrs (byteAlign adr) = true) :
    memLoadByte (afterStore s adr bt).memory s.memaddrs s.be adr = some bt :=
  load_putByte_same s.memory s.memaddrs s.be adr bt haddr

theorem load_afterStore_ne (s : PancakeState σ) (adr adr' : Word) (bt : BitVec 8)
    (hne : adr' ≠ adr) :
    memLoadByte (afterStore s adr bt).memory s.memaddrs s.be adr'
      = memLoadByte s.memory s.memaddrs s.be adr' :=
  load_putByte_diff s.memory s.memaddrs s.be adr bt adr' hne





theorem sem_seq_none' (o : Oracle σ) {c1 c2 : PancakeProg} {s s1 s' : PancakeState σ}
    (h1 : PancakeSem o c1 s = (none, s1)) (hclk : s1.clock = s.clock)
    (h2 : PancakeSem o c2 s1 = (none, s')) :
    PancakeSem o (.seq c1 c2) s = (none, s') := by
  rw [seq_step o h1 (Nat.le_of_eq hclk)]; exact h2

@[simp] theorem afterStore_locals (s : PancakeState σ) (a : Word) (bt : BitVec 8) :
    (afterStore s a bt).locals = s.locals := rfl
@[simp] theorem afterStore_memaddrs (s : PancakeState σ) (a : Word) (bt : BitVec 8) :
    (afterStore s a bt).memaddrs = s.memaddrs := rfl
@[simp] theorem afterStore_be (s : PancakeState σ) (a : Word) (bt : BitVec 8) :
    (afterStore s a bt).be = s.be := rfl
@[simp] theorem afterStore_clock (s : PancakeState σ) (a : Word) (bt : BitVec 8) :
    (afterStore s a bt).clock = s.clock := rfl

/-- **THE BYTE-LANDING INDUCTION.** Running the emitted model store list from a state
whose `dst` holds `base` lands each byte at its address (read back via the faithful
`memLoadByte`), and leaves every un-written byte address untouched — the byte-level
frame, which survives sub-word packing (unlike a cell frame). -/
theorem storesRun (o : Oracle σ) (dst : String) (base : Word) :
    ∀ (ps : List (Nat × Nat)) (s : PancakeState σ),
      s.locals dst = some base →
      (∀ p ∈ ps, s.memaddrs (byteAlign (base + BitVec.ofNat 64 p.1)) = true) →
      (∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.1 →
          base + BitVec.ofNat 64 p.1 ≠ base + BitVec.ofNat 64 q.1) →
      (ps.map Prod.fst).Nodup →
      ∃ s', PancakeSem o (storesModel dst ps) s = (none, s')
        ∧ s'.locals = s.locals ∧ s'.memaddrs = s.memaddrs
        ∧ (∀ p ∈ ps, memLoadByte s'.memory s.memaddrs s.be
              (base + BitVec.ofNat 64 p.1) = some ((BitVec.ofNat 64 p.2).setWidth 8))
        ∧ (∀ adr', (∀ p ∈ ps, adr' ≠ base + BitVec.ofNat 64 p.1) →
              memLoadByte s'.memory s.memaddrs s.be adr'
                = memLoadByte s.memory s.memaddrs s.be adr') := by
  intro ps
  induction ps with
  | nil =>
    intro s _ _ _ _
    refine ⟨s, ?_, rfl, rfl, ?_, ?_⟩
    · show PancakeSem o PancakeProg.skip s = (none, s); rw [PancakeSem]
    · intro p hp; simp at hp
    · intro adr' _; rfl
  | cons p ps' ih =>
    intro s hbase haddr hdist hnodup
    -- the head store lands `afterStore`
    have haddrp : s.memaddrs (byteAlign (base + BitVec.ofNat 64 p.1)) = true := haddr p (by simp)
    have hhead : PancakeSem o (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2))) s
        = (none, afterStore s (base + BitVec.ofNat 64 p.1) ((BitVec.ofNat 64 p.2).setWidth 8)) :=
      run_headStore o s dst base p.1 p.2 hbase haddrp
    have hnodupT : (ps'.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hnodup)).2
    have hpnotin : p.1 ∉ ps'.map Prod.fst := (List.nodup_cons.mp (by simpa using hnodup)).1
    -- p.1 differs from every tail offset
    have hne_off : ∀ q ∈ ps', p.1 ≠ q.1 := by
      intro q hq hqe
      exact hpnotin (by rw [hqe]; exact List.mem_map_of_mem hq)
    have hne_adr : ∀ q ∈ ps', (base + BitVec.ofNat 64 p.1) ≠ base + BitVec.ofNat 64 q.1 := by
      intro q hq
      exact hdist p (by simp) q (by simp [hq]) (hne_off q hq)
    cases ps' with
    | nil =>
      -- ps = [p] : storesModel is the bare head store
      refine ⟨afterStore s (base + BitVec.ofNat 64 p.1) ((BitVec.ofNat 64 p.2).setWidth 8),
              ?_, rfl, rfl, ?_, ?_⟩
      · simp only [storesModel]; exact hhead
      · intro q hq
        simp only [List.mem_singleton] at hq; subst q
        exact load_afterStore_same s (base + BitVec.ofNat 64 p.1) _ haddrp
      · intro adr' hfr
        exact load_afterStore_ne s (base + BitVec.ofNat 64 p.1) adr' _ (hfr p (by simp))
    | cons q rest =>
      -- ps = p :: q :: rest : storesModel is a seq (head ; tail)
      obtain ⟨s', hsem, hloc, hma, hland, hframe⟩ :=
        ih (afterStore s (base + BitVec.ofNat 64 p.1) ((BitVec.ofNat 64 p.2).setWidth 8))
           hbase
           (by intro r hr; exact haddr r (by simp [hr]))
           (by intro a ha b hb hab; exact hdist a (by simp [ha]) b (by simp [hb]) hab)
           hnodupT
      refine ⟨s', ?_, hloc, hma, ?_, ?_⟩
      · -- compose seq
        have hunf : storesModel dst (p :: q :: rest)
            = .seq (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2)))
                   (storesModel dst (q :: rest)) := rfl
        rw [hunf]
        exact sem_seq_none' o hhead rfl hsem
      · intro p' hp'
        rcases List.mem_cons.mp hp' with hpe | hin
        · -- head byte survives the tail (byte-frame at its address, then read-back)
          subst p'
          have h1 := hframe (base + BitVec.ofNat 64 p.1) hne_adr
          simp only [afterStore_memaddrs, afterStore_be] at h1
          rw [h1]
          exact load_afterStore_same s (base + BitVec.ofNat 64 p.1) _ haddrp
        · have h2 := hland p' hin
          simp only [afterStore_memaddrs, afterStore_be] at h2
          exact h2
      · intro adr' hfrall
        have h1 := hframe adr' (by intro r hr; exact hfrall r (by simp [hr]))
        simp only [afterStore_memaddrs, afterStore_be] at h1
        rw [h1]
        exact load_afterStore_ne s (base + BitVec.ofNat 64 p.1) adr' _ (hfrall p (by simp))





/-- **Byte-addressed** region contents: reading byte `i` at consecutive byte address
`base + i` via the faithful `mem_load_byte` returns byte `bs[i]` (its low-8 image).
The `Nat` spelling of `Bytes.memBytesAt`. -/
def MemBytesAtB (m : Word → Word) (dm : Word → Bool) (be : Bool)
    (base : Word) (bs : List Nat) : Prop :=
  ∀ i, i < bs.length →
    memLoadByte m dm be (base + BitVec.ofNat 64 i)
      = some ((BitVec.ofNat 64 bs[i]!).setWidth 8)

/-- **THE BYTE-STORE LANDING LEMMA.** Running the model `storeByte` program that the
emitted response head lowers to lands the byte string `bs` byte-addressed at `base`:
every byte reads back at its own address, even where consecutive bytes pack into one
64-bit word (a word-slot frame cannot express that). -/
theorem storesModel_landsB (o : Oracle σ) (dst : String) (base : Word) (bs : List Nat)
    (s : PancakeState σ)
    (hbase : s.locals dst = some base)
    (haddr : ∀ i, i < bs.length →
        s.memaddrs (byteAlign (base + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs.length → j < bs.length → i ≠ j →
        base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j) :
    ∃ s', PancakeSem o (storesModel dst ((List.range bs.length).zip bs)) s = (none, s')
      ∧ s'.memaddrs = s.memaddrs
      ∧ MemBytesAtB s'.memory s.memaddrs s.be base bs := by
  obtain ⟨s', hsem, _, hma, hland, _⟩ :=
    storesRun o dst base ((List.range bs.length).zip bs) s hbase
      (by intro p hp
          obtain ⟨a, b⟩ := p
          exact haddr a (by simpa using (List.of_mem_zip hp).1))
      (by intro p hp q hq hpq
          obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
          exact hinj a c (by simpa using (List.of_mem_zip hp).1)
                        (by simpa using (List.of_mem_zip hq).1) hpq)
      (by rw [List.map_fst_zip (by simp)]; exact List.nodup_range)
  refine ⟨s', hsem, hma, ?_⟩
  intro i hi
  have hmem : (i, bs[i]!) ∈ (List.range bs.length).zip bs := by
    have hlen : i < ((List.range bs.length).zip bs).length := by simp [List.length_zip, hi]
    have hz : ((List.range bs.length).zip bs)[i] = (i, bs[i]!) := by
      rw [List.getElem_zip]; simp [List.getElem_range, hi, getElem!_pos]
    rw [← hz]; exact List.getElem_mem hlen
  have hh := hland (i, bs[i]!) hmem
  simpa using hh

/-- **INTERNAL AST-TO-MODEL CORRECTNESS.** The per-byte `st8` AST
`storesInto dst bs` lowers through the internal `lowerStmtsFold` function to a
named model program `P`, and running `P` lands `bs` byte-addressed. This theorem
does not mention pretty-printed bytes or the CakeML parser and therefore does not
close the printed-source/parser bridge. See `docs/reviews/compiler-assurance.md`. -/
theorem storesInto_landsB (o : Oracle σ) (dst : String) (base : Word) (bs : List Nat)
    (s : PancakeState σ)
    (hbase : s.locals dst = some base)
    (haddr : ∀ i, i < bs.length →
        s.memaddrs (byteAlign (base + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs.length → j < bs.length → i ≠ j →
        base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j) :
    ∃ P, lowerStmtsFold (storesInto dst bs) = some P
      ∧ ∃ s', PancakeSem o P s = (none, s')
          ∧ MemBytesAtB s'.memory s.memaddrs s.be base bs := by
  refine ⟨storesModel dst ((List.range bs.length).zip bs),
          DN.Compiler.LowerBridge.storesInto_lowers dst bs, ?_⟩
  obtain ⟨s', hsem, _, hmb⟩ := storesModel_landsB o dst base bs s hbase haddr hinj
  exact ⟨s', hsem, hmb⟩


end DN.Compiler.LowerBridgeSem
