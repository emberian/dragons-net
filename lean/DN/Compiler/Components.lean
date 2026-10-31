-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.ByteCopy
import DN.Compiler.Certificate
import DN.Compiler.Kernels

/-!
# DN.Compiler.Components

**Components with every obligation named, and their composition** (issue #1). A `Contract` names
what a component asks of the state it starts in — the locals it reads, the memory it reads and
writes, what the external world has to answer, the clock it needs — and what it promises of the one
it ends in: what it computes, the locals and the bytes it may change and nothing else, what it may
make of the external world, `@base` as it was, and at most its clock spent. A `Component` is code that keeps its contract from every state the
contract admits, with a state that it admits (`Certificate`). Two compose (`Component.seq`): the
first's promise has to give the second what it asks.

Two components with memory: a literal stamped at a pointer (`stamp`), and a copy between two
buffers (`copy`); their composition stamps a buffer and copies it to another (`stampThenCopy`),
each with a state its contract admits, its memory a window of the shape the CakeML theorem gives.
The exported function `Kernels.stampCopy` runs that composition (`stampCopy_run`), and the baseline
lane runs it on the machine (`native/stamp_check.c`). An external call is a component too (`call`):
it asks the world to answer and promises what the answer makes of it, here a world that counts. No run ends with more clock than it began with
(`clock_le`), so statements in sequence group either way (`seq_assoc`).
-/

namespace DN.Compiler.Components

open DN.Compiler DN.Compiler.Clock DN.Compiler.Syntax DN.Compiler.Lower DN.Compiler.Bytes
open DN.Compiler.Kernels (stampLiteral)

variable {σ : Type}

/-! ## Runs spend the clock, never add to it -/

/-- **No run gives itself clock**: a run ends with at most the clock it began with. -/
theorem clock_le (o : Oracle σ) :
    ∀ (n : Nat) (p : PancakeProg) (s : PancakeState σ), s.clock ≤ n →
      (PancakeSem o p s).2.clock ≤ s.clock := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro p
  induction p with
  | skip => intro s _; rw [PancakeSem.eq_1]; exact Nat.le_refl _
  | dec v e c ih =>
    intro s hc
    rw [PancakeSem.eq_2]
    split
    · exact ih _ hc
    · exact Nat.le_refl _
  | assign v e =>
    intro s _
    rw [PancakeSem.eq_3]
    split <;> exact Nat.le_refl _
  | store d e =>
    intro s _
    rw [PancakeSem.eq_4]
    repeat' split
    all_goals exact Nat.le_refl _
  | storeByte d e =>
    intro s _
    rw [PancakeSem.eq_10]
    repeat' split
    all_goals exact Nat.le_refl _
  | extCall name c cl a al =>
    intro s _
    rw [PancakeSem.eq_5]
    repeat' split
    all_goals exact Nat.le_refl _
  | seq c1 c2 ih1 ih2 =>
    intro s hc
    rw [PancakeSem.eq_6]
    simp only [clampClock]
    split
    · have := ih2 { (PancakeSem o c1 s).2 with clock := min s.clock (PancakeSem o c1 s).2.clock }
        (by simp only; omega)
      simp only at this
      omega
    · (try simp only); omega
  | cond e c1 c2 ih1 ih2 =>
    intro s hc
    rw [PancakeSem.eq_7]
    split
    · split
      · exact ih1 s hc
      · exact ih2 s hc
    · exact Nat.le_refl _
  | while_ e c _ =>
    intro s hc
    rw [PancakeSem.eq_8]
    split
    · split
      · split
        · exact Nat.le_refl _
        · have hb := ihn (s.clock - 1) (by omega) c (decClock s) (by simp [decClock])
          revert hb
          cases PancakeSem o c (decClock s) with
          | mk r t =>
            intro hb
            simp only [clampClock]
            have hw := ihn (s.clock - 1) (by omega) (.while_ e c) { t with clock := min (s.clock - 1) t.clock }
              (by simp only; omega)
            try dsimp only [decClock] at hb hw
            split
            all_goals first | omega | (dsimp only; omega)
      · exact Nat.le_refl _
    · exact Nat.le_refl _
  | ret e =>
    intro s _
    rw [PancakeSem.eq_9]
    split <;> exact Nat.le_refl _
  | decCall rt f args cont _ =>
    intro s hc
    rw [PancakeSem.eq_11]
    split
    · split
      · rename_i body params _
        split
        · exact Nat.le_refl _
        · have hb := ihn (s.clock - 1) (by omega) body { decClock s with locals := params }
            (by simp [decClock])
          revert hb
          cases PancakeSem o body { decClock s with locals := params } with
          | mk r t =>
            intro hb
            simp only [clampClock]
            try dsimp only [decClock] at hb
            split
            · rename_i _ v
              have hw := ihn (s.clock - 1) (by omega) cont
                { t with clock := min (s.clock - 1) t.clock, locals := setLocal s.locals rt v }
                (by simp only; omega)
              try dsimp only at hw ⊢
              omega
            · unfold callEnded
              split <;> (dsimp only [emptyLocals]; omega)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem run_clock_le (o : Oracle σ) (p : PancakeProg) (s : PancakeState σ) :
    (PancakeSem o p s).2.clock ≤ s.clock :=
  clock_le o s.clock p s (Nat.le_refl _)

/-- So clamping a run's clock to the clock it began with changes nothing. -/
theorem clamp_run (o : Oracle σ) (p : PancakeProg) (s : PancakeState σ) :
    clampClock s.clock (PancakeSem o p s) = PancakeSem o p s := by
  have h := run_clock_le o p s
  revert h
  cases PancakeSem o p s with
  | mk r t =>
    intro h
    simp only [clampClock] at h ⊢
    rw [Nat.min_eq_right h]

/-- A sequence runs its second statement from where its first ended, the clamp of its clock a no-op. -/
theorem seq_run (o : Oracle σ) (p q : PancakeProg) (s : PancakeState σ) :
    PancakeSem o (.seq p q) s = match (PancakeSem o p s).1 with
      | none => PancakeSem o q (PancakeSem o p s).2
      | some r => (some r, (PancakeSem o p s).2) := by
  rw [PancakeSem.eq_6, clamp_run]
  rfl

/-- **Statements in sequence group either way.** -/
theorem seq_assoc (o : Oracle σ) (a b c : PancakeProg) (s : PancakeState σ) :
    PancakeSem o (.seq (.seq a b) c) s = PancakeSem o (.seq a (.seq b c)) s := by
  rw [seq_run, seq_run o a b, seq_run o a (.seq b c)]
  cases PancakeSem o a s with
  | mk r t =>
    cases r with
    | none =>
      simp only
      rw [seq_run]
    | some res => rfl

/-! ## Contracts -/

/-- What a component asks and promises, each obligation by name. It asks that the locals it reads
be bound (`inputs`), that the memory it reads hold what it reads and the memory it writes be
addressable (`memory`), what it needs of the external world's state (`ready`), and for at most
`fuel` of the clock. It promises what it computes (`output`); that of the locals only those
`scratch` names, and of the bytes only those `writes` names, change; that the memory's domain, the
byte order and `@base` stay; what it makes of the external world's state (`world`), by default
nothing; and that it spends at most `fuel`. -/
structure Contract (σ : Type) where
  inputs : PancakeState σ → Prop
  memory : PancakeState σ → Prop
  fuel : Nat
  output : PancakeState σ → PancakeState σ → Prop
  scratch : String → Prop
  writes : Word → Prop
  ready : σ → Prop := fun _ => True
  world : σ → σ → Prop := fun a b => b = a

namespace Contract

/-- What the contract asks of the state a run starts in. -/
def Pre (c : Contract σ) (s : PancakeState σ) : Prop :=
  c.inputs s ∧ c.memory s ∧ c.ready s.ffi ∧ c.fuel ≤ s.clock

/-- What it promises of the state the run ends in, normally. -/
def Post (c : Contract σ) (s t : PancakeState σ) : Prop :=
  c.output s t ∧ Frame c.scratch c.writes s t ∧ c.world s.ffi t.ffi ∧ s.clock ≤ t.clock + c.fuel

/-- `d` after `c`: the locals both read and the memory `c` asks for and what else `needs` names,
what `c` needs of the world, the clock both need, what `c` promises then what `d` does, of the
world too, and the locals and the bytes either changes. -/
def seq (c d : Contract σ) (needs : PancakeState σ → Prop) : Contract σ where
  inputs s := c.inputs s ∧ d.inputs s
  memory s := c.memory s ∧ needs s
  fuel := c.fuel + d.fuel
  output s u := ∃ t, c.Post s t ∧ d.Post t u
  scratch x := c.scratch x ∨ d.scratch x
  writes a := c.writes a ∨ d.writes a
  ready a := c.ready a
  world a b := ∃ m, c.world a m ∧ d.world m b

end Contract

/-- **A component**: code that keeps its contract from every state the contract admits, and a state
it admits. -/
abbrev Component (o : Oracle σ) (c : Contract σ) := Certificate o c.Pre c.Post

/-- **Contracts compose** when what the first promises, from a state the composition admits, gives
the second the locals, the memory and the world it asks for; the clock comes from the first's bound
on what it spends. -/
theorem seq_keeps {o : Oracle σ} {c d : Contract σ} {needs : PancakeState σ → Prop} {p1 p2 : PancakeProg}
    (h1 : RefinesClk o p1 c.Pre c.Post) (h2 : RefinesClk o p2 d.Pre d.Post)
    (link : ∀ s t, (c.seq d needs).Pre s → c.Post s t → d.inputs t ∧ d.memory t ∧ d.ready t.ffi) :
    RefinesClk o (.seq p1 p2) (c.seq d needs).Pre (c.seq d needs).Post := by
  intro s hpre
  obtain ⟨⟨hi, _⟩, ⟨hm, _⟩, hr, hf⟩ := id hpre
  have hf' : c.fuel ≤ s.clock := by simp only [Contract.seq] at hf; omega
  obtain ⟨t, ht, hpost, hct⟩ := h1 s ⟨hi, hm, hr, hf'⟩
  obtain ⟨hdi, hdm, hdr⟩ := link s t hpre hpost
  have hdf : d.fuel ≤ t.clock := by
    have := hpost.2.2.2
    simp only [Contract.seq] at hf
    omega
  obtain ⟨u, hu, hpost2, hcu⟩ := h2 t ⟨hdi, hdm, hdr, hdf⟩
  refine ⟨u, ?_, ⟨⟨t, hpost, hpost2⟩, ?_, ⟨t.ffi, hpost.2.2.1, hpost2.2.2.1⟩, ?_⟩, Nat.le_trans hcu hct⟩
  · rw [seq_run, ht]
    exact hu
  · exact (hpost.2.1.mono (fun _ h => .inl h) (fun _ h => .inl h)).trans
      (hpost2.2.1.mono (fun _ h => .inr h) (fun _ h => .inr h))
  · have h1 := hpost.2.2.2
    have h2 := hpost2.2.2.2
    simp only [Contract.seq]
    omega

/-- **Components compose**, as their contracts do; the composition needs a state of its own. -/
def Component.seq {o : Oracle σ} {c d : Contract σ} {needs : PancakeState σ → Prop}
    (first : Component o c) (second : Component o d)
    (link : ∀ s t, (c.seq d needs).Pre s → c.Post s t → d.inputs t ∧ d.memory t ∧ d.ready t.ffi)
    (witness : ∃ s, (c.seq d needs).Pre s) : Component o (c.seq d needs) :=
  ⟨.seq first.code second.code, seq_keeps first.correct second.correct link, witness⟩

/-! ## A literal stamped at a pointer -/

/-- `k` past the pointer in `p`. -/
def past (p : String) (k : Nat) : PancakeExp := .op .add (.var p) (.const (BitVec.ofNat 64 k))

/-- Each byte of a literal stored at the pointer in `p`, from `k` past it, in order. -/
def stampCode (p : String) (k : Nat) : List (BitVec 8) → PancakeProg
  | [] => .skip
  | [b] => .storeByte (past p k) (.const (BitVec.ofNat 64 b.toNat))
  | b :: bs => .seq (.storeByte (past p k) (.const (BitVec.ofNat 64 b.toNat))) (stampCode p (k + 1) bs)

theorem store_past (o : Oracle σ) {p : String} {P : Word} {s : PancakeState σ} (hp : s.locals p = some P)
    (k : Nat) (b : BitVec 8) (hdom : s.memaddrs (byteAlign (P + BitVec.ofNat 64 k)) = true) :
    PancakeSem o (.storeByte (past p k) (.const (BitVec.ofNat 64 b.toNat))) s
      = (none, { s with memory := putByte s.memory s.be (P + BitVec.ofNat 64 k) b }) := by
  rw [PancakeSem.eq_10]
  simp only [past, eval, hp, ofNat_toNat_setWidth8, memStore_eq _ _ _ _ _ hdom]

/-- **The stamp**: from `k` past the pointer each byte where it goes, every other byte as it was,
nothing else changed. -/
theorem stamp_run (o : Oracle σ) (p : String) (P : Word) :
    ∀ (bs : List (BitVec 8)) (k : Nat) (s : PancakeState σ), s.locals p = some P →
      k + bs.length < 2 ^ 63 →
      (∀ j, j < bs.length → s.memaddrs (byteAlign (P + BitVec.ofNat 64 (k + j))) = true) →
      ∃ m, PancakeSem o (stampCode p k bs) s = (none, { s with memory := m }) ∧
        (∀ j, j < bs.length → memLoadByte m s.memaddrs s.be (P + BitVec.ofNat 64 (k + j)) = some bs[j]!) ∧
        (∀ a, (∀ j, j < bs.length → a ≠ P + BitVec.ofNat 64 (k + j)) →
          memLoadByte m s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a)
  | [], k, s, _, _, _ => ⟨s.memory, by rw [stampCode, PancakeSem.eq_1], fun _ h => absurd h (by simp),
      fun _ _ => rfl⟩
  | [b], k, s, hp, _, hdom => by
    have hd := hdom 0 (by simp)
    simp only [Nat.add_zero] at hd
    refine ⟨_, store_past o hp k b hd, fun j hj => ?_, fun a ha => ?_⟩
    · have : j = 0 := by simp at hj; omega
      subst this
      simp only [Nat.add_zero, List.getElem!_cons_zero]
      exact load_putByte_same _ _ _ _ _ hd
    · exact load_putByte_diff _ _ _ _ _ _ (by simpa using ha 0 (by simp))
  | b :: b2 :: rest, k, s, hp, hlen, hdom => by
    have hd := hdom 0 (by simp)
    simp only [Nat.add_zero] at hd
    let s1 : PancakeState σ := { s with memory := putByte s.memory s.be (P + BitVec.ofNat 64 k) b }
    obtain ⟨m, hrun, hput, hout⟩ := stamp_run o p P (b2 :: rest) (k + 1) s1 hp
      (by simp at hlen ⊢; omega) (fun j hj => by
        have := hdom (j + 1) (by simp at hj ⊢; omega)
        rwa [show k + (j + 1) = k + 1 + j by omega] at this)
    have hne : ∀ j, j < (b2 :: rest).length → P + BitVec.ofNat 64 k ≠ P + BitVec.ofNat 64 (k + 1 + j) :=
      fun j hj => region_addr_inj P k (k + 1 + j) (by omega) (by simp at hj hlen; omega) (by omega)
    refine ⟨m, ?_, fun j hj => ?_, fun a ha => ?_⟩
    · rw [show stampCode p k (b :: b2 :: rest) = .seq (.storeByte (past p k)
          (.const (BitVec.ofNat 64 b.toNat))) (stampCode p (k + 1) (b2 :: rest)) from rfl,
        seq_run, store_past o hp k b hd]
      exact hrun
    · cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem!_cons_zero]
        rw [hout _ hne]
        exact load_putByte_same _ _ _ _ _ hd
      | succ j =>
        have := hput j (by simp at hj ⊢; omega)
        rw [show k + 1 + j = k + (j + 1) by omega] at this
        simpa using this
    · rw [hout a (fun j hj => by
        have := ha (j + 1) (by simp at hj ⊢; omega)
        rwa [show k + (j + 1) = k + 1 + j by omega] at this)]
      exact load_putByte_diff _ _ _ _ _ _ (by simpa using ha 0 (by simp))

/-! ## A copy between two buffers -/

/-- **The copy**: with the pointers and the length in their locals and the index at zero, the loop
lays the source's bytes at the destination, changes only the index and the destination's bytes,
and spends one tick a byte. -/
theorem copy_run (o : Oracle σ) (D S : Word) (val : Nat → BitVec 8) (L : Nat) (hL : L < 2 ^ 63)
    (hdisj : ∀ i j, i < L → j < L → D + BitVec.ofNat 64 i ≠ S + BitVec.ofNat 64 j)
    (s : PancakeState σ) (hdst : s.locals "dst" = some D) (hsrc : s.locals "src" = some S)
    (hi : s.locals "i" = some (BitVec.ofNat 64 0)) (hlen : s.locals "len" = some (BitVec.ofNat 64 L))
    (hsrcR : ∀ j, j < L → memLoadByte s.memory s.memaddrs s.be (S + BitVec.ofNat 64 j) = some (val j))
    (hdstA : ∀ j, j < L → s.memaddrs (byteAlign (D + BitVec.ofNat 64 j)) = true) (hclk : L ≤ s.clock) :
    ∃ t, PancakeSem o ByteCopy.copyByteWhile s = (none, t) ∧
      (∀ j, j < L → memLoadByte t.memory s.memaddrs s.be (D + BitVec.ofNat 64 j) = some (val j)) ∧
      Frame (· = "i") (bytesFrom D L) s t ∧ t.ffi = s.ffi ∧ t.clock + L = s.clock := by
  have hinj : ∀ i j, i < L → j < L → i ≠ j → D + BitVec.ofNat 64 i ≠ D + BitVec.ofNat 64 j :=
    fun i j hi hj hne => region_addr_inj D i j (by omega) (by omega) hne
  obtain ⟨t, ht, ⟨hI, hkeep⟩, hc⟩ := while_inv_cond_exact o (.cmp .less (.var "i") (.var "len"))
    ByteCopy.copyByteBody
    (fun n t => ByteCopy.copyInvB s.memaddrs s.be s.memory D S val L n t ∧ ByteCopy.copyKeeps s t)
    (fun n t hJ => ByteCopy.copyByte_guard s.memaddrs s.be s.memory D S val L hL n t hJ.1)
    (fun n t hJ => by
      obtain ⟨t2, ht2, hI2, hclk2, hk2⟩ :=
        ByteCopy.copyByte_step o s.memaddrs s.be s.memory D S val L hL hdisj hinj n t hJ.1
      exact ⟨t2, ht2, ⟨hI2, ByteCopy.copyKeeps_trans hJ.2 hk2⟩, hclk2⟩)
    L s ⟨⟨0, by omega, rfl, rfl, hdst, hsrc, hi, hlen, hsrcR, hdstA, fun j hj => absurd hj (by omega),
      fun _ _ => rfl⟩, Frame.refl _ _ s, rfl⟩ hclk
  obtain ⟨k, hk0, _, _, _, _, _, _, _, _, hprog, hfr⟩ := hI
  have hkL : k = L := by omega
  subst hkL
  refine ⟨t, ht, hprog, ⟨hkeep.1.memaddrs, hkeep.1.be, hkeep.1.baseAddr, hkeep.1.locals,
    fun a ha => ?_⟩, hkeep.2, hc⟩
  exact hfr a (not_bytesFrom.1 ha)

/-! ## The two contracts -/

/-- The stamp's: the pointer in `src` at `P`, its bytes addressable; it lays `bs` there and changes
nothing else. -/
def stampContract (P : Word) (bs : List (BitVec 8)) : Contract σ where
  inputs s := s.locals "src" = some P
  memory s := ∀ j, j < bs.length → s.memaddrs (byteAlign (P + BitVec.ofNat 64 j)) = true
  fuel := 0
  output s t := memBytesAt t.memory s.memaddrs s.be P bs
  scratch _ := False
  writes := bytesFrom P bs.length

theorem stamp_keeps (o : Oracle σ) (P : Word) (bs : List (BitVec 8)) (hlen : bs.length < 2 ^ 63) :
    RefinesClk o (stampCode "src" 0 bs) (stampContract P bs).Pre (stampContract P bs).Post := by
  intro s ⟨hp, hm, _, _⟩
  obtain ⟨m, hrun, hput, hout⟩ := stamp_run o "src" P bs 0 s hp (by omega)
    (fun j hj => by simpa using hm j hj)
  refine ⟨_, hrun, ⟨fun i hi => by simpa using hput i hi, ⟨rfl, rfl, rfl, fun _ _ => rfl,
    fun a ha => hout a (fun j hj => by simpa using (not_bytesFrom.1 ha) j hj)⟩, rfl, by simp⟩,
    Nat.le_refl _⟩

/-- The copy's: the pointers in `dst` and `src` at `D` and `S`, the index at zero and the length
`L` in `len`; the source's bytes `val`, the destination's addressable; `L` ticks. It lays `val` at
the destination and changes only the index and the destination's bytes. -/
def copyContract (D S : Word) (val : Nat → BitVec 8) (L : Nat) : Contract σ where
  inputs s := s.locals "dst" = some D ∧ s.locals "src" = some S ∧
    s.locals "i" = some (BitVec.ofNat 64 0) ∧ s.locals "len" = some (BitVec.ofNat 64 L)
  memory s := (∀ j, j < L → memLoadByte s.memory s.memaddrs s.be (S + BitVec.ofNat 64 j) = some (val j)) ∧
    ∀ j, j < L → s.memaddrs (byteAlign (D + BitVec.ofNat 64 j)) = true
  fuel := L
  output s t := ∀ j, j < L → memLoadByte t.memory s.memaddrs s.be (D + BitVec.ofNat 64 j) = some (val j)
  scratch x := x = "i"
  writes := bytesFrom D L

theorem copy_keeps (o : Oracle σ) (D S : Word) (val : Nat → BitVec 8) (L : Nat) (hL : L < 2 ^ 63)
    (hdisj : ∀ i j, i < L → j < L → D + BitVec.ofNat 64 i ≠ S + BitVec.ofNat 64 j) :
    RefinesClk o ByteCopy.copyByteWhile (copyContract D S val L).Pre (copyContract D S val L).Post := by
  intro s ⟨⟨hd, hs, hi, hl⟩, ⟨hr, ha⟩, _, hc⟩
  obtain ⟨t, ht, hput, hfr, hffi, hclk⟩ := copy_run o D S val L hL hdisj s hd hs hi hl hr ha hc
  exact ⟨t, ht, ⟨hput, hfr, hffi, by simp only [copyContract]; omega⟩, by omega⟩

/-- The destination's bytes addressable: what the stamp's contract does not ask and the copy's does. -/
def dstRoom (D : Word) (L : Nat) (s : PancakeState σ) : Prop :=
  ∀ j, j < L → s.memaddrs (byteAlign (D + BitVec.ofNat 64 j)) = true

/-- Stamp `bs` at `P`, then copy it to `D`. -/
abbrev stampThenCopy (P D : Word) (bs : List (BitVec 8)) : Contract σ :=
  (stampContract P bs).seq (copyContract D P (fun j => bs[j]!) bs.length) (dstRoom D bs.length)

/-- What the stamp promises gives the copy what it asks. -/
theorem stamp_gives_copy (P D : Word) (bs : List (BitVec 8)) :
    ∀ (s t : PancakeState σ), (stampThenCopy P D bs).Pre s → (stampContract P bs).Post s t →
      (copyContract D P (fun j => bs[j]!) bs.length).inputs t ∧
        (copyContract D P (fun j => bs[j]!) bs.length).memory t ∧
        (copyContract D P (fun j => bs[j]!) bs.length).ready t.ffi := by
  intro s t ⟨⟨_, hd, hs, hi, hl⟩, ⟨_, hroom⟩, _⟩ ⟨hout, hfr, _, _⟩
  have hloc : ∀ x, t.locals x = s.locals x := fun x => hfr.locals x id
  refine ⟨⟨by rw [hloc]; exact hd, by rw [hloc]; exact hs, by rw [hloc]; exact hi, by rw [hloc]; exact hl⟩,
    ⟨fun j hj => ?_, fun j hj => ?_⟩, trivial⟩
  · rw [hfr.memaddrs, hfr.be]
    exact hout j hj
  · rw [hfr.memaddrs]
    exact hroom j hj

theorem stampThenCopy_keeps (o : Oracle σ) (P D : Word) (bs : List (BitVec 8)) (hlen : bs.length < 2 ^ 63)
    (hdisj : ∀ i j, i < bs.length → j < bs.length → D + BitVec.ofNat 64 i ≠ P + BitVec.ofNat 64 j) :
    RefinesClk o (.seq (stampCode "src" 0 bs) ByteCopy.copyByteWhile) (stampThenCopy P D bs).Pre
      (stampThenCopy P D bs).Post :=
  seq_keeps (stamp_keeps o P bs hlen) (copy_keeps o D P _ bs.length hlen hdisj) (stamp_gives_copy P D bs)

/-! ## The exported function that stamps and copies -/

/-- The stores of `stampCode` with `rest` after the last, as the lowering nests them. -/
def stampThen (p : String) (k : Nat) : List (BitVec 8) → PancakeProg → PancakeProg
  | [], rest => rest
  | b :: bs, rest => .seq (.storeByte (past p k) (.const (BitVec.ofNat 64 b.toNat))) (stampThen p (k + 1) bs rest)

/-- Nested so, the stores run as the stamp and then `rest`. -/
theorem stampThen_run (o : Oracle σ) (p : String) (rest : PancakeProg) :
    ∀ (bs : List (BitVec 8)) (k : Nat) (s : PancakeState σ), bs ≠ [] →
      PancakeSem o (stampThen p k bs rest) s = PancakeSem o (.seq (stampCode p k bs) rest) s
  | [], _, _, h => absurd rfl h
  | [_], _, _, _ => rfl
  | b :: b2 :: bs, k, s, _ => by
    rw [show stampCode p k (b :: b2 :: bs) = .seq (.storeByte (past p k)
        (.const (BitVec.ofNat 64 b.toNat))) (stampCode p (k + 1) (b2 :: bs)) from rfl, seq_assoc]
    show PancakeSem o (.seq _ (stampThen p (k + 1) (b2 :: bs) rest)) s = _
    rw [seq_run, seq_run o (.storeByte _ _)]
    cases PancakeSem o (.storeByte (past p k) (.const (BitVec.ofNat 64 b.toNat))) s with
    | mk r t =>
      cases r with
      | none => exact stampThen_run o p rest (b2 :: bs) (k + 1) t (List.cons_ne_nil _ _)
      | some res => rfl

/-- The function lowers to its declarations around the stamp and then the copy and the return. -/
theorem stampCopy_lowers :
    lower Kernels.stampCopy = some (.dec "i" (.const (BitVec.ofNat 64 0)) (.dec "len" (.const (BitVec.ofNat 64 7))
      (stampThen "src" 0 Kernels.stampLiteral (.seq ByteCopy.copyByteWhile (.ret (.var "len")))))) := rfl

/-- **The exported function stamps the literal at `src` and copies it to `dst`**, from any state with
the two pointers in their locals, seven bytes addressable at each, apart, and seven ticks: it
returns 7 with the literal at both, every other byte, the memory's domain, the byte order, `@base`
and the external world's state as they were. -/
theorem stampCopy_run (o : Oracle σ) (P D : Word) (s : PancakeState σ)
    (hsrc : s.locals "src" = some P) (hdst : s.locals "dst" = some D)
    (hP : ∀ j, j < 7 → s.memaddrs (byteAlign (P + BitVec.ofNat 64 j)) = true)
    (hD : ∀ j, j < 7 → s.memaddrs (byteAlign (D + BitVec.ofNat 64 j)) = true)
    (hdisj : ∀ i j, i < 7 → j < 7 → D + BitVec.ofNat 64 i ≠ P + BitVec.ofNat 64 j) (hclk : 7 ≤ s.clock) :
    ∃ prog t, lower Kernels.stampCopy = some prog ∧ PancakeSem o prog s = (some (.return_ 7), t) ∧
      memBytesAt t.memory s.memaddrs s.be D Kernels.stampLiteral ∧
      memBytesAt t.memory s.memaddrs s.be P Kernels.stampLiteral ∧
      (∀ a, ¬ bytesFrom P 7 a → ¬ bytesFrom D 7 a →
        memLoadByte t.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a) ∧
      t.memaddrs = s.memaddrs ∧ t.be = s.be ∧ t.baseAddr = s.baseAddr ∧ t.ffi = s.ffi := by
  let s1 : PancakeState σ := { s with locals := setLocal s.locals "i" (BitVec.ofNat 64 0) }
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "len" (BitVec.ofNat 64 7) }
  have hpre : (stampThenCopy P D stampLiteral).Pre s2 := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨hP, hD⟩, trivial, hclk⟩
    · show setLocal (setLocal s.locals "i" (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 7) "src" = some P
      simp [setLocal, hsrc]
    · show setLocal (setLocal s.locals "i" (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 7) "dst" = some D
      simp [setLocal, hdst]
    · show setLocal (setLocal s.locals "i" (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 7) "src" = some P
      simp [setLocal, hsrc]
    · show setLocal (setLocal s.locals "i" (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 7) "i" = some _
      simp [setLocal]
    · show setLocal (setLocal s.locals "i" (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 7) "len" = some _
      simp [setLocal]
      rfl
  obtain ⟨u, hu, hpost, _⟩ :=
    stampThenCopy_keeps o P D stampLiteral (by decide) (fun i j hi hj => hdisj i j hi hj) s2 hpre
  obtain ⟨⟨t', hc1, hc2⟩, hfr, hffi, _⟩ := hpost
  obtain ⟨hst, hfr1, _, _⟩ := hc1
  obtain ⟨hcp, hfr2, _, _⟩ := hc2
  have hlen : u.locals "len" = some (BitVec.ofNat 64 7) := by
    rw [hfr.locals "len" (by simp [Contract.seq, stampContract, copyContract])]
    simp [s2, setLocal]
  have hinner : PancakeSem o (stampThen "src" 0 Kernels.stampLiteral (.seq ByteCopy.copyByteWhile (.ret (.var "len")))) s2
      = (some (.return_ 7), emptyLocals u) := by
    rw [stampThen_run o _ _ _ _ _ (by decide), ← seq_assoc, seq_run, hu]
    show PancakeSem o (.ret (.var "len")) u = _
    rw [PancakeSem.eq_9]
    simp only [eval, hlen]
    rfl
  have hrun := Region.sem_dec (oracle := o) (v := "i") (e := .const (BitVec.ofNat 64 0)) (s := s) rfl
    (Region.sem_dec (oracle := o) (v := "len") (e := .const (BitVec.ofNat 64 7)) (s := s1) rfl hinner)
  refine ⟨_, _, stampCopy_lowers, hrun, ?_, ?_, fun a hp hd => ?_, hfr.memaddrs, hfr.be, hfr.baseAddr, ?_⟩
  · intro j hj
    have := hcp j hj
    rw [hfr1.memaddrs, hfr1.be] at this
    exact this
  · intro j hj
    have hout := hfr2.outside (P + BitVec.ofNat 64 j) (fun ⟨i, hi, he⟩ => hdisj i j hi hj he.symm)
    rw [hfr1.memaddrs, hfr1.be] at hout
    show memLoadByte u.memory s.memaddrs s.be _ = _
    rw [hout]
    exact hst j hj
  · exact hfr.outside a (fun h => h.elim hp hd)
  · obtain ⟨_, h1, h2⟩ := hffi
    exact h2.trans h1

/-! ## The premises hold -/

/-- The memory's domain of the witnesses, in the shape the CakeML theorem gives it: the aligned words
from 64 below 192. -/
def window (a : Word) : Bool := 64 ≤ a.toNat && a.toNat < 192 && a.toNat % 8 == 0

/-- The state the exported function is entered in: the source at 64 and the destination at 128 in
its parameters, and seven ticks. -/
def entryState : PancakeState Unit :=
  { locals := fun x => if x = "src" then some 64 else if x = "dst" then some 128 else none,
    memory := fun _ => 0, memaddrs := window, be := false, clock := 7, ffi := (), baseAddr := 0 }

/-- …and as the composition runs from it, the index at zero and the length 7 declared. -/
def stampState : PancakeState Unit :=
  { entryState with locals := fun x => if x = "src" then some 64 else if x = "dst" then some 128
      else if x = "i" then some 0 else if x = "len" then some 7 else none }

/-- …and with the literal already at the source, for the copy alone. -/
def stampedState : PancakeState Unit :=
  { stampState with memory := fun a => if a == 64 then 0x00736e6f67617264 else 0 }

theorem src_room : ∀ j, j < 7 → stampState.memaddrs (byteAlign (64 + BitVec.ofNat 64 j)) = true := by
  decide

theorem dst_room : ∀ j, j < 7 → stampState.memaddrs (byteAlign (128 + BitVec.ofNat 64 j)) = true := by
  decide

theorem src_stamped : ∀ j, j < 7 →
    memLoadByte stampedState.memory stampedState.memaddrs stampedState.be (64 + BitVec.ofNat 64 j)
      = some stampLiteral[j]! := by
  decide

theorem buffers_apart : ∀ i, i < 7 → ∀ j, j < 7 → (128 : Word) + BitVec.ofNat 64 i ≠ 64 + BitVec.ofNat 64 j := by
  decide

theorem literal_short : stampLiteral.length < 2 ^ 63 := by decide

/-- The stamp, with a state it admits. -/
def stampComponent : Component (Oracle.idle (σ := Unit)) (stampContract 64 stampLiteral) :=
  ⟨stampCode "src" 0 stampLiteral, stamp_keeps _ _ _ literal_short,
    ⟨stampState, rfl, src_room, trivial, Nat.zero_le _⟩⟩

/-- The copy, with a state it admits. -/
def copyComponent : Component (Oracle.idle (σ := Unit)) (copyContract 128 64 (fun j => stampLiteral[j]!) 7) :=
  ⟨ByteCopy.copyByteWhile, copy_keeps _ _ _ _ _ (by decide) (fun i j hi hj => buffers_apart i hi j hj),
    ⟨stampedState, ⟨rfl, rfl, rfl, rfl⟩, ⟨src_stamped, dst_room⟩, trivial, Nat.le_refl _⟩⟩

/-- **Their composition**, with a state it admits: the stamp's state, both buffers addressable. -/
def stampThenCopyComponent : Component (Oracle.idle (σ := Unit)) (stampThenCopy 64 128 stampLiteral) :=
  Component.seq stampComponent copyComponent (stamp_gives_copy 64 128 stampLiteral)
    ⟨stampState, ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨src_room, dst_room⟩, trivial, Nat.le_refl _⟩

/-- What the composition promises holds of a run from its state: `Post`, which `seq_keeps`'s link
assumes, is met. -/
theorem post_witness : ∃ t, (stampThenCopy 64 128 stampLiteral).Post stampState t := by
  obtain ⟨t, _, hpost, _⟩ := stampThenCopyComponent.correct stampState
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨src_room, dst_room⟩, trivial, Nat.le_refl _⟩
  exact ⟨t, hpost⟩

/-- **`stampCopy_run`'s premises hold**: entered with only its parameters, the exported function
returns 7 with the literal at both buffers. -/
theorem stampCopy_witness :
    ∃ prog t, lower Kernels.stampCopy = some prog ∧
      PancakeSem Oracle.idle prog entryState = (some (.return_ 7), t) ∧
      memBytesAt t.memory window false 128 stampLiteral ∧ memBytesAt t.memory window false 64 stampLiteral := by
  obtain ⟨prog, t, hl, hr, hd, hs, _⟩ := stampCopy_run Oracle.idle 64 128 entryState rfl rfl src_room dst_room
    (fun i j hi hj => buffers_apart i hi j hj) (Nat.le_refl _)
  exact ⟨prog, t, hl, hr, hd, hs⟩

/-! ## A component that calls out -/

/-- The call of `name` with the configuration and the array the locals `c`, `cl`, `a`, `al` give. -/
def callCode (name : String) : PancakeProg := .extCall name (.var "c") (.var "cl") (.var "a") (.var "al")

/-- An external call's: the four locals at `C`, `CL`, `A`, `AL`, the configuration's bytes `conf`
and the array's `arr` there, and a world that answers the call. It lays the answer at the array,
changes no local and no other byte, and makes of the world what the answer says. -/
def callContract (o : Oracle σ) (name : String) (C CL A AL : Word) (conf arr : List (BitVec 8)) :
    Contract σ where
  inputs s := s.locals "c" = some C ∧ s.locals "cl" = some CL ∧ s.locals "a" = some A ∧
    s.locals "al" = some AL
  memory s := readByteArray s.memory s.memaddrs s.be C CL.toNat = some conf ∧
    readByteArray s.memory s.memaddrs s.be A AL.toNat = some arr
  fuel := 0
  output s t := ∃ bytes, callFFI o s.ffi name conf arr = .ret t.ffi bytes ∧
    t.memory = writeByteArray s.memaddrs s.be A bytes s.memory
  scratch _ := False
  writes := bytesFrom A arr.length
  ready a := ∃ w bytes, callFFI o a name conf arr = .ret w bytes
  world a b := ∃ bytes, callFFI o a name conf arr = .ret b bytes

theorem call_keeps (o : Oracle σ) (name : String) (C CL A AL : Word) (conf arr : List (BitVec 8)) :
    RefinesClk o (callCode name) (callContract o name C CL A AL conf arr).Pre
      (callContract o name C CL A AL conf arr).Post := by
  intro s ⟨⟨hc, hcl, ha, hal⟩, ⟨hconf, harr⟩, ⟨w, bytes, hcall⟩, _⟩
  have hrun : PancakeSem o (callCode name) s =
      (none, { s with memory := writeByteArray s.memaddrs s.be A bytes s.memory, ffi := w }) := by
    rw [callCode, PancakeSem.eq_5]
    simp only [eval, hc, hcl, ha, hal, hconf, harr, hcall]
  obtain ⟨hfr, hclk⟩ := extCall_keeps o s name (cptr := .var "c") (clen := .var "cl") (aptr := .var "a")
    (alen := .var "al") (by simp only [eval, hc]) (by simp only [eval, hcl]) (by simp only [eval, ha])
    (by simp only [eval, hal]) hconf harr hrun
  exact ⟨_, hrun, ⟨⟨bytes, hcall, rfl⟩, hfr, ⟨bytes, hcall⟩, by simp only [callContract]; omega⟩,
    by simp only; omega⟩

/-- A world that counts the calls made to it and answers each with the bytes it was given. -/
def counting : Oracle Nat := ⟨fun n _ _ array => .ret (n + 1) array⟩

/-- A state the call admits: a byte of configuration at 64, an array of two at 128, no call made. -/
def callState : PancakeState Nat :=
  { locals := fun x => if x = "c" then some 64 else if x = "cl" then some 1 else if x = "a" then some 128
      else if x = "al" then some 2 else none,
    memory := fun _ => 0, memaddrs := window, be := false, clock := 0, ffi := 0, baseAddr := 0 }

/-- **The call**, with a state it admits. -/
def callComponent : Component counting (callContract counting "dn_count" 64 1 128 2 [0] [0, 0]) :=
  ⟨callCode "dn_count", call_keeps _ _ _ _ _ _ _ _,
    ⟨callState, ⟨rfl, rfl, rfl, rfl⟩, ⟨by decide, by decide⟩, ⟨1, [0, 0], rfl⟩, Nat.le_refl _⟩⟩

/-- **The world moves as the contract says**: from its state the call ends with one call counted. -/
theorem call_witness : ∃ t, (callContract counting "dn_count" 64 1 128 2 [0] [0, 0]).Post callState t ∧
    t.ffi = 1 := by
  obtain ⟨t, _, hpost, _⟩ := callComponent.correct callState
    ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨by decide, by decide⟩, ⟨1, [0, 0], rfl⟩, Nat.le_refl _⟩
  obtain ⟨_, hw⟩ := hpost.2.2.1
  refine ⟨t, hpost, ?_⟩
  have h : callFFI counting 0 "dn_count" [0] [0, 0] = .ret 1 [0, 0] := rfl
  rw [show callState.ffi = 0 from rfl, h] at hw
  injection hw with h1
  exact h1.symm

end DN.Compiler.Components
