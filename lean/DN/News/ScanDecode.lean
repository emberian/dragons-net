-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ScanFrame
import DN.News.ScanRecord

/-!
# DN.News.ScanDecode

If it goes on, `ScanProg.decode` gives `ScanRun.scanCommit`'s verdict and the commit's fields in the area
(`decode_frag`, `decOut_commit`). Area offsets stay literals, 24 a group's slot and 13 a frame's header. `omega` needs
`24 * g` linear and `rw` the lowered constants; `nums` names them.
-/

namespace DN.News.ScanRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News DN.News.Journal DN.News.ScanProg
open DN.News.FramerCode (bw bw_ne0 bw_eq0 eval_lt eval_eq eval_and cmp_bw)
open DN.Compiler.WpBytes (eval_addc eval_add eval_load)

variable {σ : Type}

/-! ## What the reading of a record reads and writes -/

/-- The area's words a record's fields are written to: from its type to the key. -/
def FieldW (A : Word) (a : Word) : Prop := ∃ x, sType ≤ x ∧ x < sKey ∧ a = at_ A x

/-- The locals the reading of a commit sets. -/
def decNames : List String :=
  ["jok", "ji", "jseq", "jml", "jgc", "jgi", "jnl", "jgp", "jnum", "jhs", "jfs", "jcrc", "ja", "jbb", "jga", "jgb",
   "jla", "jna", "jnb", "jeq", "jx"]

/-- What `decode` reads: the area at `A`, the payload `pl` of the frame `o'` octets into the window. -/
structure DecIn (A : Word) (o' : Nat) (pl : Bytes) (s : PancakeState σ) : Prop where
  hA : A.toNat % 8 = 0
  dom : Dom A s.memaddrs
  sp : s.locals "jsc" = some A
  jz : s.locals "jz" = some 0
  jw : s.locals "jw" = some (at_ A sWindow)
  jo : s.locals "jo" = some (BitVec.ofNat 64 o')
  jpp : s.locals "jpp" = some (at_ A (sWindow + o' + 13))
  jpl : s.locals "jpl" = some (BitVec.ofNat 64 pl.length)
  payload : ∀ i (h : i < pl.length),
    memLoadByte s.memory s.memaddrs s.be (at_ A (sWindow + o' + 13 + i)) = some pl[i]
  room : o' + maxFrame ≤ windowRoom
  len : pl.length ≤ maxPayload
  bound : ∀ y ∈ decNames, ∃ v, s.locals y = some v
  jrec : ∃ v, s.locals "jrec" = some v

theorem not_field {A : Word} (hA : A.toNat % 8 = 0) {x : Nat} (hx : x < sType ∨ sKey ≤ x) (h64 : x < 2 ^ 63) :
    ¬ FieldW A (byteAlign (at_ A x)) := by
  rintro ⟨y, h1, h2, e⟩
  rw [at_, byteAlign_base hA, at_] at e
  have := nums
  simp only [sType] at h1 hx
  exact region_addr_inj A _ _ (by omega) (by omega) (by omega) e

/-- A local that holds a small number. -/
def Small (u : PancakeState σ) (x : String) : Prop := ∃ n, u.locals x = some (BitVec.ofNat 64 n) ∧ n ≤ maxPayload

theorem ofNat_mul24 (g : Nat) : BitVec.ofNat 64 g * BitVec.ofNat 64 24 = BitVec.ofNat 64 (24 * g) := by
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

section Decode

variable {A : Word} {o' : Nat} {pl : Bytes} {s0 : PancakeState σ}

/-- The reading so far: its frame from `s0`, `ji` small, and `jok` the verdict `b`. -/
def DAt (A : Word) (s0 : PancakeState σ) (b : Bool) (u : PancakeState σ) : Prop :=
  Kept decNames (FieldW A) s0 u ∧ Small u "ji" ∧ u.locals "jok" = some (bw b)

theorem dat_set {b : Bool} {u : PancakeState σ} (h : DAt A s0 b u) {x : String} (hx : x ∈ decNames)
    (h1 : x ≠ "ji") (h2 : x ≠ "jok") (v : Value) : DAt A s0 b (setL u x v) :=
  ⟨kept_set h.1 hx v, by obtain ⟨n, hn, hl⟩ := h.2.1; exact ⟨n, by simp [setL, setLocal, Ne.symm h1, hn], hl⟩,
    by simp [setL, setLocal, Ne.symm h2, h.2.2]⟩

/-- The Message-ID's length, the octet after the sequence number. -/
def mlOf (pl : Bytes) : Nat := (pl.getD 8 0).toNat
/-- The count of groups, the octet after the Message-ID. -/
def gcOf (pl : Bytes) : Nat := (pl.getD (9 + mlOf pl) 0).toNat

theorem dat_bound (h : DecIn A o' pl s0) {b : Bool} {u : PancakeState σ} (hu : DAt A s0 b u) {y : String}
    (hy : y ∈ decNames) : ∃ v, u.locals y = some v :=
  kept_has hu.1 (h.bound y hy)

theorem dat_local {b : Bool} {u : PancakeState σ} (hu : DAt A s0 b u) {y : String} (hy : y ∉ decNames) :
    u.locals y = s0.locals y := hu.1.locals y hy

/-- The payload's length, from any state the reading keeps. -/
theorem dat_jpl (h : DecIn A o' pl s0) {b : Bool} {u : PancakeState σ} (hu : DAt A s0 b u) :
    eval u (.var "jpl") = some (BitVec.ofNat 64 pl.length) := by
  simp only [eval]; rw [dat_local hu (by decide)]; exact h.jpl

/-- A word of the area, addressable where the reading keeps the memory's domain. -/
theorem dom_at (h : DecIn A o' pl s0) {u : PancakeState σ} (hd : u.memaddrs = s0.memaddrs) {x : Nat}
    (hx8 : x % 8 = 0) (hx : x < ScanProg.size) : u.memaddrs (at_ A x) = true := by
  rw [hd, at_, ← byteAlign_of_aligned h.hA hx8]; exact h.dom x hx

/-- The payload's octets, read from any state the reading keeps. -/
theorem dat_byte (h : DecIn A o' pl s0) {b : Bool} {u : PancakeState σ} (hu : DAt A s0 b u) (i : Nat)
    (hi : i < pl.length) :
    memLoadByte u.memory u.memaddrs u.be (at_ A (sWindow + o' + 13) + BitVec.ofNat 64 i) = some pl[i] := by
  have := nums; have := h.room; have := h.len
  rw [at_add, kept_load hu.1 (not_field h.hA (Or.inr (by omega)) (by omega))]
  exact h.payload i hi

/-- **The commit's sequence number.** -/
theorem decA_frag (o : Oracle σ) (h : DecIn A o' pl s0) :
    Frag o ScanProg.seqPart (Like s0)
      (fun u => DAt A s0 (decide (8 ≤ pl.length)) u ∧ u.locals "ji" = some (BitVec.ofNat 64 8) ∧
        (8 ≤ pl.length → u.locals "jseq" = some (BitVec.ofNat 64 (readLE (pl.take 8))))) := by
  have hn := nums
  have hl := h.len
  have kz : ∀ u, Kept decNames (FieldW A) s0 u → u.locals "jz" = some 0 := fun u hu =>
    (hu.locals "jz" (by decide)).trans h.jz
  have kb : ∀ u, Kept decNames (FieldW A) s0 u → ∀ y ∈ decNames, ∃ v, u.locals y = some v := fun u hu y hy =>
    kept_has hu (h.bound y hy)
  let Q (u : PancakeState σ) : Prop := DAt A s0 (decide (8 ≤ pl.length)) u ∧ u.locals "ji" = some (BitVec.ofNat 64 8) ∧
    (8 ≤ pl.length → u.locals "jseq" = some (BitVec.ofNat 64 (readLE (pl.take 8))))
  have hQc : Safe.ClockFree Q := fun _ _ ⟨⟨h1, h2, h3⟩, h4, h5⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4, h5⟩
  let M (u : PancakeState σ) : Prop := Kept decNames (FieldW A) s0 u ∧ u.locals "ji" = some (BitVec.ofNat 64 8) ∧
    u.locals "jok" = some 1
  have hMc : Safe.ClockFree M := fun _ _ ⟨h1, h2, h3⟩ => ⟨{ h1 with }, h2, h3⟩
  have f1 : Frag o [.assign "jok" (lit 1), .assign "ji" (lit 8)] (Like s0) M :=
    frag_append (xs := [_]) (set_frag o (E := .op .add (.var "jz") (.const 1)) rfl
      (P' := fun u => Kept decNames (FieldW A) s0 u ∧ u.locals "jok" = some 1)
      (fun _ _ ⟨h1, h2⟩ => ⟨{ h1 with }, h2⟩) fun u hu => ⟨1, by
        simp [eval, kz u (kept_of_like hu)], kb u (kept_of_like hu) "jok" (by decide),
        kept_set (kept_of_like hu) (by decide) _, by simp [setL, setLocal]⟩)
      (set_frag o (E := .op .add (.var "jz") (.const 8)) rfl hMc fun u hu => ⟨8, by simp [eval, kz u hu.1],
        kb u hu.1 "ji" (by decide), kept_set hu.1 (by decide) _, by simp [setL, setLocal],
        by simp [setL, setLocal, hu.2]⟩)
  have hjpl : ∀ u, M u → eval u (.var "jpl") = some (BitVec.ofNat 64 pl.length) := fun u hu => by
    simp only [eval]; rw [hu.1.locals "jpl" (by decide)]; exact h.jpl
  refine frag_append (xs := [_, _]) f1 (frag_ite o (C := .cmp .less (.var "jpl") (.const (BitVec.ofNat 64 8))) rfl hQc
    (fun u hu => ⟨_, eval_lt (by omega) (by decide) (hjpl u hu) rfl⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl))
  · refine set_frag o (E := .op .add (.var "jz") (.const 0)) rfl hQc fun u ⟨hu, hne⟩ => ?_
    rw [eval_lt (by omega) (by decide) (hjpl u hu) rfl] at hne
    have h8 := bw_ne0 hne
    simp only [decide_eq_true_eq] at h8
    refine ⟨0, by simp [eval, kz u hu.1], kb u hu.1 "jok" (by decide), ⟨kept_set hu.1 (by decide) _,
      ⟨8, by simp [setL, setLocal, hu.2], by omega⟩, ?_⟩, by simp [setL, setLocal, hu.2], fun e => by omega⟩
    simp [setL, setLocal, bw, show ¬ 8 ≤ pl.length by omega]
  · refine frag_each o (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨hs, h0⟩ => ?_
    rw [eval_lt (by omega) (by decide) (hjpl s hs) rfl] at h0
    have h8 := bw_eq0 h0
    simp only [decide_eq_false_iff_not, Nat.not_lt] at h8
    have e := leS_frag o (x := "jseq") (p := Syntax.v "jpp") (P := .var "jpp") rfl (s := s)
      (a := at_ A (sWindow + o' + 13)) (bs := pl.take 8) (by simp; omega)
      (fun w => by simp [eval, setL, setLocal, (hs.1.locals "jpp" (by decide)).trans h.jpp])
      (fun i hi => by
        have hi' : i < pl.length := by simp at hi; omega
        rw [at_add, kept_load hs.1 (not_field h.hA (Or.inr (by have := h.room; omega)) (by have := h.room; omega)),
          ← at_add, show at_ A (sWindow + o' + 13) + BitVec.ofNat 64 i = at_ A (sWindow + o' + 13 + i) from
            at_add _ _ _, h.payload i hi']
        simp [List.getElem_take])
      (kb s hs.1 "jseq" (by decide))
    rw [show (pl.take 8).length = 8 by simp; omega] at e
    refine frag_conseq e (fun _ h => h) fun u hu => ?_
    rw [like_eq hu]
    refine hQc _ _ ⟨⟨kept_set hs.1 (by decide) _, ⟨8, by simp [setL, setLocal, hs.2], by omega⟩, ?_⟩,
      by simp [setL, setLocal, hs.2], fun _ => by simp [setL, setLocal]⟩
    simp [setL, setLocal, bw, h8, hs.2.2]

theorem dat_jok {b c : Bool} {u : PancakeState σ} (h : DAt A s0 b u) (e : b = c) : DAt A s0 c u := e ▸ h

/-- `jok` given zero: a verdict that does not hold. -/
theorem dat_fail {b : Bool} {u : PancakeState σ} (hu : DAt A s0 b u) :
    DAt A s0 false (setL u "jok" (BitVec.ofNat 64 0)) :=
  ⟨kept_set hu.1 (by decide) _, by obtain ⟨n, hn, hl⟩ := hu.2.1; exact ⟨n, by simp [setL, setLocal, hn], hl⟩,
    by simp [setL, setLocal, bw]⟩

theorem fail_frag (o : Oracle σ) (h : DecIn A o' pl s0) {P Q : Assn σ} (hQ : Safe.ClockFree Q)
    (hP : ∀ u, P u → ∃ b, DAt A s0 b u ∧ Q (setL u "jok" (BitVec.ofNat 64 0))) :
    Frag o [.assign "jok" (lit 0)] P Q :=
  set_frag o (E := .op .add (.var "jz") (.const 0)) rfl hQ fun u hu => by
    obtain ⟨b, hb, hq⟩ := hP u hu
    exact ⟨_, by simp [eval, (hb.1.locals "jz" (by decide)).trans h.jz], ⟨_, hb.2.2⟩, hq⟩

/-- What is known once the Message-ID is placed. -/
def BFacts (A : Word) (o' : Nat) (pl : Bytes) (u : PancakeState σ) : Prop :=
  u.locals "jml" = some (BitVec.ofNat 64 (mlOf pl)) ∧
    u.locals "jseq" = some (BitVec.ofNat 64 (readLE (pl.take 8))) ∧
    u.memory (at_ A sIdAt) = BitVec.ofNat 64 (o' + 13 + 9) ∧ u.memory (at_ A sIdLen) = BitVec.ofNat 64 (mlOf pl)

theorem BFacts.jseq {u : PancakeState σ} (hb : BFacts A o' pl u) :
    u.locals "jseq" = some (BitVec.ofNat 64 (readLE (pl.take 8))) := hb.2.1
theorem BFacts.idAt {u : PancakeState σ} (hb : BFacts A o' pl u) :
    u.memory (at_ A sIdAt) = BitVec.ofNat 64 (o' + 13 + 9) := hb.2.2.1
theorem BFacts.idLen {u : PancakeState σ} (hb : BFacts A o' pl u) :
    u.memory (at_ A sIdLen) = BitVec.ofNat 64 (mlOf pl) := hb.2.2.2

/-- The facts kept where a local but `jml` and `jseq` is set. -/
theorem bfacts_set {u : PancakeState σ} (hb : BFacts A o' pl u) {x : String} (h1 : x ≠ "jml") (h2 : x ≠ "jseq")
    (v : Value) : BFacts A o' pl (setL u x v) :=
  ⟨by simp [setL, setLocal, Ne.symm h1, hb.1], by simp [setL, setLocal, Ne.symm h2, hb.2.1], hb.2.2.1, hb.2.2.2⟩

/-- **The commit's Message-ID**: its length, and where it lies. -/
theorem decB_frag (o : Oracle σ) (h : DecIn A o' pl s0) :
    Frag o ScanProg.idPart
      (fun u => DAt A s0 (decide (8 ≤ pl.length)) u ∧ u.locals "ji" = some (BitVec.ofNat 64 8) ∧
        (8 ≤ pl.length → u.locals "jseq" = some (BitVec.ofNat 64 (readLE (pl.take 8)))))
      (fun u => DAt A s0 (decide (9 + mlOf pl ≤ pl.length)) u ∧ (9 + mlOf pl ≤ pl.length →
        u.locals "ji" = some (BitVec.ofNat 64 (9 + mlOf pl)) ∧ BFacts A o' pl u)) := by
  have hn := nums
  have hl := h.len
  let Q (u : PancakeState σ) : Prop := DAt A s0 (decide (9 + mlOf pl ≤ pl.length)) u ∧ (9 + mlOf pl ≤ pl.length →
    u.locals "ji" = some (BitVec.ofNat 64 (9 + mlOf pl)) ∧ BFacts A o' pl u)
  have hQc : Safe.ClockFree Q := fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩
  refine flagIf_frag o (lowK_any _ (k := .skip) (c := _) rfl) rfl hQc (fun u hu => hu.1.2.2) ?_ ?_
  · intro hb
    simp only [decide_eq_true_eq] at hb
    refine frag_ite o (C := .cmp .less (.var "jpl") (.op .add (.var "ji") (.const 1))) rfl hQc
      (fun u hu => ⟨_, eval_lt (x := pl.length) (y := 9) (by omega) (by decide) (dat_jpl h hu.1)
        (by simp only [eval, hu.2.1]; rfl)⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
    · -- no length octet
      refine fail_frag o h hQc fun u ⟨hu, hne⟩ => ⟨_, hu.1, ?_⟩
      rw [eval_lt (x := pl.length) (y := 9) (by omega) (by decide) (dat_jpl h hu.1)
        (by simp only [eval, hu.2.1]; rfl)] at hne
      have h9 := bw_ne0 hne
      simp only [decide_eq_true_eq] at h9
      exact ⟨dat_jok (dat_fail hu.1) (by simp; omega), fun e => by omega⟩
    · refine frag_pure (9 ≤ pl.length) (fun u ⟨hu, h0⟩ => ?_) (lowK_any _ (k := .skip) (c := _) rfl) fun h9 => ?_
      · rw [eval_lt (x := pl.length) (y := 9) (by omega) (by decide) (dat_jpl h hu.1)
          (by simp only [eval, hu.2.1]; rfl)] at h0
        have := bw_eq0 h0
        simpa using this
      have hml : mlOf pl = pl[8].toNat := by
        simp [mlOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 8 < pl.length by omega)]; rfl
      have hjpp : ∀ b (u : PancakeState σ), DAt A s0 b u → u.locals "jpp" = some (at_ A (sWindow + o' + 13)) :=
        fun b u hu => (dat_local hu (by decide)).trans h.jpp
      let M (j : Nat) (u : PancakeState σ) : Prop := DAt A s0 true u ∧ u.locals "ji" = some (BitVec.ofNat 64 j) ∧
        u.locals "jseq" = some (BitVec.ofNat 64 (readLE (pl.take 8))) ∧
        u.locals "jml" = some (BitVec.ofNat 64 (mlOf pl))
      have hMc : ∀ j, Safe.ClockFree (M j) :=
        fun _ _ _ ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4, h5, h6⟩
      have g1 : Frag o [.assign "jml" (ScanProg.byte (Syntax.eAdd (Syntax.v "jpp") (Syntax.v "ji")))]
          (fun u => (DAt A s0 (decide (8 ≤ pl.length)) u ∧ u.locals "ji" = some (BitVec.ofNat 64 8) ∧
            (8 ≤ pl.length → u.locals "jseq" = some (BitVec.ofNat 64 (readLE (pl.take 8))))) ∧
            eval u (.cmp .less (.var "jpl") (.op .add (.var "ji") (.const 1))) = some 0) (M 8) :=
        set_frag o (E := .loadByte (.op .add (.var "jpp") (.var "ji"))) rfl (hMc 8) fun u ⟨hu, _⟩ => by
          have hu1 := dat_jok hu.1 (show decide (8 ≤ pl.length) = true by simp; omega)
          refine ⟨BitVec.ofNat 64 (mlOf pl), ?_, dat_bound h hu1 (by decide), dat_set hu1 (by decide) (by decide)
            (by decide) _, by simp [setL, setLocal, hu.2.1], by simp [setL, setLocal, hu.2.2 (by omega)],
            by simp [setL, setLocal]⟩
          simp only [eval, hjpp _ u hu.1, hu.2.1, dat_byte h hu.1 8 (by omega), Bytes.setWidth8_64, hml]; rfl
      have g2 : Frag o [ScanProg.inc "ji"] (M 8) (M 9) :=
        set_frag o (E := .op .add (.var "ji") (.const 1)) rfl (hMc 9) fun u hu => ⟨BitVec.ofNat 64 9,
          by simp only [eval, hu.2.1]; rfl, ⟨_, hu.2.1⟩, ⟨kept_set hu.1.1 (by decide) _, ⟨9, by simp [setL, setLocal],
            by omega⟩, by simp [setL, setLocal, hu.1.2.2]⟩, by simp [setL, setLocal],
            by simp [setL, setLocal, hu.2.2.1],
          by simp [setL, setLocal, hu.2.2.2]⟩
      refine frag_append (xs := [_]) g1 (frag_append (xs := [_]) g2 ?_)
      have hjml : ∀ u, M 9 u → eval u (.op .add (.var "ji") (.var "jml")) = some (BitVec.ofNat 64 (9 + mlOf pl)) :=
        fun u hu => by simp only [eval, hu.2.1, hu.2.2.2]; rw [← BitVec.ofNat_add]
      have hmlb : mlOf pl < 256 := by rw [hml]; exact pl[8].isLt
      refine frag_ite o (C := .cmp .less (.var "jpl") (.op .add (.var "ji") (.var "jml"))) rfl hQc
        (fun u hu => ⟨_, eval_lt (x := pl.length) (y := 9 + mlOf pl) (by omega) (by omega) (dat_jpl h hu.1)
          (hjml u hu)⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
      · refine fail_frag o h hQc fun u ⟨hu, hne⟩ => ⟨_, hu.1, ?_⟩
        rw [eval_lt (by omega) (by omega) (dat_jpl h hu.1) (hjml u hu)] at hne
        have h' := bw_ne0 hne
        simp only [decide_eq_true_eq] at h'
        exact ⟨dat_jok (dat_fail hu.1) (by simp; omega), fun e => by omega⟩
      · refine frag_pure (9 + mlOf pl ≤ pl.length) (fun u ⟨hu, h0⟩ => ?_)
          (lowK_any _ (k := .skip) (c := _) rfl) fun hok => ?_
        · rw [eval_lt (by omega) (by omega) (dat_jpl h hu.1) (hjml u hu)] at h0
          have := bw_eq0 h0
          simpa using this
        let N (u : PancakeState σ) : Prop := M 9 u ∧ u.memory (at_ A sIdAt) = BitVec.ofNat 64 (o' + 13 + 9)
        have hNc : Safe.ClockFree N := fun _ _ ⟨h1, h2⟩ => ⟨hMc 9 _ _ h1, h2⟩
        let N2 (u : PancakeState σ) : Prop := N u ∧ u.memory (at_ A sIdLen) = BitVec.ofNat 64 (mlOf pl)
        have hN2c : Safe.ClockFree N2 := fun _ _ ⟨h1, h2⟩ => ⟨hNc _ _ h1, h2⟩
        have s1 : Frag o [ScanProg.setw sIdAt (ScanProg.inWindow (Syntax.v "ji"))]
            (fun u => M 9 u ∧ eval u (.cmp .less (.var "jpl") (.op .add (.var "ji") (.var "jml"))) = some 0) N :=
          store_frag o (D := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sIdAt)))
            (E := .op .add (.op .add (.var "jo") (.const (BitVec.ofNat 64 headerLength))) (.var "ji")) rfl rfl hNc
            fun u ⟨hu, _⟩ => ⟨at_ A sIdAt, BitVec.ofNat 64 (o' + 13 + 9),
              by simp [eval, (dat_local hu.1 (by decide)).trans h.sp, at_],
              by simp only [eval, (dat_local hu.1 (by decide)).trans h.jo, hu.2.1, headerLength,
                ← BitVec.ofNat_add], dom_at h hu.1.1.memaddrs (by decide) (by decide),
              ⟨⟨kept_word hu.1.1 ⟨sIdAt, by decide, by decide, rfl⟩ _, hu.1.2⟩, hu.2⟩, by simp⟩
        have s2 : Frag o [ScanProg.setw sIdLen (Syntax.v "jml")] N N2 :=
          store_frag o (D := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sIdLen))) (E := .var "jml") rfl rfl hN2c
            fun u hu => ⟨at_ A sIdLen, BitVec.ofNat 64 (mlOf pl),
              by simp [eval, (dat_local hu.1.1 (by decide)).trans h.sp, at_], by simp only [eval]; exact hu.1.2.2.2,
              dom_at h hu.1.1.1.memaddrs (by decide) (by decide),
              ⟨⟨⟨kept_word hu.1.1.1 ⟨sIdLen, by decide, by decide, rfl⟩ _,
                hu.1.1.2⟩, hu.1.2⟩, by
                  show (if at_ A sIdAt = at_ A sIdLen then _ else u.memory (at_ A sIdAt)) = _
                  rw [if_neg (by unfold at_; exact region_addr_inj A _ _ (by decide) (by decide) (by decide))]
                  exact hu.2⟩, by simp⟩
        have s3 : Frag o [.assign "ji" (Syntax.eAdd (Syntax.v "ji") (Syntax.v "jml"))] N2 Q :=
          set_frag o (E := .op .add (.var "ji") (.var "jml")) rfl hQc fun u hu => ⟨_, hjml u hu.1.1, ⟨_, hu.1.1.2.1⟩,
            ⟨kept_set hu.1.1.1.1 (by decide) _, ⟨9 + mlOf pl, by simp [setL, setLocal], by omega⟩, by
              simp only [setL, setLocal]; rw [hu.1.1.1.2.2]; simp [hok]⟩, fun _ => ⟨by simp [setL, setLocal],
              by simp [setL, setLocal, hu.1.1.2.2.2], by simp [setL, setLocal, hu.1.1.2.2.1], hu.1.2, hu.2⟩⟩
        exact frag_append (xs := [_]) s1 (frag_append (xs := [_]) s2 s3)
  · intro hb u hu
    simp only [decide_eq_false_iff_not] at hb
    exact ⟨dat_jok hu.1 (by simp; omega), fun e => by omega⟩

/-- **The commit's count of groups**, at most `groupsMax`. -/
theorem decC_frag (o : Oracle σ) (h : DecIn A o' pl s0) :
    Frag o ScanProg.countPart
      (fun u => DAt A s0 (decide (9 + mlOf pl ≤ pl.length)) u ∧ (9 + mlOf pl ≤ pl.length →
        u.locals "ji" = some (BitVec.ofNat 64 (9 + mlOf pl)) ∧ BFacts A o' pl u))
      (fun u => DAt A s0 (decide (10 + mlOf pl ≤ pl.length ∧ gcOf pl ≤ 16)) u ∧
        (10 + mlOf pl ≤ pl.length ∧ gcOf pl ≤ 16 → u.locals "ji" = some (BitVec.ofNat 64 (10 + mlOf pl)) ∧
          u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧ BFacts A o' pl u)) := by
  have hn := nums
  have hl := h.len
  let Q (u : PancakeState σ) : Prop := DAt A s0 (decide (10 + mlOf pl ≤ pl.length ∧ gcOf pl ≤ 16)) u ∧
    (10 + mlOf pl ≤ pl.length ∧ gcOf pl ≤ 16 → u.locals "ji" = some (BitVec.ofNat 64 (10 + mlOf pl)) ∧
      u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧ BFacts A o' pl u)
  have hQc : Safe.ClockFree Q := fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩
  refine flagIf_frag o (lowK_any _ (k := .skip) (c := _) rfl) rfl hQc (fun u hu => hu.1.2.2) ?_
    (fun hb u hu => ⟨dat_jok hu.1 (by
      rw [hb]; symm; rw [decide_eq_false_iff_not]; intro e; simp at hb; exact absurd e.1 (by omega)),
      fun e => absurd e.1 (by simp at hb; omega)⟩)
  intro hb
  have hb : 9 + mlOf pl ≤ pl.length := by simpa using hb
  refine frag_ite o (C := .cmp .less (.var "jpl") (.op .add (.var "ji") (.const (BitVec.ofNat 64 1)))) rfl hQc
    (fun u hu => ⟨_, eval_lt (x := pl.length) (y := 9 + mlOf pl + 1) (by omega) (by omega) (dat_jpl h hu.1)
      (eval_addc (e := .var "ji") 1 (hu.2 hb).1)⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
  · refine fail_frag o h hQc fun u ⟨hu, hne⟩ => ⟨_, hu.1, ?_⟩
    rw [eval_lt (x := pl.length) (y := 9 + mlOf pl + 1) (by omega) (by omega) (dat_jpl h hu.1)
      (eval_addc (e := .var "ji") 1 (hu.2 hb).1)] at hne
    have h' := bw_ne0 hne
    simp only [decide_eq_true_eq] at h'
    exact ⟨dat_jok (dat_fail hu.1) (by simp; omega), fun e => by omega⟩
  refine frag_pure (10 + mlOf pl ≤ pl.length) (fun u ⟨hu, h0⟩ => ?_) (lowK_any _ (k := .skip) (c := _) rfl)
    fun h10 => ?_
  · rw [eval_lt (x := pl.length) (y := 9 + mlOf pl + 1) (by omega) (by omega) (dat_jpl h hu.1)
      (eval_addc (e := .var "ji") 1 (hu.2 hb).1)] at h0
    have := bw_eq0 h0
    simp at this; omega
  have hgc : gcOf pl = pl[9 + mlOf pl].toNat := by
    simp [gcOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 9 + mlOf pl < pl.length by omega)]
  have hgcb : gcOf pl < 256 := by rw [hgc]; exact (pl[9 + mlOf pl]).isLt
  let M (j : Nat) (u : PancakeState σ) : Prop := DAt A s0 true u ∧ u.locals "ji" = some (BitVec.ofNat 64 j) ∧
    u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧ BFacts A o' pl u
  have hMc : ∀ j, Safe.ClockFree (M j) := fun _ _ _ ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4, h5, h6⟩
  have kbf : ∀ (u : PancakeState σ) (x : String) (v : Value), x ∈ ["jgc", "ji", "jok"] → BFacts A o' pl u →
      BFacts A o' pl (setL u x v) := fun u x v hx hb => by
    simp at hx
    rcases hx with rfl | rfl | rfl <;>
      exact bfacts_set hb (by decide) (by decide) v
  have g1 : Frag o [.assign "jgc" (ScanProg.byte (Syntax.eAdd (Syntax.v "jpp") (Syntax.v "ji")))]
      (fun u => (DAt A s0 (decide (9 + mlOf pl ≤ pl.length)) u ∧ (9 + mlOf pl ≤ pl.length →
        u.locals "ji" = some (BitVec.ofNat 64 (9 + mlOf pl)) ∧ BFacts A o' pl u)) ∧
        eval u (.cmp .less (.var "jpl") (.op .add (.var "ji") (.const (BitVec.ofNat 64 1)))) = some 0)
      (M (9 + mlOf pl)) :=
    set_frag o (E := .loadByte (.op .add (.var "jpp") (.var "ji"))) rfl (hMc _) fun u ⟨hu, _⟩ => by
      have hu1 := dat_jok hu.1 (show decide (9 + mlOf pl ≤ pl.length) = true by simp; omega)
      refine ⟨BitVec.ofNat 64 (gcOf pl), ?_, dat_bound h hu1 (by decide), dat_set hu1 (by decide) (by decide)
        (by decide) _, by simp [setL, setLocal, (hu.2 hb).1], by simp [setL, setLocal],
        kbf u _ _ (by decide) (hu.2 hb).2⟩
      simp only [eval, (dat_local hu.1 (by decide)).trans h.jpp, (hu.2 hb).1, dat_byte h hu.1 (9 + mlOf pl) (by omega),
        Bytes.setWidth8_64, hgc]
  have g2 : Frag o [ScanProg.inc "ji"] (M (9 + mlOf pl)) (M (10 + mlOf pl)) :=
    set_frag o (E := .op .add (.var "ji") (.const 1)) rfl (hMc _) fun u hu => ⟨BitVec.ofNat 64 (10 + mlOf pl),
      by rw [show 10 + mlOf pl = 9 + mlOf pl + 1 by omega]; exact eval_addc (e := .var "ji") 1 hu.2.1,
      ⟨_, hu.2.1⟩, ⟨kept_set hu.1.1 (by decide) _, ⟨10 + mlOf pl, by simp [setL, setLocal], by omega⟩,
        by simp [setL, setLocal, hu.1.2.2]⟩,
      by simp [setL, setLocal], by simp [setL, setLocal, hu.2.2.1], kbf u _ _ (by decide) hu.2.2.2⟩
  refine frag_append (xs := [_]) g1 (frag_append (xs := [_]) g2 ?_)
  have hev : ∀ u, M (10 + mlOf pl) u → eval u (.cmp .less (.const (BitVec.ofNat 64 groupsMax)) (.var "jgc")) =
      some (bw (decide (16 < gcOf pl))) := fun u hu =>
    eval_lt (by decide) (by omega) rfl (by simp only [eval]; exact hu.2.2.1)
  refine frag_ite o (C := .cmp .less (.const (BitVec.ofNat 64 groupsMax)) (.var "jgc")) rfl hQc
    (fun u hu => ⟨_, hev u hu⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
  · refine fail_frag o h hQc fun u ⟨hu, hne⟩ => ⟨_, hu.1, ?_⟩
    rw [hev u hu] at hne
    have h' := bw_ne0 hne
    simp only [decide_eq_true_eq] at h'
    exact ⟨dat_jok (dat_fail hu.1) (by simp; omega), fun e => by omega⟩
  · rw [hev u hu] at h0
    have h' := bw_eq0 h0
    simp only [decide_eq_false_iff_not] at h'
    exact ⟨dat_jok hu.1 (by simp; omega), fun _ => ⟨hu.2.1, hu.2.2.1, hu.2.2.2⟩⟩

/-! ### The groups -/

/-- The verdict once the count of groups is read. -/
def okCOf (pl : Bytes) : Bool := decide (10 + mlOf pl ≤ pl.length ∧ gcOf pl ≤ 16)

/-- …and once `g` groups are read. -/
def gokOf (pl : Bytes) (g : Nat) : Bool := okCOf pl && (scanGroups pl g (10 + mlOf pl)).isSome

/-- Group `h`'s slot: where its name lies in the window, its length and its number. The name is the payload's octets
from `s`. -/
def SlotAt (A : Word) (o' : Nat) (pl : Bytes) (h : Nat) (gr : Group) (u : PancakeState σ) : Prop :=
  ∃ s, u.memory (at_ A (sGroups + 24 * h)) = BitVec.ofNat 64 (o' + 13 + s) ∧
    u.memory (at_ A (sGroups + 24 * h + 8)) = BitVec.ofNat 64 gr.name.length ∧
    u.memory (at_ A (sGroups + 24 * h + 16)) = BitVec.ofNat 64 gr.number ∧
    gr.name = (pl.drop s).take gr.name.length ∧ s + gr.name.length ≤ pl.length

/-- The loop over the groups after `g` of them. -/
def GInv (A : Word) (s0 : PancakeState σ) (o' : Nat) (pl : Bytes) (g j : Nat) (u : PancakeState σ) : Prop :=
  DAt A s0 (gokOf pl g) u ∧ u.locals "jgi" = some (BitVec.ofNat 64 j) ∧
    (okCOf pl = true → g ≤ gcOf pl ∧ u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧ BFacts A o' pl u) ∧
    (∀ r, gokOf pl g = true → scanGroups pl g (10 + mlOf pl) = some r →
      u.locals "ji" = some (BitVec.ofNat 64 r.2) ∧ ∀ h (hh : h < r.1.length), SlotAt A o' pl h r.1[h] u)

theorem ginv_clock {g j : Nat} : Safe.ClockFree (GInv A s0 o' pl g j) :=
  fun _ _ ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4, h5, h6⟩

theorem slot_word {h : Nat} {gr : Group} {u : PancakeState σ} (hs : SlotAt A o' pl h gr u) {x : Nat}
    (hx : x < 2 ^ 63) (h0 : x ≠ sGroups + 24 * h) (h8 : x ≠ sGroups + 24 * h + 8) (h16 : x ≠ sGroups + 24 * h + 16)
    (hh : h < 256) (v : Word) :
    SlotAt A o' pl h gr { u with memory := fun k => if k = at_ A x then v else u.memory k } := by
  have hn := nums
  obtain ⟨s, e0, e8, e16, en, el⟩ := hs
  have ne : ∀ y, y < 2 ^ 63 → y ≠ x → at_ A y ≠ at_ A x := fun y hy hne e =>
    region_addr_inj A y x (by omega) (by omega) hne e
  refine ⟨s, ?_, ?_, ?_, en, el⟩ <;> simp only
  · rw [if_neg (ne _ (by simp only [sGroups]; omega) (Ne.symm h0))]; exact e0
  · rw [if_neg (ne _ (by simp only [sGroups]; omega) (Ne.symm h8))]; exact e8
  · rw [if_neg (ne _ (by simp only [sGroups]; omega) (Ne.symm h16))]; exact e16

theorem bfacts_word {u : PancakeState σ} (hb : BFacts A o' pl u) {x : Nat} (hx : x < 2 ^ 63) (h1 : x ≠ sIdAt)
    (h2 : x ≠ sIdLen) (v : Word) :
    BFacts A o' pl { u with memory := fun k => if k = at_ A x then v else u.memory k } := by
  have ne : ∀ y, y < 2 ^ 63 → y ≠ x → at_ A y ≠ at_ A x := fun y hy hne e =>
    region_addr_inj A y x (by omega) (by omega) hne e
  refine ⟨hb.1, hb.2.1, ?_, ?_⟩ <;> simp only
  · rw [if_neg (ne _ (by decide) (Ne.symm h1))]; exact hb.2.2.1
  · rw [if_neg (ne _ (by decide) (Ne.symm h2))]; exact hb.2.2.2

/-- A group's bounds as the program tests them, two flags each, are `bounded`'s. -/
theorem bounded_flags (n m : Nat) :
    ((decide (n < 1) || decide (64 < n)) || (decide (m < 1) || decide (2 ^ 31 - 1 < m))) =
      !(decide (1 ≤ n) && decide (n ≤ 64) && decide (1 ≤ m) && decide (m < 2 ^ 31)) := by
  cases h1 : decide (1 ≤ n) <;> cases h2 : decide (n ≤ 64) <;> cases h3 : decide (1 ≤ m) <;>
    cases h4 : decide (m < 2 ^ 31) <;> simp_all <;> omega

/-- **One group**: read, its slot written, and checked. -/
theorem decGroup_frag (o : Oracle σ) (h : DecIn A o' pl s0) {fail : List Syntax.PStmt} (hfl : LowKK fail)
    (hfd : declared fail = []) (g : Nat) (hc : (gokOf pl g && decide (g < gcOf pl)) = true) :
    Frag o (ScanProg.groupBody fail) (GInv A s0 o' pl g g) (GInv A s0 o' pl (g + 1) (g + 1)) := by
  have hn := nums
  have hl := h.len
  simp only [gokOf, Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq] at hc
  obtain ⟨⟨hokC, r, hr⟩, hg⟩ := hc
  have hokC' : 10 + mlOf pl ≤ pl.length ∧ gcOf pl ≤ 16 := by simpa [okCOf] using hokC
  obtain ⟨hrl, hik, hkl⟩ := scanGroups_le hr
  have hgok : gokOf pl g = true := by simp [gokOf, hokC, hr]
  have hk : r.2 ≤ pl.length := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · subst h0; simp [scanGroups] at hr; rw [← hr]; exact hokC'.1
    · exact hkl (by omega)
  have hg16 : g < 16 := by omega
  -- the reading of the group so far
  let Mid (j : Nat) (u : PancakeState σ) : Prop := DAt A s0 true u ∧ u.locals "jgi" = some (BitVec.ofNat 64 g) ∧
    u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧ BFacts A o' pl u ∧ u.locals "ji" = some (BitVec.ofNat 64 j) ∧
    ∀ h (hh : h < r.1.length), SlotAt A o' pl h r.1[h] u
  have hMc : ∀ j, Safe.ClockFree (Mid j) := fun _ _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩
  have mid_set : ∀ j (u : PancakeState σ), Mid j u → ∀ x, x ∈ decNames → x ≠ "ji" → x ≠ "jok" → x ≠ "jgi" →
      x ≠ "jgc" → x ≠ "jml" → x ≠ "jseq" → ∀ v, Mid j (setL u x v) := fun j u hu x hx h1 h2 h3 h4 h5 h6 v =>
    ⟨dat_set hu.1 hx h1 h2 v, by simp [setL, setLocal, Ne.symm h3, hu.2.1],
      by simp [setL, setLocal, Ne.symm h4, hu.2.2.1],
      bfacts_set hu.2.2.2.1 h5 h6 v, by simp [setL, setLocal, Ne.symm h1, hu.2.2.2.2.1], hu.2.2.2.2.2⟩
  have mid_ji : ∀ j (u : PancakeState σ), Mid j u → ∀ j', j' ≤ pl.length → Mid j' (setL u "ji" (BitVec.ofNat 64 j')) :=
    fun j u hu j' hj' => ⟨⟨kept_set hu.1.1 (by decide) _, ⟨j', by simp [setL, setLocal], by omega⟩,
      by simp [setL, setLocal, hu.1.2.2]⟩, by simp [setL, setLocal, hu.2.1], by simp [setL, setLocal, hu.2.2.1],
      bfacts_set hu.2.2.2.1 (by decide) (by decide) _,
      by simp [setL, setLocal], hu.2.2.2.2.2⟩
  -- a step that fails: the group is not one, nor are those after it
  have gnone : oneGroup pl r.2 = none → gokOf pl (g + 1) = false := fun e => by
    simp [gokOf, scanGroups_snoc, hr, e]
  have mid_fail : ∀ j (u : PancakeState σ), Mid j u → oneGroup pl r.2 = none →
      GInv A s0 o' pl (g + 1) g (setL u "jok" (BitVec.ofNat 64 0)) := fun j u hu e =>
    ⟨dat_jok (dat_fail hu.1) (gnone e).symm, by simp [setL, setLocal, hu.2.1], fun _ => ⟨by omega,
      by simp [setL, setLocal, hu.2.2.1], bfacts_set hu.2.2.2.1 (by decide) (by decide) _⟩,
      fun r' hg' _ => by rw [gnone e] at hg'; cases hg'⟩
  have hfc : Safe.ClockFree (GInv A s0 o' pl (g + 1) g) := ginv_clock
  have fkept : Frag o [ScanProg.kept fail "ji" maxPayload] (GInv A s0 o' pl g g) (Mid r.2) :=
    frag_conseq (kept_skip o hfl hfd (by omega) (hMc r.2) fun u hu => ⟨r.2, hu.2.2.2.2.1, by omega⟩)
      (fun u hu => by
        have hu1 := dat_jok hu.1 hgok
        obtain ⟨_, hjgc, hbf⟩ := hu.2.2.1 hokC
        obtain ⟨hji, hsl⟩ := hu.2.2.2 r hgok hr
        exact ⟨hu1, hu.2.1, hjgc, hbf, hji, hsl⟩) fun _ h => h
  have finc : Frag o [ScanProg.inc "jgi"] (GInv A s0 o' pl (g + 1) g) (GInv A s0 o' pl (g + 1) (g + 1)) :=
    set_frag o (E := .op .add (.var "jgi") (.const 1)) rfl ginv_clock fun u hu => ⟨_, eval_addc 1 hu.2.1, ⟨_, hu.2.1⟩,
      dat_set hu.1 (by decide) (by decide) (by decide) _, by simp [setL, setLocal],
      fun hc => ⟨(hu.2.2.1 hc).1, by simp [setL, setLocal, (hu.2.2.1 hc).2.1],
        ⟨by simp [setL, setLocal, (hu.2.2.1 hc).2.2.1], by simp [setL, setLocal, (hu.2.2.1 hc).2.2.2.1],
          (hu.2.2.1 hc).2.2.2.2⟩⟩, fun r' hg' hr' => ⟨by simp [setL, setLocal, (hu.2.2.2 r' hg' hr').1],
          fun h' hh => (hu.2.2.2 r' hg' hr').2 h' hh⟩⟩
  refine frag_append (xs := [_]) fkept (frag_append (xs := [_]) ?_ finc)
  -- a word of group `g`'s slot written
  have mid_word : ∀ j (u : PancakeState σ), Mid j u → ∀ d, d = 0 ∨ d = 8 ∨ d = 16 → ∀ v,
      Mid j { u with memory := fun k => if k = at_ A (sGroups + 24 * g + d) then v else u.memory k } :=
    fun j u hu d hd v => by
      have hx : sGroups + 24 * g + d < 2 ^ 63 := by simp only [sGroups]; omega
      refine ⟨⟨kept_word hu.1.1 ⟨_, by simp only [sType, sGroups]; omega, by simp only [sGroups]; omega, rfl⟩ _,
        hu.1.2.1, hu.1.2.2⟩, hu.2.1, hu.2.2.1, bfacts_word hu.2.2.2.1 hx (by simp only [sGroups, sIdAt]; omega)
        (by simp only [sGroups, sIdLen]; omega) v, hu.2.2.2.2.1, fun h' hh => ?_⟩
      have hh' : h' < g := by omega
      exact slot_word (hu.2.2.2.2.2 h' hh) hx (by omega) (by omega) (by omega) (by omega) v
  have hC1 : ∀ u, Mid r.2 u → eval u (.cmp .less (.var "jpl") (.op .add (.var "ji") (.const (BitVec.ofNat 64 1)))) =
      some (bw (decide (pl.length < r.2 + 1))) := fun u hu =>
    eval_lt (by omega) (by omega) (dat_jpl h hu.1) (eval_addc (e := .var "ji") 1 hu.2.2.2.2.1)
  refine frag_ite o (C := .cmp .less (.var "jpl") (.op .add (.var "ji") (.const (BitVec.ofNat 64 1)))) rfl hfc
    (fun u hu => ⟨_, hC1 u hu⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
  · -- no octet of length
    refine fail_frag o h hfc fun u ⟨hu, hne⟩ => ⟨_, hu.1, ?_⟩
    rw [hC1 u hu] at hne
    have h' := bw_ne0 hne
    simp only [decide_eq_true_eq] at h'
    exact mid_fail _ u hu (by simp only [oneGroup]; rw [if_pos h'])
  refine frag_pure (r.2 + 1 ≤ pl.length) (fun u ⟨hu, h0⟩ => ?_) (lowK_any _ (k := .skip) (c := _) rfl) fun h1 => ?_
  · rw [hC1 u hu] at h0
    have := bw_eq0 h0
    simp at this; omega
  have hgd : pl.getD r.2 0 = pl[r.2] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show r.2 < pl.length by omega)]; rfl
  have hnl := (pl[r.2]).isLt
  let Mn (j : Nat) (u : PancakeState σ) : Prop := Mid j u ∧ u.locals "jnl" = some (BitVec.ofNat 64 (pl[r.2]).toNat)
  have hMnc : ∀ j, Safe.ClockFree (Mn j) := fun j _ _ ⟨h1, h2⟩ => ⟨hMc j _ _ h1, h2⟩
  have g1 : Frag o [.assign "jnl" (ScanProg.byte (Syntax.eAdd (Syntax.v "jpp") (Syntax.v "ji")))]
      (fun u => Mid r.2 u ∧ eval u (.cmp .less (.var "jpl") (.op .add (.var "ji")
        (.const (BitVec.ofNat 64 1)))) = some 0) (Mn r.2) :=
    set_frag o (E := .loadByte (.op .add (.var "jpp") (.var "ji"))) rfl (hMnc _) fun u ⟨hu, _⟩ => by
      refine ⟨BitVec.ofNat 64 (pl[r.2]).toNat, ?_, dat_bound h hu.1 (by decide),
        mid_set _ u hu _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _,
        by simp [setL, setLocal]⟩
      simp only [eval, (dat_local hu.1 (by decide)).trans h.jpp, hu.2.2.2.2.1, dat_byte h hu.1 r.2 (by omega),
        Bytes.setWidth8_64]; rfl
  have g2 : Frag o [ScanProg.inc "ji"] (Mn r.2) (Mn (r.2 + 1)) :=
    set_frag o (E := .op .add (.var "ji") (.const 1)) rfl (hMnc _) fun u hu => ⟨_, eval_addc 1 hu.1.2.2.2.2.1,
      ⟨_, hu.1.2.2.2.2.1⟩, mid_ji _ u hu.1 _ h1, by simp [setL, setLocal, hu.2]⟩
  refine frag_append (xs := [_]) g1 (frag_append (xs := [_]) g2 ?_)
  have hC2 : ∀ u, Mn (r.2 + 1) u → eval u (.cmp .less (.var "jpl") (.op .add (.var "ji") (.var "jnl"))) =
      some (bw (decide (pl.length < r.2 + 1 + (pl[r.2]).toNat))) := fun u hu =>
    eval_lt (by omega) (by omega) (dat_jpl h hu.1.1) (eval_add (e := .var "ji") (f := .var "jnl") hu.1.2.2.2.2.1 hu.2)
  refine frag_ite o (C := .cmp .less (.var "jpl") (.op .add (.var "ji") (.var "jnl"))) rfl hfc
    (fun u hu => ⟨_, hC2 u hu⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
  · -- the name past the payload
    refine fail_frag o h hfc fun u ⟨hu, hne⟩ => ⟨_, hu.1.1, ?_⟩
    rw [hC2 u hu] at hne
    have h' := bw_ne0 hne
    simp only [decide_eq_true_eq] at h'
    exact mid_fail _ u hu.1 (by simp only [oneGroup]; rw [if_neg (by omega), hgd, if_pos h'])
  refine frag_pure (r.2 + 1 + (pl[r.2]).toNat ≤ pl.length) (fun u ⟨hu, h0⟩ => ?_)
    (lowK_any _ (k := .skip) (c := _) rfl) fun h2 => ?_
  · rw [hC2 u hu] at h0
    have := bw_eq0 h0
    simp at this; omega
  -- the slot: where the name lies, and its length
  let S0 (u : PancakeState σ) : Prop := Mn (r.2 + 1) u ∧ u.locals "jgp" = some (at_ A (sGroups + 24 * g))
  let S1 (u : PancakeState σ) : Prop := S0 u ∧
    u.memory (at_ A (sGroups + 24 * g)) = BitVec.ofNat 64 (o' + 13 + (r.2 + 1))
  let S2 (u : PancakeState σ) : Prop := S1 u ∧
    u.memory (at_ A (sGroups + 24 * g + 8)) = BitVec.ofNat 64 (pl[r.2]).toNat
  have hS0c : Safe.ClockFree S0 := fun _ _ ⟨h1, h2⟩ => ⟨hMnc _ _ _ h1, h2⟩
  have hS1c : Safe.ClockFree S1 := fun _ _ ⟨h1, h2⟩ => ⟨hS0c _ _ h1, h2⟩
  have hS2c : Safe.ClockFree S2 := fun _ _ ⟨h1, h2⟩ => ⟨hS1c _ _ h1, h2⟩
  have hsl : (24 * g + sGroups) % 8 = 0 := by simp only [sGroups]; omega
  have s0f : Frag o [.assign "jgp" (ScanProg.slot "jgi")] (fun u => Mn (r.2 + 1) u ∧
      eval u (.cmp .less (.var "jpl") (.op .add (.var "ji") (.var "jnl"))) = some 0) S0 :=
    set_frag o (E := .op .add (.op .add (.var "jsc") (.const (BitVec.ofNat 64 sGroups)))
      (.mul (.var "jgi") (.const (BitVec.ofNat 64 groupSlot)))) rfl hS0c fun u ⟨hu, _⟩ => by
      refine ⟨at_ A (sGroups + 24 * g), ?_, dat_bound h hu.1.1 (by decide),
        ⟨mid_set _ u hu.1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _,
          by simp [setL, setLocal, hu.2]⟩, by simp [setL, setLocal]⟩
      simp only [eval, (dat_local hu.1.1 (by decide)).trans h.sp, hu.1.2.1, groupSlot, ofNat_mul24, at_, add_ofNat]
  have s1f : Frag o [.store (Syntax.v "jgp") (ScanProg.inWindow (Syntax.v "ji"))] S0 S1 :=
    store_frag o (D := .var "jgp") (E := .op .add (.op .add (.var "jo") (.const (BitVec.ofNat 64 headerLength)))
      (.var "ji")) rfl rfl hS1c fun u hu => ⟨_, BitVec.ofNat 64 (o' + 13 + (r.2 + 1)), hu.2,
        eval_add (eval_addc (e := .var "jo") 13 ((dat_local hu.1.1.1 (by decide)).trans h.jo)) hu.1.1.2.2.2.2.1,
        dom_at h hu.1.1.1.1.memaddrs (by omega) (by simp only [sGroups, ScanProg.size]; omega),
        ⟨⟨mid_word _ u hu.1.1 0 (Or.inl rfl) _, by simpa using hu.1.2⟩, hu.2⟩, by simp⟩
  have s2f : Frag o [.store (Syntax.atOff (Syntax.v "jgp") 8) (Syntax.v "jnl")] S1 S2 :=
    store_frag o (D := .op .add (.var "jgp") (.const (BitVec.ofNat 64 8))) (E := .var "jnl") rfl rfl hS2c
      fun u hu => ⟨at_ A (sGroups + 24 * g + 8), _, by simp only [eval, hu.1.2, at_add], hu.1.1.2,
        dom_at h hu.1.1.1.1.1.memaddrs (by omega) (by simp only [sGroups, ScanProg.size]; omega),
        ⟨⟨⟨mid_word _ u hu.1.1.1 8 (Or.inr (Or.inl rfl)) _, by simpa using hu.1.1.2⟩, hu.1.2⟩, by
          show (if at_ A (sGroups + 24 * g) = at_ A (sGroups + 24 * g + 8) then _ else _) = _
          rw [if_neg (at_ne (by simp only [sGroups]; omega) (by simp only [sGroups]; omega) (by omega))]
          exact hu.2⟩, by simp⟩
  refine frag_append (xs := [_]) s0f (frag_append (xs := [_]) s1f (frag_append (xs := [_]) s2f ?_))
  -- past the name
  let N := r.2 + 1 + (pl[r.2]).toNat
  let S3 (u : PancakeState σ) : Prop := Mn N u ∧ u.locals "jgp" = some (at_ A (sGroups + 24 * g)) ∧
    u.memory (at_ A (sGroups + 24 * g)) = BitVec.ofNat 64 (o' + 13 + (r.2 + 1)) ∧
    u.memory (at_ A (sGroups + 24 * g + 8)) = BitVec.ofNat 64 (pl[r.2]).toNat
  have hS3c : Safe.ClockFree S3 := fun _ _ ⟨h1, h2⟩ => ⟨hMnc _ _ _ h1, h2⟩
  have s3f : Frag o [.assign "ji" (Syntax.eAdd (Syntax.v "ji") (Syntax.v "jnl"))] S2 S3 :=
    set_frag o (E := .op .add (.var "ji") (.var "jnl")) rfl hS3c fun u hu => ⟨_,
      eval_add (e := .var "ji") (f := .var "jnl") hu.1.1.1.1.2.2.2.2.1 hu.1.1.1.2, ⟨_, hu.1.1.1.1.2.2.2.2.1⟩,
      ⟨mid_ji _ u hu.1.1.1.1 _ h2, by simp [setL, setLocal, hu.1.1.1.2]⟩, by simp [setL, setLocal, hu.1.1.2],
      hu.1.2, hu.2⟩
  refine frag_append (xs := [_]) s3f ?_
  have hC3 : ∀ u, S3 u → eval u (.cmp .less (.var "jpl") (.op .add (.var "ji") (.const (BitVec.ofNat 64 4)))) =
      some (bw (decide (pl.length < N + 4))) := fun u hu =>
    eval_lt (by omega) (by omega) (dat_jpl h hu.1.1.1) (eval_addc (e := .var "ji") 4 hu.1.1.2.2.2.2.1)
  refine frag_ite o (C := .cmp .less (.var "jpl") (.op .add (.var "ji") (.const (BitVec.ofNat 64 4)))) rfl hfc
    (fun u hu => ⟨_, hC3 u hu⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
  · -- no number after the name
    refine fail_frag o h hfc fun u ⟨hu, hne⟩ => ⟨_, hu.1.1.1, ?_⟩
    rw [hC3 u hu] at hne
    have h' := bw_ne0 hne
    simp only [decide_eq_true_eq] at h'
    exact mid_fail _ u hu.1.1 (by simp only [oneGroup]; rw [if_neg (by omega), hgd, if_neg (by omega), if_pos h'])
  refine frag_pure (N + 4 ≤ pl.length) (fun u ⟨hu, h0⟩ => ?_) (lowK_any _ (k := .skip) (c := _) rfl) fun h3 => ?_
  · rw [hC3 u hu] at h0
    have := bw_eq0 h0
    simp at this; omega
  -- the number
  have h4 : ((pl.drop N).take 4).length = 4 := by simp; omega
  have hnum := readLE_take_lt (pl.drop N) 4
  let S4 (u : PancakeState σ) : Prop := S3 u ∧ u.locals "jnum" = some (BitVec.ofNat 64 (readLE ((pl.drop N).take 4)))
  have hS4c : Safe.ClockFree S4 := fun _ _ ⟨h1, h2⟩ => ⟨hS3c _ _ h1, h2⟩
  have s4f : Frag o (ScanProg.leS "jnum" (Syntax.eAdd (Syntax.v "jpp") (Syntax.v "ji")) 4)
      (fun u => S3 u ∧ eval u (.cmp .less (.var "jpl") (.op .add (.var "ji")
        (.const (BitVec.ofNat 64 4)))) = some 0) S4 := by
    refine frag_each o (lowK_any _ (k := .skip) (c := _) rfl) fun s ⟨hs, _⟩ => ?_
    have e := leS_frag o (x := "jnum") (p := Syntax.eAdd (Syntax.v "jpp") (Syntax.v "ji"))
      (P := .op .add (.var "jpp") (.var "ji")) rfl (s := s) (a := at_ A (sWindow + o' + 13) + BitVec.ofNat 64 N)
      (bs := (pl.drop N).take 4) (by omega)
      (fun w => by simp [eval, setL, setLocal, (dat_local hs.1.1.1 (by decide)).trans h.jpp, hs.1.1.2.2.2.2.1])
      (fun i hi => by
        rw [add_ofNat, dat_byte h hs.1.1.1 (N + i) (by simp at hi; omega)]
        simp [List.getElem_take, List.getElem_drop])
      (dat_bound h hs.1.1.1 (by decide))
    rw [h4] at e
    refine frag_conseq e (fun _ h => h) fun u hu => ?_
    rw [like_eq hu]
    refine hS4c _ _ ⟨⟨⟨mid_set _ s hs.1.1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _, by simp [setL, setLocal, hs.1.2]⟩, by simp [setL, setLocal, hs.2.1], hs.2.2⟩,
      by simp [setL, setLocal]⟩
  let S5 (u : PancakeState σ) : Prop :=
    S4 u ∧ u.memory (at_ A (sGroups + 24 * g + 16)) = BitVec.ofNat 64 (readLE ((pl.drop N).take 4))
  have hS5c : Safe.ClockFree S5 := fun _ _ ⟨h1, h2⟩ => ⟨hS4c _ _ h1, h2⟩
  have s5f : Frag o [.store (Syntax.atOff (Syntax.v "jgp") 16) (Syntax.v "jnum")] S4 S5 :=
    store_frag o (D := .op .add (.var "jgp") (.const (BitVec.ofNat 64 16))) (E := .var "jnum") rfl rfl hS5c
      fun u hu => by
        have e0 : at_ A (sGroups + 24 * g) ≠ at_ A (sGroups + 24 * g + 16) :=
          at_ne (by simp only [sGroups]; omega) (by simp only [sGroups]; omega) (by omega)
        have e8 : at_ A (sGroups + 24 * g + 8) ≠ at_ A (sGroups + 24 * g + 16) :=
          at_ne (by simp only [sGroups]; omega) (by simp only [sGroups]; omega) (by omega)
        exact ⟨at_ A (sGroups + 24 * g + 16), _, by simp only [eval, hu.1.2.1, at_add], hu.2,
          dom_at h hu.1.1.1.1.1.memaddrs (by omega) (by simp only [sGroups, ScanProg.size]; omega),
          ⟨⟨⟨mid_word _ u hu.1.1.1 16 (Or.inr (Or.inr rfl)) _, by simpa using hu.1.1.2⟩, hu.1.2.1,
            by simp only [if_neg e0]; exact hu.1.2.2.1, by simp only [if_neg e8]; exact hu.1.2.2.2⟩, hu.2⟩, by simp⟩
  let S6 (u : PancakeState σ) : Prop := Mn (N + 4) u ∧ u.locals "jgp" = some (at_ A (sGroups + 24 * g)) ∧
    u.memory (at_ A (sGroups + 24 * g)) = BitVec.ofNat 64 (o' + 13 + (r.2 + 1)) ∧
    u.memory (at_ A (sGroups + 24 * g + 8)) = BitVec.ofNat 64 (pl[r.2]).toNat ∧
    u.locals "jnum" = some (BitVec.ofNat 64 (readLE ((pl.drop N).take 4))) ∧
    u.memory (at_ A (sGroups + 24 * g + 16)) = BitVec.ofNat 64 (readLE ((pl.drop N).take 4))
  have hS6c : Safe.ClockFree S6 := fun _ _ ⟨h1, h2⟩ => ⟨hMnc _ _ _ h1, h2⟩
  have s6f : Frag o [.assign "ji" (Syntax.eAdd (Syntax.v "ji") (Syntax.n 4))] S5 S6 :=
    set_frag o (E := .op .add (.var "ji") (.const (BitVec.ofNat 64 4))) rfl hS6c fun u hu => ⟨_,
      eval_addc (e := .var "ji") 4 hu.1.1.1.1.2.2.2.2.1, ⟨_, hu.1.1.1.1.2.2.2.2.1⟩,
      ⟨mid_ji _ u hu.1.1.1.1 _ h3, by simp [setL, setLocal, hu.1.1.1.2]⟩, by simp [setL, setLocal, hu.1.1.2.1],
      hu.1.1.2.2.1, hu.1.1.2.2.2, by simp [setL, setLocal, hu.1.2], hu.2⟩
  -- the name's length and the number checked
  let gr : Group := ⟨(pl.drop (r.2 + 1)).take (pl[r.2]).toNat, readLE ((pl.drop N).take 4)⟩
  have hgrl : gr.name.length = (pl[r.2]).toNat := by simp [gr]; omega
  have hbd : bounded gr = (decide (1 ≤ (pl[r.2]).toNat) && decide ((pl[r.2]).toNat ≤ 64) &&
      decide (1 ≤ readLE ((pl.drop N).take 4)) && decide (readLE ((pl.drop N).take 4) < 2 ^ 31)) := by
    rw [bounded, hgrl]
  have hC4 : ∀ u, S6 u → eval u (.cmp .less (.const 0) (.op .add (.cmp .less (.const 0) (.op .add
      (.cmp .less (.var "jnl") (.const (BitVec.ofNat 64 1))) (.cmp .less (.const (BitVec.ofNat 64 64)) (.var "jnl"))))
      (.cmp .less (.const 0) (.op .add (.cmp .less (.var "jnum") (.const (BitVec.ofNat 64 1)))
        (.cmp .less (.const (BitVec.ofNat 64 (2 ^ 31 - 1))) (.var "jnum")))))) = some (bw (!bounded gr)) :=
    fun u hu => by
      have ej : eval u (.var "jnl") = some (BitVec.ofNat 64 (pl[r.2]).toNat) := hu.1.2
      have en : eval u (.var "jnum") = some (BitVec.ofNat 64 (readLE ((pl.drop N).take 4))) := hu.2.2.2.2.1
      rw [e_or2 (e_or2 (eval_lt (by omega) (by decide) ej rfl) (eval_lt (by decide) (by omega) rfl ej))
        (e_or2 (eval_lt (by omega) (by decide) en rfl) (eval_lt (by decide) (by omega) rfl en)), hbd]
      congr 2
      exact bounded_flags _ _
  have hone : bounded gr = true → oneGroup pl r.2 = some (gr, N + 4) := fun hb => by
    simp only [oneGroup]
    rw [if_neg (by omega), hgd, if_neg (by omega), if_neg (by omega), if_neg (by simpa [gr] using hb)]
  refine frag_append s4f (frag_append (xs := [_]) s5f (frag_append (xs := [_]) s6f ?_))
  refine frag_ite o (C := .cmp .less (.const 0) (.op .add (.cmp .less (.const 0) (.op .add
      (.cmp .less (.var "jnl") (.const (BitVec.ofNat 64 1))) (.cmp .less (.const (BitVec.ofNat 64 64)) (.var "jnl"))))
      (.cmp .less (.const 0) (.op .add (.cmp .less (.var "jnum") (.const (BitVec.ofNat 64 1)))
        (.cmp .less (.const (BitVec.ofNat 64 (2 ^ 31 - 1))) (.var "jnum")))))) rfl hfc
    (fun u hu => ⟨_, hC4 u hu⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
  · -- out of bounds
    refine fail_frag o h hfc fun u ⟨hu, hne⟩ => ⟨_, hu.1.1.1, ?_⟩
    rw [hC4 u hu] at hne
    have hb := bw_ne0 hne
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hb
    exact mid_fail _ u hu.1.1 (by
      simp only [oneGroup]
      rw [if_neg (by omega), hgd, if_neg (by omega), if_neg (by omega), if_pos (by simpa [gr] using hb)])
  · -- a group read
    rw [hC4 u hu] at h0
    have hb : bounded gr = true := by simpa using bw_eq0 h0
    have hsc : scanGroups pl (g + 1) (10 + mlOf pl) = some (r.1 ++ [gr], N + 4) := by
      rw [scanGroups_snoc, hr]; simp [hone hb]
    have hg1 : gokOf pl (g + 1) = true := by simp [gokOf, hokC, hsc]
    refine ⟨dat_jok hu.1.1.1 hg1.symm, hu.1.1.2.1, fun _ => ⟨by omega, hu.1.1.2.2.1, hu.1.1.2.2.2.1⟩,
      fun r' _ hr' => ?_⟩
    rw [hsc, Option.some.injEq] at hr'
    subst hr'
    refine ⟨hu.1.1.2.2.2.2.1, fun h' hh => ?_⟩
    simp only [List.length_append, List.length_singleton] at hh
    by_cases hlt : h' < r.1.length
    · rw [List.getElem_append_left hlt]; exact hu.1.1.2.2.2.2.2 h' hlt
    · have he : h' = r.1.length := by omega
      subst he
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      rw [hrl]
      exact ⟨r.2 + 1, hu.2.2.1, by rw [hgrl]; exact hu.2.2.2.1, hu.2.2.2.2.2, by rw [hgrl], by rw [hgrl]; omega⟩

/-- After the groups: the verdict, and with it where they end and their slots. -/
def DFacts (A : Word) (o' : Nat) (pl : Bytes) (u : PancakeState σ) : Prop :=
  ∀ r, gokOf pl (gcOf pl) = true → scanGroups pl (gcOf pl) (10 + mlOf pl) = some r →
    u.locals "ji" = some (BitVec.ofNat 64 r.2) ∧ u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧
    BFacts A o' pl u ∧ ∀ h (hh : h < r.1.length), SlotAt A o' pl h r.1[h] u

/-- **The groups**, each read into its slot, until one is not one or all are read. -/
theorem decD_frag (o : Oracle σ) (h : DecIn A o' pl s0) {fail : List Syntax.PStmt} (hfl : LowKK fail)
    (hfd : declared fail = []) :
    Frag o (ScanProg.groupsPart fail)
      (fun u => DAt A s0 (okCOf pl) u ∧ (10 + mlOf pl ≤ pl.length ∧ gcOf pl ≤ 16 →
        u.locals "ji" = some (BitVec.ofNat 64 (10 + mlOf pl)) ∧
        u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧ BFacts A o' pl u))
      (fun u => DAt A s0 (gokOf pl (gcOf pl)) u ∧ DFacts A o' pl u) := by
  have hokC : okCOf pl = true ↔ 10 + mlOf pl ≤ pl.length ∧ gcOf pl ≤ 16 := by simp [okCOf]
  have h0 : scanGroups pl 0 (10 + mlOf pl) = some ([], 10 + mlOf pl) := rfl
  have hg0 : gokOf pl 0 = okCOf pl := by simp [gokOf, h0]
  have f0 : Frag o [.assign "jgi" (lit 0)] (fun u => DAt A s0 (okCOf pl) u ∧ (10 + mlOf pl ≤ pl.length ∧
      gcOf pl ≤ 16 → u.locals "ji" = some (BitVec.ofNat 64 (10 + mlOf pl)) ∧
      u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧ BFacts A o' pl u)) (GInv A s0 o' pl 0 0) :=
    set_frag o (E := .op .add (.var "jz") (.const 0)) rfl ginv_clock fun u hu => by
      refine ⟨0, by simp [eval, (dat_local hu.1 (by decide)).trans h.jz], dat_bound h hu.1 (by decide),
        dat_jok (dat_set hu.1 (by decide) (by decide) (by decide) _) hg0.symm, by simp [setL, setLocal],
        fun hc => ?_, fun r _ hr => ?_⟩
      · obtain ⟨e1, e2, e3⟩ := hu.2 (hokC.mp hc)
        exact ⟨Nat.zero_le _, by simp [setL, setLocal, e2], ⟨by simp [setL, setLocal, e3.1],
          by simp [setL, setLocal, e3.2.1], e3.2.2⟩⟩
      · rw [h0, Option.some.injEq] at hr
        subst hr
        refine ⟨?_, fun h' hh => by simp at hh⟩
        have hc : okCOf pl = true := by rw [← hg0]; assumption
        simp [setL, setLocal, (hu.2 (hokC.mp hc)).1]
  have hlow : LowKK (groupBody fail) := lowKK_append (xs := [_]) (lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩))
    (lowK_any _ (k := .skip) (c := _) rfl)
  have hcond : ∀ i u, GInv A s0 o' pl i i u → eval u (.op .and_ (.var "jok") (.cmp .less (.var "jgi") (.var "jgc"))) =
      some (if (gokOf pl i && decide (i < gcOf pl)) then 1 else 0) := fun i u hu => by
    by_cases hc : okCOf pl = true
    · obtain ⟨hig, hjgc, -⟩ := hu.2.2.1 hc
      have hgc16 := ((hokC.mp hc).2)
      rw [eval_and (q := decide (i < gcOf pl)) (by simp only [eval]; exact hu.1.2.2)
        (eval_lt (by omega) (by omega) (by simp only [eval]; exact hu.2.1) (by simp only [eval]; exact hjgc))]
      rfl
    · have hg : gokOf pl i = false := by simp [gokOf, hc]
      obtain ⟨w, hw⟩ := dat_bound h hu.1 (show "jgc" ∈ decNames by decide)
      have hlt : eval u (.cmp .less (.var "jgi") (.var "jgc")) =
          some (bw (signedLt (BitVec.ofNat 64 i) w)) := by
        simp only [eval, hu.2.1, hw]; cases signedLt (BitVec.ofNat 64 i) w <;> rfl
      rw [eval_and (by simp only [eval]; exact hu.1.2.2) hlt, hg]
      rfl
  have fl := frag_count o (c := Syntax.eAnd (Syntax.v "jok") (Syntax.eLt (Syntax.v "jgi") (Syntax.v "jgc")))
    (C := .op .and_ (.var "jok") (.cmp .less (.var "jgi") (.var "jgc"))) rfl hlow (I := fun i => GInv A s0 o' pl i i)
    (fun _ => ginv_clock) (fun _ _ _ _ _ hy => by rw [show declared (groupBody fail) = [] from rfl] at hy; cases hy)
    hcond
    (fun i hi => decGroup_frag o h hfl hfd i hi) 0
  refine frag_append (xs := [_]) f0 (frag_conseq fl (fun _ h => h) fun u ⟨i, hu, hz⟩ => ⟨?_, fun r hg hr => ?_⟩)
  · -- the verdict once the loop ends
    by_cases hc : okCOf pl = true
    · obtain ⟨hig, -, -⟩ := hu.2.2.1 hc
      by_cases hgi : gokOf pl i = true
      · have hi : i = gcOf pl := by simp [hgi] at hz; omega
        subst hi; exact hu.1
      · have hgi' : gokOf pl i = false := by simpa using hgi
        have hnone : scanGroups pl i (10 + mlOf pl) = none := by
          simp only [gokOf, hc, Bool.true_and, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hgi'
          exact hgi'
        have : gokOf pl (gcOf pl) = false := by simp [gokOf, scanGroups_none hig hnone]
        exact dat_jok hu.1 (hgi'.trans this.symm)
    · have e1 : gokOf pl i = false := by simp [gokOf, hc]
      have e2 : gokOf pl (gcOf pl) = false := by simp [gokOf, hc]
      exact dat_jok hu.1 (e1.trans e2.symm)
  · -- all the groups read
    have hc : okCOf pl = true := by simp only [gokOf, Bool.and_eq_true] at hg; exact hg.1
    obtain ⟨hig, hjgc, hbf⟩ := hu.2.2.1 hc
    have hi : i = gcOf pl := by
      rcases Nat.lt_or_ge i (gcOf pl) with hlt | hge
      · exfalso
        have hgi : gokOf pl i = false := by simpa [hlt] using hz
        have hnone : scanGroups pl i (10 + mlOf pl) = none := by
          simp only [gokOf, hc, Bool.true_and, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hgi
          exact hgi
        rw [scanGroups_none hig hnone] at hr; cases hr
      · omega
    subst hi
    obtain ⟨hji, hsl⟩ := hu.2.2.2 r hg hr
    exact ⟨hji, hjgc, hbf, hsl⟩

/-! ### The numbers after the groups, and the commit's checks -/

/-- Where the groups end. -/
def kOf (pl : Bytes) : Nat := ((scanGroups pl (gcOf pl) (10 + mlOf pl)).map (·.2)).getD 0

/-- The header's size, the file's size and its CRC, four octets each after the groups. -/
def hsOf (pl : Bytes) : Nat := readLE ((pl.drop (kOf pl)).take 4)
/-- …the file's size… -/
def fsOf (pl : Bytes) : Nat := readLE ((pl.drop (kOf pl + 4)).take 4)
/-- …and its CRC. -/
def crcOf (pl : Bytes) : Nat := readLE ((pl.drop (kOf pl + 8)).take 4)

/-- A commit no correct store writes. -/
def badOf (pl : Bytes) : Bool :=
  decide (readLE (pl.take 8) = 0) || decide (mlOf pl < 1) || decide (250 < mlOf pl) || decide (gcOf pl < 1) ||
    decide (fsOf pl < hsOf pl)

/-- The verdict after the three numbers… -/
def okEOf (pl : Bytes) : Bool := gokOf pl (gcOf pl) && decide (kOf pl + 12 ≤ pl.length)
/-- …after the end, nothing after them… -/
def okFOf (pl : Bytes) : Bool := gokOf pl (gcOf pl) && decide (kOf pl + 12 = pl.length)
/-- …and after the checks of what a correct store writes. -/
def okGOf (pl : Bytes) : Bool := okFOf pl && !badOf pl

/-- What is known once the commit's numbers are read and checked. -/
def TFacts (A : Word) (o' : Nat) (pl : Bytes) (u : PancakeState σ) : Prop :=
  ∀ r, scanGroups pl (gcOf pl) (10 + mlOf pl) = some r →
    u.locals "ji" = some (BitVec.ofNat 64 (r.2 + 12)) ∧ u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧
    BFacts A o' pl u ∧ (∀ h (hh : h < r.1.length), SlotAt A o' pl h r.1[h] u) ∧
    u.locals "jhs" = some (BitVec.ofNat 64 (hsOf pl)) ∧ u.locals "jfs" = some (BitVec.ofNat 64 (fsOf pl)) ∧
    u.locals "jcrc" = some (BitVec.ofNat 64 (crcOf pl))

theorem TFacts.jgc {u : PancakeState σ} {r : List Group × Nat} (ht : TFacts A o' pl u)
    (hr : scanGroups pl (gcOf pl) (10 + mlOf pl) = some r) : u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) :=
  (ht r hr).2.1
theorem TFacts.b {u : PancakeState σ} {r : List Group × Nat} (ht : TFacts A o' pl u)
    (hr : scanGroups pl (gcOf pl) (10 + mlOf pl) = some r) : BFacts A o' pl u := (ht r hr).2.2.1
theorem TFacts.slots {u : PancakeState σ} {r : List Group × Nat} (ht : TFacts A o' pl u)
    (hr : scanGroups pl (gcOf pl) (10 + mlOf pl) = some r) :
    ∀ h (hh : h < r.1.length), SlotAt A o' pl h r.1[h] u := (ht r hr).2.2.2.1
theorem TFacts.jhs {u : PancakeState σ} {r : List Group × Nat} (ht : TFacts A o' pl u)
    (hr : scanGroups pl (gcOf pl) (10 + mlOf pl) = some r) : u.locals "jhs" = some (BitVec.ofNat 64 (hsOf pl)) :=
  (ht r hr).2.2.2.2.1
theorem TFacts.jfs {u : PancakeState σ} {r : List Group × Nat} (ht : TFacts A o' pl u)
    (hr : scanGroups pl (gcOf pl) (10 + mlOf pl) = some r) : u.locals "jfs" = some (BitVec.ofNat 64 (fsOf pl)) :=
  (ht r hr).2.2.2.2.2.1
theorem TFacts.jcrc {u : PancakeState σ} {r : List Group × Nat} (ht : TFacts A o' pl u)
    (hr : scanGroups pl (gcOf pl) (10 + mlOf pl) = some r) : u.locals "jcrc" = some (BitVec.ofNat 64 (crcOf pl)) :=
  (ht r hr).2.2.2.2.2.2

theorem kOf_eq {r : List Group × Nat} (hr : scanGroups pl (gcOf pl) (10 + mlOf pl) = some r) : kOf pl = r.2 := by
  simp [kOf, hr]

theorem lowKK_leS {x : String} {p : Syntax.PExpr} {E : PancakeExp} (hp : Lower.lowerExp p = some E) (k : Nat) :
    LowKK (ScanProg.leS x p k) := by
  rw [leS_eq]
  refine lowKK_append (xs := [_]) (lowKK_one rfl (a := .assign x (.const 0)) rfl) ?_
  induction k with
  | zero => exact fun k => ⟨k, rfl⟩
  | succ k ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]
    have hs : Lower.lowerStmt1 (leStep x p k) = some (.assign x (.op .or_ (.shiftL (.var x)
        (.const (BitVec.ofNat 64 8))) (.loadByte (if k = 0 then E else .op .add E (.const (BitVec.ofNat 64 k)))))) := by
      simp [leStep, Lower.lowerStmt1, Syntax.eOr, Syntax.v, Syntax.n, ScanProg.byte, Lower.lowerExp, atOff_lower hp k]
    exact lowKK_append (xs := [_]) (lowKK_one rfl hs) ih

/-- A number of four octets read at `jpp + off`, into `x`. -/
theorem num4_frag (o : Oracle σ) (h : DecIn A o' pl s0) {x : String} (hx : x ∈ decNames) {p : Syntax.PExpr}
    {E : PancakeExp} (hp : Lower.lowerExp p = some E) {j : Nat}
    (hj : j + 4 ≤ pl.length) {P : Assn σ} (hPc : Safe.ClockFree P) (hP : ∀ u, P u → DAt A s0 true u)
    (hE : ∀ u w, P u → eval (setL u x w) E = some (at_ A (sWindow + o' + 13) + BitVec.ofNat 64 j))
    (hPs : ∀ u w, P u → P (setL u x w)) :
    Frag o (ScanProg.leS x p 4) P
      (fun u => P u ∧ u.locals x = some (BitVec.ofNat 64 (readLE ((pl.drop j).take 4)))) := by
  refine frag_each o (lowKK_leS hp 4) fun s hs => ?_
  have e := leS_frag o (x := x) (p := p) (P := E) hp (s := s) (a := at_ A (sWindow + o' + 13) + BitVec.ofNat 64 j)
    (bs := (pl.drop j).take 4) (by simp; omega) (fun w => hE s w hs) (fun i hi => by
      rw [add_ofNat, dat_byte h (hP s hs) (j + i) (by simp at hi; omega)]
      simp [List.getElem_take, List.getElem_drop]) (dat_bound h (hP s hs) hx)
  rw [show ((pl.drop j).take 4).length = 4 by simp; omega] at e
  refine frag_conseq e (fun _ h => h) fun u hu => ?_
  rw [like_eq hu]
  exact ⟨hPc _ _ (hPs s _ hs), by simp [setL, setLocal]⟩

/-- **The commit's last numbers**: the header's and the file's sizes and the CRC. -/
theorem decE_frag (o : Oracle σ) (h : DecIn A o' pl s0) {fail : List Syntax.PStmt} (hfl : LowKK fail)
    (hfd : declared fail = []) :
    Frag o (ScanProg.tailPart fail)
      (fun u => DAt A s0 (gokOf pl (gcOf pl)) u ∧ DFacts A o' pl u)
      (fun u => DAt A s0 (okEOf pl) u ∧ (okEOf pl = true → TFacts A o' pl u)) := by
  have hn := nums
  have hl := h.len
  let Q (u : PancakeState σ) : Prop := DAt A s0 (okEOf pl) u ∧ (okEOf pl = true → TFacts A o' pl u)
  have hQc : Safe.ClockFree Q := fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩
  refine frag_append (xs := [_]) (kept_skip o hfl hfd (by omega)
    (fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩) fun u hu => by
      obtain ⟨n, hn', hle⟩ := hu.1.2.1; exact ⟨n, hn', hle⟩) ?_
  refine flagIf_frag o (lowK_any _ (k := .skip) (c := _) rfl) rfl hQc (fun u hu => hu.1.2.2) ?_
    (fun hb u hu => ⟨dat_jok hu.1 (by simp [okEOf, hb]), fun e => by simp [okEOf, hb] at e⟩)
  intro hg
  obtain ⟨r, hr⟩ : ∃ r, scanGroups pl (gcOf pl) (10 + mlOf pl) = some r := by
    simp only [gokOf, Bool.and_eq_true, Option.isSome_iff_exists] at hg; exact hg.2
  have hk := kOf_eq hr
  obtain ⟨hrl, hik, hkl⟩ := scanGroups_le hr
  have hrk : r.2 ≤ pl.length := by
    rcases Nat.eq_zero_or_pos (gcOf pl) with h0 | h0
    · rw [h0] at hr; simp [scanGroups] at hr; rw [← hr]
      have := (show okCOf pl = true by simp only [gokOf, Bool.and_eq_true] at hg; exact hg.1)
      simp [okCOf] at this; omega
    · exact hkl (by omega)
  let Tp (u : PancakeState σ) : Prop := DAt A s0 true u ∧ u.locals "ji" = some (BitVec.ofNat 64 r.2) ∧
    u.locals "jgc" = some (BitVec.ofNat 64 (gcOf pl)) ∧ BFacts A o' pl u ∧
    ∀ h (hh : h < r.1.length), SlotAt A o' pl h r.1[h] u
  have hTpc : Safe.ClockFree Tp := fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩
  have tp_set : ∀ u, Tp u → ∀ x, x ∈ ["jhs", "jfs", "jcrc"] → ∀ v, Tp (setL u x v) := fun u hu x hx v => by
    simp at hx
    rcases hx with rfl | rfl | rfl <;>
      exact ⟨dat_set hu.1 (by decide) (by decide) (by decide) v, by simp [setL, setLocal, hu.2.1],
        by simp [setL, setLocal, hu.2.2.1], bfacts_set hu.2.2.2.1 (by decide) (by decide) _, hu.2.2.2.2⟩
  have hC : ∀ u, (DAt A s0 (gokOf pl (gcOf pl)) u ∧ DFacts A o' pl u) → eval u (.cmp .less (.var "jpl")
      (.op .add (.var "ji") (.const (BitVec.ofNat 64 12)))) = some (bw (decide (pl.length < r.2 + 12))) :=
    fun u hu => eval_lt (by omega) (by omega) (dat_jpl h hu.1) (eval_addc (e := .var "ji") 12 (hu.2 r hg hr).1)
  refine frag_ite o (C := .cmp .less (.var "jpl") (.op .add (.var "ji") (.const (BitVec.ofNat 64 12)))) rfl hQc
    (fun u hu => ⟨_, hC u hu⟩) ?_ (noDecl _ rfl) ?_ (noDecl _ rfl)
  · refine fail_frag o h hQc fun u ⟨hu, hne⟩ => ⟨_, hu.1, ?_⟩
    rw [hC u hu] at hne
    have h' := bw_ne0 hne
    simp only [decide_eq_true_eq] at h'
    have he : okEOf pl = false := by simp [okEOf, hk]; omega
    exact ⟨dat_jok (dat_fail hu.1) he.symm, fun e => by rw [he] at e; cases e⟩
  refine frag_pure (r.2 + 12 ≤ pl.length) (fun u ⟨hu, h0⟩ => ?_) (lowK_any _ (k := .skip) (c := _) rfl) fun h12 => ?_
  · rw [hC u hu] at h0
    have := bw_eq0 h0
    simp at this; omega
  have hjpp : ∀ u, Tp u → ∀ x w, x ≠ "jpp" → x ≠ "ji" →
      (setL u x w).locals "jpp" = some (at_ A (sWindow + o' + 13)) ∧
      (setL u x w).locals "ji" = some (BitVec.ofNat 64 r.2) :=
    fun u hu x w h1 h2 => ⟨by simp [setL, setLocal, Ne.symm h1, (dat_local hu.1 (by decide)).trans h.jpp],
      by simp [setL, setLocal, Ne.symm h2, hu.2.1]⟩
  have f1 := num4_frag o h (x := "jhs") (by decide)
    (p := Syntax.eAdd (Syntax.v "jpp") (Syntax.v "ji")) (E := .op .add (.var "jpp") (.var "ji")) rfl (j := r.2)
    (by omega) hTpc (fun u hu => hu.1) (fun u w hu => by
      simp only [eval, (hjpp u hu "jhs" w (by decide) (by decide)).1, (hjpp u hu "jhs" w (by decide) (by decide)).2])
    (fun u w hu => tp_set u hu _ (by decide) w)
  have f2 := num4_frag o h (x := "jfs") (by decide)
    (p := Syntax.eAdd (Syntax.v "jpp") (Syntax.eAdd (Syntax.v "ji") (Syntax.n 4)))
    (E := .op .add (.var "jpp") (.op .add (.var "ji") (.const (BitVec.ofNat 64 4)))) rfl (j := r.2 + 4)
    (by omega) (P := fun u => Tp u ∧ u.locals "jhs" = some (BitVec.ofNat 64 (readLE ((pl.drop r.2).take 4))))
    (fun _ _ ⟨h1, h2⟩ => ⟨hTpc _ _ h1, h2⟩) (fun u hu => hu.1.1) (fun u w hu => by
      simp only [eval, (hjpp u hu.1 "jfs" w (by decide) (by decide)).1, (hjpp u hu.1 "jfs" w (by decide) (by decide)).2,
        ← BitVec.ofNat_add]) (fun u w hu => ⟨tp_set u hu.1 _ (by decide) w, by simp [setL, setLocal, hu.2]⟩)
  have f3 := num4_frag o h (x := "jcrc") (by decide)
    (p := Syntax.eAdd (Syntax.v "jpp") (Syntax.eAdd (Syntax.v "ji") (Syntax.n 8)))
    (E := .op .add (.var "jpp") (.op .add (.var "ji") (.const (BitVec.ofNat 64 8)))) rfl (j := r.2 + 8)
    (by omega) (P := fun u => (Tp u ∧ u.locals "jhs" = some (BitVec.ofNat 64 (readLE ((pl.drop r.2).take 4)))) ∧
      u.locals "jfs" = some (BitVec.ofNat 64 (readLE ((pl.drop (r.2 + 4)).take 4))))
    (fun _ _ ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨hTpc _ _ h1, h2⟩, h3⟩) (fun u hu => hu.1.1.1) (fun u w hu => by
      simp only [eval, (hjpp u hu.1.1 "jcrc" w (by decide) (by decide)).1,
        (hjpp u hu.1.1 "jcrc" w (by decide) (by decide)).2, ← BitVec.ofNat_add])
      (fun u w hu => ⟨⟨tp_set u hu.1.1 _ (by decide) w, by simp [setL, setLocal, hu.1.2]⟩,
          by simp [setL, setLocal, hu.2]⟩)
  have he : okEOf pl = true := by simp [okEOf, hg, hk]; omega
  refine frag_append (frag_append (frag_append (frag_conseq f1 (fun u hu => ?_) fun _ h => h) f2) f3) ?_
  · obtain ⟨hji, hjgc, hbf, hsl⟩ := hu.1.2 r hg hr
    exact ⟨dat_jok hu.1.1 hg, hji, hjgc, hbf, hsl⟩
  refine set_frag o (E := .op .add (.var "ji") (.const (BitVec.ofNat 64 12))) rfl hQc fun u hu => ⟨_,
    eval_addc (e := .var "ji") 12 hu.1.1.1.2.1, ⟨_, hu.1.1.1.2.1⟩, ?_, fun _ r' hr' => ?_⟩
  · exact dat_jok ⟨kept_set hu.1.1.1.1.1 (by decide) _, ⟨r.2 + 12, by simp [setL, setLocal], by omega⟩,
      by simp [setL, setLocal, hu.1.1.1.1.2.2]⟩ he.symm
  · rw [hr, Option.some.injEq] at hr'
    subst hr'
    refine ⟨by simp [setL, setLocal], by simp [setL, setLocal, hu.1.1.1.2.2.1],
      bfacts_set hu.1.1.1.2.2.2.1 (by decide) (by decide) _,
      hu.1.1.1.2.2.2.2, by simp [setL, setLocal, hu.1.1.2, hsOf, hk], by simp [setL, setLocal, hu.1.2, fsOf, hk],
      by simp [setL, setLocal, hu.2, crcOf, hk]⟩

theorem okF_okE {pl : Bytes} (h : okFOf pl = true) : okEOf pl = true := by
  simp only [okFOf, okEOf, Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact ⟨h.1, by omega⟩

/-- **Nothing after the numbers.** -/
theorem decF_frag (o : Oracle σ) (h : DecIn A o' pl s0) :
    Frag o ScanProg.exactPart
      (fun u => DAt A s0 (okEOf pl) u ∧ (okEOf pl = true → TFacts A o' pl u))
      (fun u => DAt A s0 (okFOf pl) u ∧ (okFOf pl = true → TFacts A o' pl u)) := by
  have hn := nums
  have hl := h.len
  let Q (u : PancakeState σ) : Prop := DAt A s0 (okFOf pl) u ∧ (okFOf pl = true → TFacts A o' pl u)
  have hQc : Safe.ClockFree Q := fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩
  have hC : ∀ u, (DAt A s0 (okEOf pl) u ∧ (okEOf pl = true → TFacts A o' pl u)) →
      eval u (.op .and_ (.var "jok") (.cmp .equal (.cmp .equal (.var "ji") (.var "jpl")) (.const 0))) =
        some (bw (okEOf pl && !okFOf pl)) := fun u hu => by
    obtain ⟨n, hn', hle⟩ := hu.1.2.1
    rw [eval_and (by simp only [eval]; exact hu.1.2.2) (e_ne (a := .var "ji") (x := n) (y := pl.length) (by omega)
      (by omega) hn' (dat_jpl h hu.1))]
    cases he : okEOf pl
    · rfl
    · obtain ⟨r, hr⟩ : ∃ r, scanGroups pl (gcOf pl) (10 + mlOf pl) = some r := by
        simp only [okEOf, gokOf, Bool.and_eq_true, Option.isSome_iff_exists] at he; exact he.1.2
      have hji := (hu.2 he r hr).1
      rw [hn'] at hji
      have hnk : n = r.2 + 12 := NatToDec.ofNat64_inj (by omega) (by
        have := (scanGroups_le hr).2.1; simp only [okEOf, decide_eq_true_eq, Bool.and_eq_true] at he
        rw [kOf_eq hr] at he; omega) (Option.some.inj hji)
      simp [okFOf, okEOf, kOf_eq hr] at he ⊢
      simp [he, hnk]
  refine frag_ite o (C := .op .and_ (.var "jok") (.cmp .equal (.cmp .equal (.var "ji") (.var "jpl")) (.const 0)))
    rfl hQc (fun u hu => ⟨_, hC u hu⟩) ?_ (noDecl _ rfl) (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
  · refine fail_frag o h hQc fun u ⟨hu, hne⟩ => ⟨_, hu.1, ?_⟩
    rw [hC u hu] at hne
    have h' := bw_ne0 hne
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
    exact ⟨dat_jok (dat_fail hu.1) h'.2.symm, fun e => by rw [h'.2] at e; cases e⟩
  · rw [hC u hu] at h0
    have h' := bw_eq0 h0
    cases hf : okFOf pl
    · exact ⟨dat_jok hu.1 (by
        cases he : okEOf pl
        · rfl
        · rw [he, hf] at h'; cases h'), fun e => by cases e⟩
    · exact ⟨dat_jok hu.1 (okF_okE hf), fun _ => hu.2 (okF_okE hf)⟩

theorem add_bw {u : PancakeState σ} {X Y : PancakeExp} {p q : Bool} (hx : eval u X = some (bw p))
    (hy : eval u Y = some (bw q)) : ∃ w, eval u (.op .add X Y) = some w :=
  ⟨bw p + bw q, by simp only [eval, hx, hy]⟩

/-- **The commit checked**: a sequence number, a Message-ID's and a count's bounds, the header within the file. -/
theorem decG_frag (o : Oracle σ) (h : DecIn A o' pl s0) :
    Frag o ScanProg.checkPart
      (fun u => DAt A s0 (okFOf pl) u ∧ (okFOf pl = true → TFacts A o' pl u))
      (fun u => DAt A s0 (okGOf pl) u ∧ (okGOf pl = true → TFacts A o' pl u)) := by
  have hn := nums
  have hl := h.len
  let Q (u : PancakeState σ) : Prop := DAt A s0 (okGOf pl) u ∧ (okGOf pl = true → TFacts A o' pl u)
  have hQc : Safe.ClockFree Q := fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩
  let BAD : PancakeExp := .cmp .less (.const 0) (.op .add (.cmp .less (.const 0) (.op .add
    (.cmp .equal (.var "jseq") (.const 0)) (.cmp .less (.var "jml") (.const (BitVec.ofNat 64 1)))))
    (.cmp .less (.const 0) (.op .add (.cmp .less (.const 0) (.op .add (.cmp .less (.const (BitVec.ofNat 64 250))
      (.var "jml")) (.cmp .less (.var "jgc") (.const (BitVec.ofNat 64 1))))) (.cmp .less (.var "jfs") (.var "jhs")))))
  have hC : ∀ u, (DAt A s0 (okFOf pl) u ∧ (okFOf pl = true → TFacts A o' pl u)) →
      eval u (.op .and_ (.var "jok") BAD) = some (bw (okFOf pl && badOf pl)) := fun u hu => by
    cases hf : okFOf pl
    · -- the verdict is no: the checks are only evaluated
      obtain ⟨a1, e1⟩ := dat_bound h hu.1 (show "jseq" ∈ decNames by decide)
      obtain ⟨a2, e2⟩ := dat_bound h hu.1 (show "jml" ∈ decNames by decide)
      obtain ⟨a3, e3⟩ := dat_bound h hu.1 (show "jgc" ∈ decNames by decide)
      obtain ⟨a4, e4⟩ := dat_bound h hu.1 (show "jfs" ∈ decNames by decide)
      obtain ⟨a5, e5⟩ := dat_bound h hu.1 (show "jhs" ∈ decNames by decide)
      obtain ⟨p1, c1⟩ := cmp_bw (u := u) (c := .equal) (l := .var "jseq") (r := .const 0) e1 rfl
      obtain ⟨p2, c2⟩ := cmp_bw (u := u) (c := .less) (l := .var "jml") (r := .const (BitVec.ofNat 64 1)) e2 rfl
      obtain ⟨p3, c3⟩ := cmp_bw (u := u) (c := .less) (l := .const (BitVec.ofNat 64 250)) (r := .var "jml") rfl e2
      obtain ⟨p4, c4⟩ := cmp_bw (u := u) (c := .less) (l := .var "jgc") (r := .const (BitVec.ofNat 64 1)) e3 rfl
      obtain ⟨p5, c5⟩ := cmp_bw (u := u) (c := .less) (l := .var "jfs") (r := .var "jhs") e4 e5
      obtain ⟨w1, d1⟩ := add_bw c1 c2
      obtain ⟨q1, o1⟩ := cmp_bw (u := u) (c := .less) (l := .const 0) rfl d1
      obtain ⟨w2, d2⟩ := add_bw c3 c4
      obtain ⟨q2, o2⟩ := cmp_bw (u := u) (c := .less) (l := .const 0) rfl d2
      obtain ⟨w3, d3⟩ := add_bw o2 c5
      obtain ⟨q3, o3⟩ := cmp_bw (u := u) (c := .less) (l := .const 0) rfl d3
      obtain ⟨w4, d4⟩ := add_bw o1 o3
      obtain ⟨q4, o4⟩ := cmp_bw (u := u) (c := .less) (l := .const 0) rfl d4
      rw [eval_and (by simp only [eval]; exact hu.1.2.2) o4, hf]
      rfl
    · obtain ⟨r, hr⟩ : ∃ r, scanGroups pl (gcOf pl) (10 + mlOf pl) = some r := by
        simp only [okFOf, gokOf, Bool.and_eq_true, Option.isSome_iff_exists] at hf; exact hf.1.2
      obtain ⟨-, hjgc, hbf, -, hhs, hfs, -⟩ := hu.2 hf r hr
      have hokC : okCOf pl = true := by simp only [okFOf, gokOf, Bool.and_eq_true] at hf; exact hf.1.1
      have hgc : gcOf pl ≤ 16 := by simp [okCOf] at hokC; exact hokC.2
      have hml : mlOf pl < 256 := (pl.getD 8 0).isLt
      have hseq := readLE_take_lt pl 8
      have hh4 := readLE_take_lt (pl.drop (kOf pl)) 4
      have hf4 := readLE_take_lt (pl.drop (kOf pl + 4)) 4
      rw [eval_and (by simp only [eval]; exact hu.1.2.2)
        (e_or2 (e_or2 (eval_eq (a := .var "jseq") hseq (by decide) hbf.jseq rfl)
        (eval_lt (a := .var "jml") (by omega) (by decide) hbf.1 rfl)) (e_or2 (e_or2
          (eval_lt (b := .var "jml") (by decide) (by omega) rfl hbf.1)
          (eval_lt (a := .var "jgc") (by omega) (by decide) hjgc rfl))
          (eval_lt (a := .var "jfs") (b := .var "jhs") (by simp only [fsOf]; omega) (by simp only [hsOf]; omega)
            hfs hhs)))]
      simp only [badOf, hf, Bool.true_and, Bool.or_assoc]
  refine frag_ite o (C := .op .and_ (.var "jok") BAD) rfl hQc (fun u hu => ⟨_, hC u hu⟩) ?_ (noDecl _ rfl)
    (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)
  · refine fail_frag o h hQc fun u ⟨hu, hne⟩ => ⟨_, hu.1, ?_⟩
    rw [hC u hu] at hne
    have h' := bw_ne0 hne
    have hg : okGOf pl = false := by simp only [okGOf]; simp only [Bool.and_eq_true] at h'; simp [h'.1, h'.2]
    exact ⟨dat_jok (dat_fail hu.1) hg.symm, fun e => by rw [hg] at e; cases e⟩
  · rw [hC u hu] at h0
    have h' := bw_eq0 h0
    cases hf : okFOf pl
    · have hg : okGOf pl = false := by simp [okGOf, hf]
      exact ⟨dat_jok hu.1 (hf.trans hg.symm), fun e => by rw [hg] at e; cases e⟩
    · rw [hf] at h'
      have hg : okGOf pl = true := by simp only [okGOf, hf]; simpa using h'
      exact ⟨dat_jok hu.1 (hf.trans hg.symm), fun _ => hu.2 hf⟩

/-! ### Names alike -/

theorem take_succ_eq {xs ys : Bytes} {x : Nat} (hx : x < xs.length) (hy : x < ys.length) :
    decide (xs.take (x + 1) = ys.take (x + 1)) = (decide (xs.take x = ys.take x) && decide (xs[x] = ys[x])) := by
  have hxs : xs.take (x + 1) = xs.take x ++ [xs[x]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hx]; rfl
  have hys : ys.take (x + 1) = ys.take x ++ [ys[x]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hy]; rfl
  rw [hxs, hys]
  by_cases e : xs.take x = ys.take x
  · rw [e]; simp only [List.append_cancel_left_eq, List.cons.injEq, and_true, decide_true, Bool.true_and]
  · simp only [e, decide_false, Bool.false_and, decide_eq_false_iff_not]
    intro h'
    exact e (List.append_inj_left' h' (by simp))

theorem lowKK_namesAlike {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.namesAlike fail) := by
  refine lowKK_append (xs := [_, _, _, _]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
  refine lowKK_append (xs := [_]) (lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)) ?_
  refine lowKK_ite rfl ?_ (fun k => ⟨k, rfl⟩)
  refine lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
  refine lowKK_append (xs := [_]) (lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)) ?_
  refine lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
  refine lowKK_append (xs := [_]) (lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)) ?_
  exact lowK_any _ (k := .skip) (c := _) rfl

/-- Group `a`'s and group `b`'s slots, each holding a group whose name is at most 64 octets. -/
structure TwoSlots (A : Word) (o' : Nat) (pl : Bytes) (a b : Nat) (ga gb : Group) (u : PancakeState σ) : Prop where
  sa : SlotAt A o' pl a ga u
  sb : SlotAt A o' pl b gb u
  ja : u.locals "ja" = some (BitVec.ofNat 64 a)
  jbb : u.locals "jbb" = some (BitVec.ofNat 64 b)

/-- **Two names compared**: `jeq` is one when group `a`'s name is group `b`'s. -/
theorem namesAlike_frag (o : Oracle σ) (h : DecIn A o' pl s0) {fail : List Syntax.PStmt} (hfl : LowKK fail)
    (hfd : declared fail = []) {a b : Nat} (ha : a < 16) (hb : b < 16) {ga gb : Group} (hla : ga.name.length ≤ 64)
    (hlb : gb.name.length ≤ 64) {P : Assn σ} (hPc : Safe.ClockFree P)
    (hK : ∀ u, P u → Kept decNames (FieldW A) s0 u) (hT : ∀ u, P u → TwoSlots A o' pl a b ga gb u)
    (hPs : ∀ u x v, P u → x ∈ ["jga", "jgb", "jeq", "jla", "jna", "jnb", "jx"] → P (setL u x v)) :
    Frag o (ScanProg.namesAlike fail) P (fun u => P u ∧ u.locals "jeq" = some (bw (decide (ga.name = gb.name)))) := by
  have hn := nums
  have hl := h.len
  have hroom := h.room
  have hlow := lowKK_namesAlike hfl
  refine frag_each o hlow fun u0 hu0 => ?_
  obtain ⟨sA, a0, a8, a16, ena, ela⟩ := (hT u0 hu0).sa
  obtain ⟨sB, b0, b8, b16, enb, elb⟩ := (hT u0 hu0).sb
  have hdm := fun x (hx8 : x % 8 = 0) (hx : x < ScanProg.size) => dom_at h (hK u0 hu0).memaddrs hx8 hx
  -- the run so far: `P`, the memory as it was
  let R (u : PancakeState σ) : Prop := P u ∧ u.memory = u0.memory ∧ u.memaddrs = u0.memaddrs ∧ u.be = u0.be
  have hRc : Safe.ClockFree R := fun _ _ ⟨h1, h2⟩ => ⟨hPc _ _ h1, h2⟩
  have r_set : ∀ u x v, R u → x ∈ ["jga", "jgb", "jeq", "jla", "jna", "jnb", "jx"] → R (setL u x v) :=
    fun u x v hu hx => ⟨hPs u x v hu.1 hx, hu.2⟩
  have hsp : ∀ u, R u → u.locals "jsc" = some A := fun u hu => ((hK u hu.1).locals "jsc" (by decide)).trans h.sp
  have hjz : ∀ u, R u → u.locals "jz" = some 0 := fun u hu => ((hK u hu.1).locals "jz" (by decide)).trans h.jz
  have hjw : ∀ u, R u → u.locals "jw" = some (at_ A sWindow) := fun u hu =>
    ((hK u hu.1).locals "jw" (by decide)).trans h.jw
  have hbd : ∀ u, R u → ∀ y ∈ decNames, ∃ v, u.locals y = some v := fun u hu y hy =>
    kept_has (hK u hu.1) (h.bound y hy)
  have hslot : ∀ g, g < 16 → ∀ u, R u → ∀ x, x ∈ ["ja", "jbb"] → u.locals x = some (BitVec.ofNat 64 g) →
      eval u (.op .add (.op .add (.var "jsc") (.const (BitVec.ofNat 64 sGroups)))
        (.mul (.var x) (.const (BitVec.ofNat 64 groupSlot)))) = some (at_ A (sGroups + 24 * g)) :=
      fun g _ u hu x _ hx =>
    by simp only [eval, hsp u hu, hx, groupSlot, ofNat_mul24, at_, add_ofNat]
  -- the slots' addresses, the zero verdict, the first length
  let R4 (u : PancakeState σ) : Prop := R u ∧ u.locals "jga" = some (at_ A (sGroups + 24 * a)) ∧
    u.locals "jgb" = some (at_ A (sGroups + 24 * b)) ∧ u.locals "jeq" = some (bw false) ∧
    u.locals "jla" = some (BitVec.ofNat 64 ga.name.length)
  have hR4c : Safe.ClockFree R4 := fun _ _ ⟨h1, h2⟩ => ⟨hRc _ _ h1, h2⟩
  have f1 : Frag o [.assign "jga" (ScanProg.slot "ja"), .assign "jgb" (ScanProg.slot "jbb"), .assign "jeq" (lit 0),
      .assign "jla" (.loadw 1 (Syntax.atOff (Syntax.v "jga") 8))] (Like u0) R4 := by
    refine frag_append (xs := [_]) (set_frag o (E := .op .add (.op .add (.var "jsc") (.const (BitVec.ofNat 64 sGroups)))
      (.mul (.var "ja") (.const (BitVec.ofNat 64 groupSlot)))) rfl
      (P' := fun u => R u ∧ u.locals "jga" = some (at_ A (sGroups + 24 * a)))
      (fun _ _ ⟨h1, h2⟩ => ⟨hRc _ _ h1, h2⟩) fun u hu => ?_) ?_
    · have hR : R u := by rw [like_eq hu]; exact hRc _ _ ⟨hu0, rfl, rfl, rfl⟩
      exact ⟨_, hslot a ha u hR "ja" (by decide) (by rw [hu.locals]; exact (hT u0 hu0).ja), hbd u hR "jga" (by decide),
        r_set u _ _ hR (by decide), by simp [setL, setLocal]⟩
    refine frag_append (xs := [_]) (set_frag o (E := .op .add (.op .add (.var "jsc") (.const (BitVec.ofNat 64 sGroups)))
      (.mul (.var "jbb") (.const (BitVec.ofNat 64 groupSlot)))) rfl
      (P' := fun u => (R u ∧ u.locals "jga" = some (at_ A (sGroups + 24 * a))) ∧
        u.locals "jgb" = some (at_ A (sGroups + 24 * b)))
      (fun _ _ ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨hRc _ _ h1, h2⟩, h3⟩) fun u hu => ?_) ?_
    · exact ⟨_, hslot b hb u hu.1 "jbb" (by decide) (hT u hu.1.1).jbb,
        hbd u hu.1 "jgb" (by decide), ⟨r_set u _ _ hu.1 (by decide), by simp [setL, setLocal, hu.2]⟩,
        by simp [setL, setLocal]⟩
    refine frag_append (xs := [_]) (set_frag o (E := .op .add (.var "jz") (.const 0)) rfl
      (P' := fun u => ((R u ∧ u.locals "jga" = some (at_ A (sGroups + 24 * a))) ∧
        u.locals "jgb" = some (at_ A (sGroups + 24 * b))) ∧ u.locals "jeq" = some (bw false))
      (fun _ _ ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ⟨⟨⟨hRc _ _ h1, h2⟩, h3⟩, h4⟩) fun u hu => ⟨0, by simp [eval, hjz u hu.1.1],
        hbd u hu.1.1 "jeq" (by decide), ⟨⟨r_set u _ _ hu.1.1 (by decide), by simp [setL, setLocal, hu.1.2]⟩,
          by simp [setL, setLocal, hu.2]⟩, by simp [setL, setLocal, bw]⟩) ?_
    refine set_frag o (E := .loadWord (.op .add (.var "jga") (.const (BitVec.ofNat 64 8)))) rfl hR4c fun u hu => ?_
    have hw : eval u (.op .add (.var "jga") (.const (BitVec.ofNat 64 8))) = some (at_ A (sGroups + 24 * a + 8)) := by
      simp only [eval, hu.1.1.2, at_add]
    have hd0 : u0.memaddrs (at_ A (sGroups + 24 * a + 8)) = true :=
      hdm _ (by simp only [sGroups]; omega) (by simp only [sGroups, ScanProg.size]; omega)
    have hd : u.memaddrs (at_ A (sGroups + 24 * a + 8)) = true := by rw [hu.1.1.1.2.2.1]; exact hd0
    have hmm : u.memory (at_ A (sGroups + 24 * a + 8)) = BitVec.ofNat 64 ga.name.length := by
      rw [hu.1.1.1.2.1]; exact a8
    have hm := eval_load hw hd hmm
    exact ⟨_, hm, hbd u hu.1.1.1 "jla" (by decide), r_set u _ _ hu.1.1.1 (by decide),
      by simp [setL, setLocal, hu.1.1.2],
      by simp [setL, setLocal, hu.1.2], by simp [setL, setLocal, hu.2], by simp [setL, setLocal]⟩
  have hk1 : Frag o [ScanProg.kept fail "jla" 64] R4 R4 :=
    kept_skip o hfl hfd (by decide) hR4c fun u hu => ⟨_, hu.2.2.2.2, hla⟩
  refine frag_append (xs := [_, _, _, _]) f1 (frag_append (xs := [_]) hk1 ?_)
  let Q (u : PancakeState σ) : Prop := P u ∧ u.locals "jeq" = some (bw (decide (ga.name = gb.name)))
  have hQc : Safe.ClockFree Q := fun _ _ ⟨h1, h2⟩ => ⟨hPc _ _ h1, h2⟩
  have hlb' : ∀ u, R4 u → eval u (.loadWord (.op .add (.var "jgb") (.const (BitVec.ofNat 64 8)))) =
      some (BitVec.ofNat 64 gb.name.length) := fun u hu => by
    have hw : eval u (.op .add (.var "jgb") (.const (BitVec.ofNat 64 8))) = some (at_ A (sGroups + 24 * b + 8)) := by
      simp only [eval, hu.2.2.1, at_add]
    have hd0 : u0.memaddrs (at_ A (sGroups + 24 * b + 8)) = true :=
      hdm _ (by simp only [sGroups]; omega) (by simp only [sGroups, ScanProg.size]; omega)
    have hd : u.memaddrs (at_ A (sGroups + 24 * b + 8)) = true := by rw [hu.1.2.2.1]; exact hd0
    have hmm : u.memory (at_ A (sGroups + 24 * b + 8)) = BitVec.ofNat 64 gb.name.length := by
      rw [hu.1.2.1]; exact b8
    exact eval_load hw hd hmm
  have hCe : ∀ u, R4 u → eval u (.cmp .equal (.var "jla") (.loadWord (.op .add (.var "jgb")
      (.const (BitVec.ofNat 64 8))))) = some (bw (decide (ga.name.length = gb.name.length))) := fun u hu =>
    eval_eq (by omega) (by omega) hu.2.2.2.2 (hlb' u hu)
  -- lengths differ: names differ
  have helse : ∀ u, R4 u ∧ eval u (.cmp .equal (.var "jla") (.loadWord (.op .add (.var "jgb")
      (.const (BitVec.ofNat 64 8))))) = some 0 → Q u := fun u ⟨hu, h0⟩ => by
    rw [hCe u hu] at h0
    have hne := bw_eq0 h0
    simp only [decide_eq_false_iff_not] at hne
    refine ⟨hu.1.1, ?_⟩
    rw [hu.2.2.2.1]
    have : decide (ga.name = gb.name) = false := by
      simp only [decide_eq_false_iff_not]; exact fun e => hne (by rw [e])
    rw [this]
  refine frag_ite o (C := .cmp .equal (.var "jla") (.loadWord (.op .add (.var "jgb")
    (.const (BitVec.ofNat 64 8))))) rfl hQc (fun u hu => ⟨_, hCe u hu⟩) ?_ (noDecl _ rfl)
    (frag_nil o helse) (noDecl _ rfl)
  refine frag_pure (ga.name.length = gb.name.length) (fun u ⟨hu, hne⟩ => by
    rw [hCe u hu] at hne; simpa using bw_ne0 hne) (by
      refine lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
      refine lowKK_append (xs := [_]) (lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)) ?_
      refine lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) ?_
      refine lowKK_append (xs := [_]) (lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)) ?_
      exact lowK_any _ (k := .skip) (c := _) rfl) fun hlen => ?_
  have hwA : o' + 13 + sA ≤ windowRoom := by omega
  have hwB : o' + 13 + sB ≤ windowRoom := by omega
  -- where the names lie, the verdict so far one, the count zero
  let R6 (u : PancakeState σ) : Prop := R u ∧ u.locals "jla" = some (BitVec.ofNat 64 ga.name.length) ∧
    u.locals "jna" = some (BitVec.ofNat 64 (o' + 13 + sA)) ∧ u.locals "jnb" = some (BitVec.ofNat 64 (o' + 13 + sB))
  have hR6c : Safe.ClockFree R6 := fun _ _ ⟨h1, h2⟩ => ⟨hRc _ _ h1, h2⟩
  have hwd : ∀ (u : PancakeState σ) x, R u → x % 8 = 0 → x < ScanProg.size → u.memaddrs (at_ A x) = true :=
    fun u x hu h8 hx => by rw [hu.2.2.1]; exact hdm x h8 hx
  have hga : ∀ u, R4 u → eval u (.loadWord (.var "jga")) = some (BitVec.ofNat 64 (o' + 13 + sA)) := fun u hu =>
    eval_load hu.2.1 (hwd u _ hu.1 (by simp only [sGroups]; omega) (by simp only [sGroups, ScanProg.size]; omega))
      (by rw [hu.1.2.1]; exact a0)
  have hgb : ∀ u, R4 u → eval u (.loadWord (.var "jgb")) = some (BitVec.ofNat 64 (o' + 13 + sB)) := fun u hu =>
    eval_load hu.2.2.1 (hwd u _ hu.1 (by simp only [sGroups]; omega) (by simp only [sGroups, ScanProg.size]; omega))
      (by rw [hu.1.2.1]; exact b0)
  let R5a (u : PancakeState σ) : Prop := R4 u ∧ u.locals "jna" = some (BitVec.ofNat 64 (o' + 13 + sA))
  let R5b (u : PancakeState σ) : Prop := R5a u ∧ u.locals "jnb" = some (BitVec.ofNat 64 (o' + 13 + sB))
  have hR5ac : Safe.ClockFree R5a := fun _ _ ⟨h1, h2⟩ => ⟨hR4c _ _ h1, h2⟩
  have hR5bc : Safe.ClockFree R5b := fun _ _ ⟨h1, h2⟩ => ⟨hR5ac _ _ h1, h2⟩
  have r4_set : ∀ u x v, R4 u → x ∈ ["jna", "jnb", "jx"] → R4 (setL u x v) := fun u x v hu hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl <;>
      exact ⟨r_set u _ v hu.1 (by decide), by simp [setL, setLocal, hu.2.1], by simp [setL, setLocal, hu.2.2.1],
        by simp [setL, setLocal, hu.2.2.2.1], by simp [setL, setLocal, hu.2.2.2.2]⟩
  have g1 : Frag o [.assign "jna" (.loadw 1 (Syntax.v "jga")), ScanProg.kept fail "jna" windowRoom,
      .assign "jnb" (.loadw 1 (Syntax.v "jgb")), ScanProg.kept fail "jnb" windowRoom]
      (fun u => R4 u ∧ eval u (.cmp .equal (.var "jla") (.loadWord (.op .add (.var "jgb")
        (.const (BitVec.ofNat 64 8))))) ≠ some 0) R5b := by
    refine frag_append (xs := [_]) (set_frag o (E := .loadWord (.var "jga")) rfl hR5ac fun u ⟨hu, _⟩ =>
      ⟨_, hga u hu, hbd u hu.1 "jna" (by decide), r4_set u _ _ hu (by decide), by simp [setL, setLocal]⟩) ?_
    refine frag_append (xs := [_]) (kept_skip o hfl hfd (by decide) hR5ac fun u hu => ⟨_, hu.2, hwA⟩) ?_
    refine frag_append (xs := [_]) (set_frag o (E := .loadWord (.var "jgb")) rfl hR5bc fun u hu =>
      ⟨_, hgb u hu.1, hbd u hu.1.1 "jnb" (by decide), ⟨r4_set u _ _ hu.1 (by decide), by simp [setL, setLocal, hu.2]⟩,
        by simp [setL, setLocal]⟩) ?_
    exact kept_skip o hfl hfd (by decide) hR5bc fun u hu => ⟨_, hu.2, hwB⟩
  refine frag_append (xs := [_, _, _, _]) g1 ?_
  -- the octets of the two names, compared one by one
  have hnA : ∀ x (hx : x < ga.name.length), ga.name[x] = pl[sA + x]'(by omega) := fun x hx => by
    rw [List.getElem_of_eq ena hx]; simp [List.getElem_take, List.getElem_drop]
  have hnB : ∀ x (hx : x < gb.name.length), gb.name[x] = pl[sB + x]'(by omega) := fun x hx => by
    rw [List.getElem_of_eq enb hx]; simp [List.getElem_take, List.getElem_drop]
  have hbyte : ∀ u, R u → ∀ s x (hsx : s + x < pl.length), memLoadByte u.memory u.memaddrs u.be
      (at_ A sWindow + BitVec.ofNat 64 (o' + 13 + s) + BitVec.ofNat 64 x) = some (pl[s + x]'(by omega)) :=
    fun u hu s x hsx => by
      rw [hu.2.1, hu.2.2.1, hu.2.2.2, at_add, at_add, show sWindow + (o' + 13 + s) + x = sWindow + o' + 13 + (s + x) by
        omega, kept_load (hK u0 hu0) (not_field h.hA (Or.inr (by omega)) (by omega))]
      exact h.payload (s + x) hsx
  let I (x : Nat) (u : PancakeState σ) : Prop := R6 u ∧ u.locals "jx" = some (BitVec.ofNat 64 x) ∧
    x ≤ ga.name.length ∧ u.locals "jeq" = some (bw (decide (ga.name.take x = gb.name.take x)))
  have hIc : ∀ x, Safe.ClockFree (I x) := fun _ _ _ ⟨h1, h2⟩ => ⟨hR6c _ _ h1, h2⟩
  have r6_set : ∀ u x v, R6 u → x ∈ ["jeq", "jx"] → R6 (setL u x v) := fun u x v hu hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;>
      exact ⟨r_set u _ v hu.1 (by decide), by simp [setL, setLocal, hu.2.1], by simp [setL, setLocal, hu.2.2.1],
        by simp [setL, setLocal, hu.2.2.2]⟩
  have g2 : Frag o [.assign "jeq" (lit 1), .assign "jx" (lit 0)] R5b (I 0) := by
    refine frag_append (xs := [_]) (set_frag o (E := .op .add (.var "jz") (.const 1)) rfl
      (P' := fun u => R6 u ∧ u.locals "jeq" = some 1) (fun _ _ ⟨h1, h2⟩ => ⟨hR6c _ _ h1, h2⟩) fun u hu =>
        ⟨1, by simp [eval, hjz u hu.1.1.1], hbd u hu.1.1.1 "jeq" (by decide), ⟨r_set u _ _ hu.1.1.1 (by decide),
          by simp [setL, setLocal, hu.1.1.2.2.2.2], by simp [setL, setLocal, hu.1.2], by simp [setL, setLocal, hu.2]⟩,
          by simp [setL, setLocal]⟩) ?_
    exact set_frag o (E := .op .add (.var "jz") (.const 0)) rfl (hIc 0) fun u hu => ⟨0, by simp [eval, hjz u hu.1.1],
      hbd u hu.1.1 "jx" (by decide), r6_set u _ _ hu.1 (by decide), by simp [setL, setLocal], Nat.zero_le _,
      by simp [setL, setLocal, hu.2, bw]⟩
  refine frag_append (xs := [_, _]) g2 ?_
  let CB : PancakeExp := .cmp .equal (.cmp .equal (.loadByte (.op .add (.op .add (.var "jw") (.var "jna")) (.var "jx")))
    (.loadByte (.op .add (.op .add (.var "jw") (.var "jnb")) (.var "jx")))) (.const 0)
  have hev : ∀ x u, I x u → ∀ (hx : x < ga.name.length), eval u CB =
      some (bw (decide ((ga.name[x]).toNat ≠ (gb.name[x]'(by omega)).toNat))) := fun x u hu hx => by
    have hxa : eval u (.loadByte (.op .add (.op .add (.var "jw") (.var "jna")) (.var "jx"))) =
        some (BitVec.ofNat 64 (ga.name[x]).toNat) := by
      simp only [eval, hjw u hu.1.1, hu.1.2.2.1, hu.2.1, hbyte u hu.1.1 sA x (by omega), Bytes.setWidth8_64, hnA x hx]
    have hxb : eval u (.loadByte (.op .add (.op .add (.var "jw") (.var "jnb")) (.var "jx"))) =
        some (BitVec.ofNat 64 (gb.name[x]'(by omega)).toNat) := by
      simp only [eval, hjw u hu.1.1, hu.1.2.2.2, hu.2.1, hbyte u hu.1.1 sB x (by omega), Bytes.setWidth8_64,
        hnB x (by omega)]
    exact e_ne (Nat.lt_trans (ga.name[x]).isLt (by decide)) (Nat.lt_trans (gb.name[x]'(by omega)).isLt (by decide))
      hxa hxb
  have hbody : ∀ x, decide (x < ga.name.length) = true → Frag o ScanProg.alikeOctet (I x) (I (x + 1)) :=
      fun x hx => by
    simp only [decide_eq_true_eq] at hx
    have hxb : x < gb.name.length := by omega
    have hstep := take_succ_eq hx hxb
    have hbe : decide ((ga.name[x]).toNat ≠ (gb.name[x]).toNat) = !decide (ga.name[x] = gb.name[x]) := by
      by_cases e : ga.name[x] = gb.name[x]
      · simp [e]
      · have : (ga.name[x]).toNat ≠ (gb.name[x]).toNat := fun h' => e (BitVec.eq_of_toNat_eq h')
        simp [e, this]
    let M (u : PancakeState σ) : Prop := R6 u ∧ u.locals "jx" = some (BitVec.ofNat 64 x) ∧
      u.locals "jeq" = some (bw (decide (ga.name.take (x + 1) = gb.name.take (x + 1))))
    have hMc : Safe.ClockFree M := fun _ _ ⟨h1, h2⟩ => ⟨hR6c _ _ h1, h2⟩
    refine frag_append (xs := [_]) (frag_ite o (C := CB) rfl hMc (fun u hu => ⟨_, hev x u hu hx⟩) ?_ (noDecl _ rfl)
      (frag_nil o fun u ⟨hu, h0⟩ => ?_) (noDecl _ rfl)) ?_
    · refine set_frag o (E := .op .add (.var "jz") (.const 0)) rfl hMc fun u ⟨hu, hne⟩ => ⟨0,
        by simp [eval, hjz u hu.1.1], ⟨_, hu.2.2.2⟩, r6_set u _ _ hu.1 (by decide), by simp [setL, setLocal, hu.2.1],
        ?_⟩
      rw [hev x u hu hx, hbe] at hne
      have hd := bw_ne0 hne
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hd
      rw [hstep, hd]
      simp [setL, setLocal, bw]
    · rw [hev x u hu hx, hbe] at h0
      have hd := bw_eq0 h0
      simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at hd
      exact ⟨hu.1, hu.2.1, by rw [hstep, hd, Bool.and_true]; exact hu.2.2.2⟩
    · exact set_frag o (E := .op .add (.var "jx") (.const 1)) rfl (hIc (x + 1)) fun u hu => ⟨_, eval_addc 1 hu.2.1,
        ⟨_, hu.2.1⟩, r6_set u _ _ hu.1 (by decide), by simp [setL, setLocal], by omega,
        by simp [setL, setLocal, hu.2.2]⟩
  have fl := frag_count o (c := Syntax.eLt (Syntax.v "jx") (Syntax.v "jla")) (C := .cmp .less (.var "jx") (.var "jla"))
    rfl (lowK_any _ (k := .skip) (c := _) rfl) hIc
    (fun _ _ _ _ _ hy => by rw [show declared ScanProg.alikeOctet = [] from rfl] at hy; cases hy)
    (g := fun x => decide (x < ga.name.length)) (fun x u hu => by
      rw [eval_lt (a := .var "jx") (b := .var "jla") (by omega) (by omega) hu.2.1 hu.1.2.1]; rfl) hbody 0
  refine frag_conseq fl (fun _ h => h) fun u ⟨x, hu, hz⟩ => ?_
  have hx : x = ga.name.length := by simp at hz; omega
  subst hx
  refine ⟨hu.1.1.1, ?_⟩
  rw [hu.2.2.2, List.take_length, hlen, List.take_length]

/-! ### No two names alike -/

/-- The names of the groups read. -/
def namesOf (pl : Bytes) : List Bytes :=
  ((scanGroups pl (gcOf pl) (10 + mlOf pl)).map fun r => r.1.map Group.name).getD []

/-- No group before `a` shares its name with a group after it. -/
def distOf (pl : Bytes) (a : Nat) : Bool :=
  decide (∀ i < a, ∀ j < (namesOf pl).length, i < j → (namesOf pl)[i]? ≠ (namesOf pl)[j]?)

/-- …and group `a`'s name is none of those from `a + 1` up to `b`. -/
def dist2Of (pl : Bytes) (a b : Nat) : Bool :=
  distOf pl a && decide (∀ j < b, a < j → (namesOf pl)[a]? ≠ (namesOf pl)[j]?)

theorem dist_zero (pl : Bytes) : distOf pl 0 = true := by simp [distOf]

theorem dist2_start (pl : Bytes) (a : Nat) : dist2Of pl a (a + 1) = distOf pl a := by
  simp only [dist2Of]
  have : decide (∀ j < a + 1, a < j → (namesOf pl)[a]? ≠ (namesOf pl)[j]?) = true := by
    simp only [decide_eq_true_eq]; intro j hj haj; omega
  rw [this, Bool.and_true]

theorem dist2_step (pl : Bytes) {a b : Nat} (hab : a < b) :
    dist2Of pl a (b + 1) = (dist2Of pl a b && decide ((namesOf pl)[a]? ≠ (namesOf pl)[b]?)) := by
  simp only [dist2Of, Bool.and_assoc]
  congr 1
  by_cases e : (namesOf pl)[a]? = (namesOf pl)[b]?
  · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.and_false, decide_eq_false_iff_not]
    intro hall; exact hall b (by omega) hab rfl
  · simp only [e, ne_eq, not_false_eq_true, decide_true, Bool.and_true]
    apply decide_eq_decide.mpr
    constructor
    · intro hall j hj haj; exact hall j (by omega) haj
    · intro hall j hj haj
      by_cases hjb : j = b
      · subst hjb; exact e
      · exact hall j (by omega) haj

theorem dist2_end (pl : Bytes) {a : Nat} (ha : a < (namesOf pl).length) :
    dist2Of pl a (namesOf pl).length = distOf pl (a + 1) := by
  simp only [dist2Of, distOf]
  rw [← Bool.decide_and]
  apply decide_eq_decide.mpr
  constructor
  · intro ⟨h1, h2⟩ i hi j hj hij
    by_cases e : i = a
    · subst e; exact h2 j hj hij
    · exact h1 i (by omega) j hj hij
  · intro h
    exact ⟨fun i hi j hj hij => h i (by omega) j hj hij, fun j hj haj => h a (by omega) j hj haj⟩

theorem dist_mono (pl : Bytes) {a b : Nat} (hab : a ≤ b) (h : distOf pl b = true) : distOf pl a = true := by
  simp only [distOf, decide_eq_true_eq] at h ⊢
  exact fun i hi j hj hij => h i (by omega) j hj hij

theorem dist_nodup (pl : Bytes) : distOf pl (namesOf pl).length = decide (namesOf pl).Nodup := by
  simp only [distOf]
  apply decide_eq_decide.mpr
  rw [List.Nodup, List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij e
    exact h i hi j hj hij (by rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, e])
  · intro h i hi j hj hij e
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at e
    exact h i j hi hj hij (Option.some.inj e)

theorem namesOf_eq {r : List Group × Nat} (hr : scanGroups pl (gcOf pl) (10 + mlOf pl) = some r) :
    namesOf pl = r.1.map Group.name := by simp [namesOf, hr]

/-- The inner loop over the names, group `a` against the groups from `b`. -/
def NJ (A : Word) (s0 : PancakeState σ) (o' : Nat) (pl : Bytes) (a b : Nat) (u : PancakeState σ) : Prop :=
  DAt A s0 (dist2Of pl a b) u ∧ u.locals "ja" = some (BitVec.ofNat 64 a) ∧
    u.locals "jbb" = some (BitVec.ofNat 64 b) ∧ TFacts A o' pl u

theorem nj_clock {a b : Nat} : Safe.ClockFree (NJ A s0 o' pl a b) :=
  fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩

theorem tfacts_set {u : PancakeState σ} (ht : TFacts A o' pl u) {x : String}
    (hx : x ∉ ["ji", "jgc", "jml", "jseq", "jhs", "jfs", "jcrc"]) (v : Value) : TFacts A o' pl (setL u x v) :=
  fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ht r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hx
    obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hx
    exact ⟨by simp [setL, setLocal, Ne.symm n1, h1], by simp [setL, setLocal, Ne.symm n2, h2],
      ⟨by simp [setL, setLocal, Ne.symm n3, h3.1], by simp [setL, setLocal, Ne.symm n4, h3.2.1], h3.2.2⟩, h4,
      by simp [setL, setLocal, Ne.symm n5, h5], by simp [setL, setLocal, Ne.symm n6, h6],
      by simp [setL, setLocal, Ne.symm n7, h7]⟩

/-- **One pair of names**: group `a`'s against group `b`'s; a pair alike makes the verdict no. -/
theorem decPair_frag (o : Oracle σ) (h : DecIn A o' pl s0) {fail : List Syntax.PStmt} (hfl : LowKK fail)
    (hfd : declared fail = []) {r : List Group × Nat} (hr : scanGroups pl (gcOf pl) (10 + mlOf pl) = some r)
    (hgc : gcOf pl ≤ 16) {a b : Nat} (hab : a < b) (hb : b < gcOf pl) :
    Frag o (ScanProg.pairBody fail)
      (NJ A s0 o' pl a b) (NJ A s0 o' pl a (b + 1)) := by
  obtain ⟨hrl, -, -⟩ := scanGroups_le hr
  have hbd := scanGroups_bounded hr
  have hal : a < r.1.length := by omega
  have hbl : b < r.1.length := by omega
  have hla : (r.1[a]).name.length ≤ 64 := by
    have := hbd _ (List.getElem_mem hal); simp [bounded] at this; omega
  have hlb : (r.1[b]).name.length ≤ 64 := by
    have := hbd _ (List.getElem_mem hbl); simp [bounded] at this; omega
  have hnm := namesOf_eq hr
  have hna : (namesOf pl)[a]? = some (r.1[a]).name := by rw [hnm]; simp [hal]
  have hnb : (namesOf pl)[b]? = some (r.1[b]).name := by rw [hnm]; simp [hbl]
  have fn := namesAlike_frag o h hfl hfd (a := a) (b := b) (by omega) (by omega) (ga := r.1[a]) (gb := r.1[b]) hla hlb
    (P := NJ A s0 o' pl a b) nj_clock (fun u hu => hu.1.1) (fun u hu => ⟨(hu.2.2.2.slots hr a hal),
      (hu.2.2.2.slots hr b hbl), hu.2.1, hu.2.2.1⟩) (fun u x v hu hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨dat_set hu.1 (by decide) (by decide) (by decide) v, by simp [setL, setLocal, hu.2.1],
            by simp [setL, setLocal, hu.2.2.1], tfacts_set hu.2.2.2 (by decide) v⟩)
  let M (u : PancakeState σ) : Prop := DAt A s0 (dist2Of pl a (b + 1)) u ∧ u.locals "ja" = some (BitVec.ofNat 64 a) ∧
    u.locals "jbb" = some (BitVec.ofNat 64 b) ∧ TFacts A o' pl u
  have hMc : Safe.ClockFree M := fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩
  have hstep := dist2_step pl hab
  rw [hna, hnb] at hstep
  have fi : Frag o [.ite (Syntax.v "jeq") [.assign "jok" (lit 0)] []]
      (fun u => NJ A s0 o' pl a b u ∧ u.locals "jeq" = some (bw (decide ((r.1[a]).name = (r.1[b]).name)))) M :=
    flagIf_frag o (lowK_any _ (k := .skip) (c := _) rfl) rfl hMc (fun u hu => hu.2) (fun he => by
      refine fail_frag o h hMc fun u hu => ⟨_, hu.1.1, ?_⟩
      have hd : dist2Of pl a (b + 1) = false := by
        rw [hstep]; simp only [decide_eq_true_eq] at he; simp [he]
      exact ⟨dat_jok (dat_fail hu.1.1) hd.symm, by simp [setL, setLocal, hu.1.2.1],
        by simp [setL, setLocal, hu.1.2.2.1],
        tfacts_set hu.1.2.2.2 (by decide) _⟩)
      (fun he u hu => by
        have hd : dist2Of pl a (b + 1) = dist2Of pl a b := by
          rw [hstep]; simp only [decide_eq_false_iff_not] at he; simp [he]
        exact ⟨dat_jok hu.1.1 hd.symm, hu.1.2.1, hu.1.2.2.1, hu.1.2.2.2⟩)
  refine frag_append fn (frag_append (xs := [_]) fi ?_)
  exact set_frag o (E := .op .add (.var "jbb") (.const 1)) rfl nj_clock fun u hu => ⟨_, eval_addc 1 hu.2.2.1,
    ⟨_, hu.2.2.1⟩, dat_set hu.1 (by decide) (by decide) (by decide) _, by simp [setL, setLocal, hu.2.1],
    by simp [setL, setLocal], tfacts_set hu.2.2.2 (by decide) _⟩

/-- The verdict once the names are compared: no two alike. -/
def okHOf (pl : Bytes) : Bool := okGOf pl && decide (namesOf pl).Nodup

/-- The outer loop over the names after `a` groups. -/
def NI (A : Word) (s0 : PancakeState σ) (o' : Nat) (pl : Bytes) (a : Nat) (u : PancakeState σ) : Prop :=
  DAt A s0 (okGOf pl && distOf pl a) u ∧ u.locals "ja" = some (BitVec.ofNat 64 a) ∧
    (okGOf pl = true → a ≤ gcOf pl ∧ TFacts A o' pl u)

theorem ni_clock {a : Nat} : Safe.ClockFree (NI A s0 o' pl a) :=
  fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩

/-- **No two names alike**: each group's name against those after it. -/
theorem decH_frag (o : Oracle σ) (h : DecIn A o' pl s0) {fail : List Syntax.PStmt} (hfl : LowKK fail)
    (hfd : declared fail = []) :
    Frag o (ScanProg.pairsPart fail)
      (fun u => DAt A s0 (okGOf pl) u ∧ (okGOf pl = true → TFacts A o' pl u))
      (fun u => DAt A s0 (okHOf pl) u ∧ (okHOf pl = true → TFacts A o' pl u)) := by
  -- the groups read, when the verdict so far holds
  have hgr : okGOf pl = true → ∃ r, scanGroups pl (gcOf pl) (10 + mlOf pl) = some r := fun hg => by
    simp only [okGOf, okFOf, gokOf, Bool.and_eq_true, Option.isSome_iff_exists] at hg; exact hg.1.1.2
  have hgc16 : okGOf pl = true → gcOf pl ≤ 16 := fun hg => by
    simp only [okGOf, okFOf, gokOf, okCOf, Bool.and_eq_true, decide_eq_true_eq] at hg; exact hg.1.1.1.2
  have hlen : okGOf pl = true → (namesOf pl).length = gcOf pl := fun hg => by
    obtain ⟨r, hr⟩ := hgr hg
    rw [namesOf_eq hr, List.length_map]; exact (scanGroups_le hr).1
  have f0 : Frag o [.assign "ja" (lit 0)] (fun u => DAt A s0 (okGOf pl) u ∧ (okGOf pl = true → TFacts A o' pl u))
      (NI A s0 o' pl 0) :=
    set_frag o (E := .op .add (.var "jz") (.const 0)) rfl ni_clock fun u hu => ⟨0,
      by simp [eval, (dat_local hu.1 (by decide)).trans h.jz], dat_bound h hu.1 (by decide),
      dat_jok (dat_set hu.1 (by decide) (by decide) (by decide) _) (by simp [dist_zero]), by simp [setL, setLocal],
      fun hg => ⟨Nat.zero_le _, tfacts_set (hu.2 hg) (by decide) _⟩⟩
  -- the body of the outer loop
  have hbody : ∀ a, (okGOf pl && distOf pl a && decide (a < gcOf pl)) = true →
      Frag o (ScanProg.pairRow fail) (NI A s0 o' pl a) (NI A s0 o' pl (a + 1)) := fun a hc => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hg, hd⟩, ha⟩ := hc
    obtain ⟨r, hr⟩ := hgr hg
    have h16 := hgc16 hg
    have f1 : Frag o [.assign "jbb" (Syntax.eAdd (Syntax.v "ja") (Syntax.n 1))] (NI A s0 o' pl a)
        (fun u => NJ A s0 o' pl a (a + 1) u ∧ a + 1 ≤ a + 1) :=
      set_frag o (E := .op .add (.var "ja") (.const 1)) rfl (fun _ _ ⟨h1, h2⟩ => ⟨nj_clock _ _ h1, h2⟩) fun u hu =>
        ⟨_, eval_addc 1 hu.2.1, dat_bound h hu.1 (by decide),
          ⟨dat_jok (dat_set hu.1 (by decide) (by decide) (by decide) _) (by rw [dist2_start, hg, hd]; rfl),
            by simp [setL, setLocal, hu.2.1], by simp [setL, setLocal], tfacts_set (hu.2.2 hg).2 (by decide) _⟩,
          Nat.le_refl _⟩
    let J (b : Nat) (u : PancakeState σ) : Prop := NJ A s0 o' pl a b u ∧ a + 1 ≤ b ∧ b ≤ gcOf pl
    have hJc : ∀ b, Safe.ClockFree (J b) := fun _ _ _ ⟨h1, h2⟩ => ⟨nj_clock _ _ h1, h2⟩
    have hinner : LowKK (ScanProg.pairBody fail) :=
      lowKK_append (lowKK_namesAlike hfl) (lowK_any _ (k := .skip) (c := _) rfl)
    have fl := frag_count o (c := Syntax.eLt (Syntax.v "jbb") (Syntax.v "jgc"))
      (C := .cmp .less (.var "jbb") (.var "jgc")) rfl
      (body := ScanProg.pairBody fail)
      hinner hJc
      (fun _ _ _ _ _ hy => by
        rw [show declared (ScanProg.pairBody fail) = [] from rfl] at hy; cases hy)
      (g := fun b => decide (b < gcOf pl)) (fun b u hu => by
        rw [eval_lt (a := .var "jbb") (b := .var "jgc") (by omega) (by omega) hu.1.2.2.1
          (hu.1.2.2.2.jgc hr)]; rfl)
      (fun b hb => by
        simp only [decide_eq_true_eq] at hb
        exact frag_pure (a < b) (fun u hu => by omega) hinner fun hab =>
          frag_conseq (decPair_frag o h hfl hfd hr h16 (a := a) (b := b) hab hb)
            (fun u hu => hu.1) (fun u hu => ⟨hu, by omega, by omega⟩)) (a + 1)
    have f1 : Frag o [.assign "jbb" (Syntax.eAdd (Syntax.v "ja") (Syntax.n 1))] (NI A s0 o' pl a) (J (a + 1)) :=
      frag_conseq f1 (fun _ h => h) fun u hu => ⟨hu.1, Nat.le_refl _, by omega⟩
    refine frag_append (xs := [_]) f1 (frag_append (xs := [_]) fl ?_)
    refine set_frag o (E := .op .add (.var "ja") (.const 1)) rfl ni_clock fun u ⟨b, hu, hz⟩ => ?_
    have hb : b = gcOf pl := by simp at hz; omega
    subst hb
    have hd2 : dist2Of pl a (gcOf pl) = (okGOf pl && distOf pl (a + 1)) := by
      rw [← hlen hg, dist2_end pl (by rw [hlen hg]; omega), hg, Bool.true_and]
    exact ⟨_, eval_addc 1 hu.1.2.1, ⟨_, hu.1.2.1⟩, dat_jok (dat_set hu.1.1 (by decide) (by decide) (by decide) _) hd2,
      by simp [setL, setLocal], fun _ => ⟨by omega, tfacts_set hu.1.2.2.2 (by decide) _⟩⟩
  have hcond : ∀ a u, NI A s0 o' pl a u → eval u (.op .and_ (.var "jok") (.cmp .less (.var "ja") (.var "jgc"))) =
      some (if (okGOf pl && distOf pl a && decide (a < gcOf pl)) then 1 else 0) := fun a u hu => by
    by_cases hg : okGOf pl = true
    · obtain ⟨r, hr⟩ := hgr hg
      have h16 := hgc16 hg
      obtain ⟨hag, ht⟩ := hu.2.2 hg
      rw [eval_and (q := decide (a < gcOf pl)) (by simp only [eval]; exact hu.1.2.2)
        (eval_lt (by omega) (by omega) (by simp only [eval]; exact hu.2.1) (by simp only [eval]; exact ht.jgc hr))]
      rfl
    · have hg' : okGOf pl = false := by simpa using hg
      obtain ⟨w, hw⟩ := dat_bound h hu.1 (show "jgc" ∈ decNames by decide)
      have hlt : eval u (.cmp .less (.var "ja") (.var "jgc")) = some (bw (signedLt (BitVec.ofNat 64 a) w)) := by
        simp only [eval, hu.2.1, hw]; cases signedLt (BitVec.ofNat 64 a) w <;> rfl
      rw [eval_and (by simp only [eval]; exact hu.1.2.2) hlt, hg']
      rfl
  have hlow : LowKK (ScanProg.pairRow fail) := lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowKK_append (xs := [_]) (lowKK_while rfl (lowKK_append (lowKK_namesAlike hfl)
      (lowK_any _ (k := .skip) (c := _) rfl))) (lowK_any _ (k := .skip) (c := _) rfl))
  have fl := frag_count o (c := Syntax.eAnd (Syntax.v "jok") (Syntax.eLt (Syntax.v "ja") (Syntax.v "jgc")))
    (C := .op .and_ (.var "jok") (.cmp .less (.var "ja") (.var "jgc"))) rfl hlow (I := NI A s0 o' pl)
    (fun _ => ni_clock) (fun _ _ _ _ _ hy => by
      rw [show declared (ScanProg.pairRow fail) = [] from rfl] at hy
      cases hy) hcond hbody 0
  refine frag_append (xs := [_]) f0 (frag_conseq fl (fun _ h => h) fun u ⟨a, hu, hz⟩ => ?_)
  by_cases hg : okGOf pl = true
  · obtain ⟨hag, ht⟩ := hu.2.2 hg
    by_cases hd : distOf pl a = true
    · have ha : a = gcOf pl := by simp [hg, hd] at hz; omega
      subst ha
      have hdn : distOf pl (gcOf pl) = decide (namesOf pl).Nodup := by rw [← hlen hg, dist_nodup]
      exact ⟨dat_jok hu.1 (by simp only [okHOf, hg, hdn, Bool.true_and]), fun _ => ht⟩
    · have hd' : distOf pl a = false := by simpa using hd
      have hnd : decide (namesOf pl).Nodup = false := by
        rw [← dist_nodup, hlen hg]
        cases e : distOf pl (gcOf pl)
        · rfl
        · rw [dist_mono pl hag e] at hd'; cases hd'
      have hh : okHOf pl = false := by simp only [okHOf, hnd, Bool.and_false]
      exact ⟨dat_jok hu.1 (by rw [hd', hh]; simp), fun e => by rw [hh] at e; cases e⟩
  · have hg' : okGOf pl = false := by simpa using hg
    have hh : okHOf pl = false := by simp only [okHOf, hg', Bool.false_and]
    exact ⟨dat_jok hu.1 (by rw [hg', hh]; simp), fun e => by rw [hh] at e; cases e⟩

/-! ### The commit -/

/-- The groups read. -/
def groupsOf (pl : Bytes) : List Group := ((scanGroups pl (gcOf pl) (10 + mlOf pl)).map (·.1)).getD []

/-- The commit the fields make. -/
def commitOf (pl : Bytes) : Commit :=
  ⟨readLE (pl.take 8), (pl.drop 9).take (mlOf pl), groupsOf pl, hsOf pl, fsOf pl, crcOf pl⟩

/-- **The verdicts are `scanCommit`'s.** -/
theorem scan_okH (pl : Bytes) : scanCommit pl = if okHOf pl = true then some (commitOf pl) else none := by
  unfold scanCommit
  by_cases h1 : pl.length < 9 + mlOf pl + 1
  · rw [show (pl.getD 8 0).toNat = mlOf pl from rfl, if_pos h1, if_neg]
    simp [okHOf, okGOf, okFOf, gokOf, okCOf]; omega
  rw [show (pl.getD 8 0).toNat = mlOf pl from rfl, if_neg h1, show (pl.getD (9 + mlOf pl) 0).toNat = gcOf pl from rfl]
  by_cases h2 : 16 < gcOf pl
  · rw [if_pos h2, if_neg]
    simp [okHOf, okGOf, okFOf, gokOf, okCOf]; omega
  rw [if_neg h2, show 10 + mlOf pl = 10 + mlOf pl from rfl]
  have hc : okCOf pl = true := by simp [okCOf]; omega
  cases hr : scanGroups pl (gcOf pl) (10 + mlOf pl) with
  | none =>
    rw [if_neg]; simp [okHOf, okGOf, okFOf, gokOf, hr]
  | some r =>
    obtain ⟨gs, k⟩ := r
    have hk : kOf pl = k := by simp [kOf, hr]
    have hg : groupsOf pl = gs := by simp [groupsOf, hr]
    have hn : namesOf pl = gs.map Group.name := by simp [namesOf, hr]
    simp only
    by_cases h3 : k + 12 ≠ pl.length
    · rw [if_pos h3, if_neg]; simp [okHOf, okGOf, okFOf, gokOf, hc, hr, hk]; omega
    rw [if_neg h3]
    have hf : okFOf pl = true := by simp [okFOf, gokOf, hc, hr, hk]; omega
    have hbad : badOf pl = decide (readLE (pl.take 8) = 0 ∨ mlOf pl < 1 ∨ 250 < mlOf pl ∨ gcOf pl < 1 ∨
        readLE ((pl.drop (k + 4)).take 4) < readLE ((pl.drop k).take 4)) := by
      simp [badOf, fsOf, hsOf, hk, Bool.or_assoc]
    by_cases h4 : readLE (pl.take 8) = 0 ∨ mlOf pl < 1 ∨ 250 < mlOf pl ∨ gcOf pl < 1 ∨
        readLE ((pl.drop (k + 4)).take 4) < readLE ((pl.drop k).take 4)
    · have hb : badOf pl = true := by rw [hbad]; exact decide_eq_true h4
      rw [if_pos h4, if_neg]; simp [okHOf, okGOf, hb]
    rw [if_neg h4]
    have hb : badOf pl = false := by rw [hbad]; exact decide_eq_false h4
    have hgg : okGOf pl = true := by simp [okGOf, hf, hb]
    by_cases h5 : (gs.map Group.name).Nodup
    · rw [if_pos h5, if_pos (by simp [okHOf, hgg, hn, h5])]
      simp [commitOf, hg, hsOf, fsOf, crcOf, hk]
    · rw [if_neg h5, if_neg (by simp [okHOf, hgg, hn, h5])]

/-- The commit `c`'s fields in the area: its sequence number, its Message-ID's place in the window and length. Also its
group count and their slots, the header's and the file's sizes and the CRC. -/
def CommitAt (A : Word) (o' : Nat) (pl : Bytes) (c : Commit) (u : PancakeState σ) : Prop :=
  u.memory (at_ A sSeq) = BitVec.ofNat 64 c.seq ∧ u.memory (at_ A sIdAt) = BitVec.ofNat 64 (o' + 13 + 9) ∧
    u.memory (at_ A sIdLen) = BitVec.ofNat 64 c.messageId.length ∧
    u.memory (at_ A sGroupCount) = BitVec.ofNat 64 c.groups.length ∧
    (∀ h (hh : h < c.groups.length), SlotAt A o' pl h c.groups[h] u) ∧
    u.memory (at_ A sHeader) = BitVec.ofNat 64 c.headerSize ∧
    u.memory (at_ A sFileSize) = BitVec.ofNat 64 c.fileSize ∧ u.memory (at_ A sCrc) = BitVec.ofNat 64 c.fileCrc

theorem tfacts_word {u : PancakeState σ} (ht : TFacts A o' pl u) {x : Nat} (hx : x < sGroups) (h1 : x ≠ sIdAt)
    (h2 : x ≠ sIdLen) (v : Word) :
    TFacts A o' pl { u with memory := fun k => if k = at_ A x then v else u.memory k } := fun r hr => by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := ht r hr
  have hbd := scanGroups_bounded hr
  obtain ⟨hrl, -, -⟩ := scanGroups_le hr
  exact ⟨e1, e2, bfacts_word e3 (by simp only [sGroups] at hx; omega) h1 h2 v, fun h' hh =>
    slot_word (e4 h' hh) (by simp only [sGroups] at hx; omega) (by omega) (by omega) (by omega)
      (by have := (pl.getD (9 + mlOf pl) 0).isLt; simp only [gcOf] at hrl; omega) v, e5, e6, e7⟩

/-- The reading with `jrec` set too. -/
def DAtR (A : Word) (s0 : PancakeState σ) (b : Bool) (u : PancakeState σ) : Prop :=
  Kept ("jrec" :: decNames) (FieldW A) s0 u ∧ Small u "ji" ∧ u.locals "jok" = some (bw b)

theorem datR_of {b : Bool} {u : PancakeState σ} (h : DAt A s0 b u) : DAtR A s0 b u :=
  ⟨kept_widen h.1 (fun _ hx => List.mem_cons_of_mem _ hx) fun _ h => h, h.2⟩

/-- What reading a commit leaves: the verdict, `jrec` as it was without a commit. With one, its type and the commit's
fields. -/
def DecOut (A : Word) (s0 : PancakeState σ) (o' : Nat) (pl : Bytes) (u : PancakeState σ) : Prop :=
  DAtR A s0 (okHOf pl) u ∧ (okHOf pl = false → u.locals "jrec" = s0.locals "jrec") ∧ (okHOf pl = true →
    u.locals "jrec" = some (BitVec.ofNat 64 commitType) ∧ CommitAt A o' pl (commitOf pl) u)

theorem decOut_clock : Safe.ClockFree (DecOut A s0 o' pl) :=
  fun _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩

/-- **The commit's fields written**, its verdict holding. -/
theorem decI_frag (o : Oracle σ) (h : DecIn A o' pl s0) :
    Frag o ScanProg.storePart
      (fun u => DAt A s0 (okHOf pl) u ∧ (okHOf pl = true → TFacts A o' pl u)) (DecOut A s0 o' pl) := by
  refine flagIf_frag o (lowK_any _ (k := .skip) (c := _) rfl) rfl decOut_clock (fun u hu => hu.1.2.2) ?_
    (fun hb u hu => ⟨datR_of hu.1, fun _ => hu.1.1.locals "jrec" (by decide), fun e => by rw [hb] at e; cases e⟩)
  intro hh
  obtain ⟨r, hr⟩ : ∃ r, scanGroups pl (gcOf pl) (10 + mlOf pl) = some r := by
    simp only [okHOf, okGOf, okFOf, gokOf, Bool.and_eq_true, Option.isSome_iff_exists] at hh; exact hh.1.1.1.2
  have hc : okCOf pl = true := by
    simp only [okHOf, okGOf, okFOf, gokOf, Bool.and_eq_true] at hh; exact hh.1.1.1.1
  have hml : 9 + mlOf pl ≤ pl.length := by simp [okCOf] at hc; omega
  have hgl : (groupsOf pl).length = gcOf pl := by simp [groupsOf, hr]; exact (scanGroups_le hr).1
  -- the facts after each store
  let F (n : Nat) (u : PancakeState σ) : Prop := DAtR A s0 true u ∧ TFacts A o' pl u ∧
    u.locals "jrec" = some (BitVec.ofNat 64 commitType) ∧
    (1 ≤ n → u.memory (at_ A sSeq) = BitVec.ofNat 64 (readLE (pl.take 8))) ∧
    (2 ≤ n → u.memory (at_ A sGroupCount) = BitVec.ofNat 64 (gcOf pl)) ∧
    (3 ≤ n → u.memory (at_ A sHeader) = BitVec.ofNat 64 (hsOf pl)) ∧
    (4 ≤ n → u.memory (at_ A sFileSize) = BitVec.ofNat 64 (fsOf pl)) ∧
    (5 ≤ n → u.memory (at_ A sCrc) = BitVec.ofNat 64 (crcOf pl))
  have hFc : ∀ n, Safe.ClockFree (F n) := fun _ _ _ ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨⟨{ h1 with }, h2, h3⟩, h4⟩
  -- a field stored: the frame, the facts so far, and the field itself kept
  have upd : ∀ (n x : Nat) (u : PancakeState σ) (v : Word), F n u → x % 8 = 0 → sType ≤ x → x < sGroups →
      x ≠ sIdAt → x ≠ sIdLen → (1 ≤ n → x ≠ sSeq) → (2 ≤ n → x ≠ sGroupCount) → (3 ≤ n → x ≠ sHeader) →
      (4 ≤ n → x ≠ sFileSize) → n < 5 → F n { u with memory := fun k => if k = at_ A x then v else u.memory k } :=
    fun n x u v hu h8 h1 h2 h3 h4 e1 e2 e3 e4 hn5 => by
      have ne : ∀ y, y < 2 ^ 63 → y ≠ x → at_ A y ≠ at_ A x := fun y hy hne =>
        at_ne (by omega) (by simp only [sGroups] at h2; omega) hne
      refine ⟨⟨kept_word hu.1.1 ⟨x, h1, by simp only [sGroups, sKey] at h2 ⊢; omega, rfl⟩ _, hu.1.2.1, hu.1.2.2⟩,
        tfacts_word hu.2.1 h2 h3 h4 v, hu.2.2.1, fun hn => ?_, fun hn => ?_, fun hn => ?_, fun hn => ?_,
        fun hn => absurd hn (by omega)⟩
      · show (if at_ A sSeq = at_ A x then v else u.memory (at_ A sSeq)) = _
        rw [if_neg (ne _ (by decide) (Ne.symm (e1 hn)))]; exact hu.2.2.2.1 hn
      · show (if at_ A sGroupCount = at_ A x then v else u.memory (at_ A sGroupCount)) = _
        rw [if_neg (ne _ (by decide) (Ne.symm (e2 hn)))]; exact hu.2.2.2.2.1 hn
      · show (if at_ A sHeader = at_ A x then v else u.memory (at_ A sHeader)) = _
        rw [if_neg (ne _ (by decide) (Ne.symm (e3 hn)))]; exact hu.2.2.2.2.2.1 hn
      · show (if at_ A sFileSize = at_ A x then v else u.memory (at_ A sFileSize)) = _
        rw [if_neg (ne _ (by decide) (Ne.symm (e4 hn)))]; exact hu.2.2.2.2.2.2.1 hn
  have hjsc : ∀ (u : PancakeState σ), DAtR A s0 true u → ∀ x, eval u (.op .add (.var "jsc")
      (.const (BitVec.ofNat 64 x))) = some (at_ A x) := fun u hu x => by
    simp [eval, (hu.1.locals "jsc" (by decide)).trans h.sp, at_]
  have f0 : Frag o [.assign "jrec" (lit commitType)] (fun u => DAt A s0 (okHOf pl) u ∧
      (okHOf pl = true → TFacts A o' pl u)) (F 0) :=
    set_frag o (E := .op .add (.var "jz") (.const (BitVec.ofNat 64 commitType))) rfl (hFc 0) fun u hu =>
      ⟨BitVec.ofNat 64 commitType, by simp [eval, (dat_local hu.1 (by decide)).trans h.jz],
      kept_has hu.1.1 h.jrec,
      ⟨kept_set (datR_of (dat_jok hu.1 hh)).1 (by decide) _, by
        obtain ⟨n, hn', hl'⟩ := hu.1.2.1; exact ⟨n, by simp [setL, setLocal, hn'], hl'⟩,
        by simp [setL, setLocal, (dat_jok hu.1 hh).2.2]⟩, tfacts_set (hu.2 hh) (by decide) _,
      by simp [setL, setLocal], fun e => absurd e (by omega), fun e => absurd e (by omega),
      fun e => absurd e (by omega), fun e => absurd e (by omega), fun e => absurd e (by omega)⟩
  have hgcl : gcOf pl < 2 ^ 63 := Nat.lt_trans (pl.getD (9 + mlOf pl) 0).isLt (by decide)
  have f1 : Frag o [ScanProg.setw sSeq (Syntax.v "jseq")] (F 0) (F 1) :=
    store_frag o (D := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sSeq))) (E := .var "jseq") rfl rfl (hFc 1)
      fun u hu => by
        have e := upd 0 sSeq u (BitVec.ofNat 64 (readLE (pl.take 8))) hu (by decide) (by decide) (by decide)
          (by decide) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
        exact ⟨_, _, hjsc u hu.1 _, (hu.2.1.b hr).jseq, dom_at h hu.1.1.memaddrs (by decide) (by decide),
          e.1, e.2.1, e.2.2.1, fun _ => by simp, fun e' => absurd e' (by omega), fun e' => absurd e' (by omega),
          fun e' => absurd e' (by omega), fun e' => absurd e' (by omega)⟩
  have f2 : Frag o [ScanProg.setw sGroupCount (Syntax.v "jgc")] (F 1) (F 2) :=
    store_frag o (D := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sGroupCount))) (E := .var "jgc") rfl rfl (hFc 2)
      fun u hu => by
        have e := upd 1 sGroupCount u (BitVec.ofNat 64 (gcOf pl)) hu (by decide) (by decide) (by decide)
          (by decide) (by decide) (fun _ => by decide) (by omega) (by omega) (by omega) (by omega)
        exact ⟨_, _, hjsc u hu.1 _, hu.2.1.jgc hr, dom_at h hu.1.1.memaddrs (by decide) (by decide),
          e.1, e.2.1, e.2.2.1, fun _ => e.2.2.2.1 (by omega), fun _ => by simp, fun e' => absurd e' (by omega),
          fun e' => absurd e' (by omega), fun e' => absurd e' (by omega)⟩
  have f3 : Frag o [ScanProg.setw sHeader (Syntax.v "jhs")] (F 2) (F 3) :=
    store_frag o (D := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sHeader))) (E := .var "jhs") rfl rfl (hFc 3)
      fun u hu => by
        have e := upd 2 sHeader u (BitVec.ofNat 64 (hsOf pl)) hu (by decide) (by decide) (by decide)
          (by decide) (by decide) (fun _ => by decide) (fun _ => by decide) (by omega) (by omega) (by omega)
        exact ⟨_, _, hjsc u hu.1 _, hu.2.1.jhs hr, dom_at h hu.1.1.memaddrs (by decide) (by decide),
          e.1, e.2.1, e.2.2.1, fun _ => e.2.2.2.1 (by omega), fun _ => e.2.2.2.2.1 (by omega), fun _ => by simp,
          fun e' => absurd e' (by omega), fun e' => absurd e' (by omega)⟩
  have f4 : Frag o [ScanProg.setw sFileSize (Syntax.v "jfs")] (F 3) (F 4) :=
    store_frag o (D := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sFileSize))) (E := .var "jfs") rfl rfl (hFc 4)
      fun u hu => by
        have e := upd 3 sFileSize u (BitVec.ofNat 64 (fsOf pl)) hu (by decide) (by decide) (by decide)
          (by decide) (by decide) (fun _ => by decide) (fun _ => by decide) (fun _ => by decide) (by omega) (by omega)
        exact ⟨_, _, hjsc u hu.1 _, hu.2.1.jfs hr, dom_at h hu.1.1.memaddrs (by decide) (by decide),
          e.1, e.2.1, e.2.2.1, fun _ => e.2.2.2.1 (by omega), fun _ => e.2.2.2.2.1 (by omega),
          fun _ => e.2.2.2.2.2.1 (by omega), fun _ => by simp, fun e' => absurd e' (by omega)⟩
  have f5 : Frag o [ScanProg.setw sCrc (Syntax.v "jcrc")] (F 4) (F 5) :=
    store_frag o (D := .op .add (.var "jsc") (.const (BitVec.ofNat 64 sCrc))) (E := .var "jcrc") rfl rfl (hFc 5)
      fun u hu => by
        have e := upd 4 sCrc u (BitVec.ofNat 64 (crcOf pl)) hu (by decide) (by decide) (by decide)
          (by decide) (by decide) (fun _ => by decide) (fun _ => by decide) (fun _ => by decide) (fun _ => by decide)
          (by omega)
        exact ⟨_, _, hjsc u hu.1 _, hu.2.1.jcrc hr, dom_at h hu.1.1.memaddrs (by decide) (by decide),
          e.1, e.2.1, e.2.2.1, fun _ => e.2.2.2.1 (by omega), fun _ => e.2.2.2.2.1 (by omega),
          fun _ => e.2.2.2.2.2.1 (by omega), fun _ => e.2.2.2.2.2.2.1 (by omega), fun _ => by simp⟩
  refine frag_append (xs := [_]) f0 (frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2
    (frag_append (xs := [_]) f3 (frag_append (xs := [_]) f4 (frag_conseq f5 (fun _ h => h) fun u hu => ?_)))))
  obtain ⟨-, hjgc, hbf, hsl, -, -, -⟩ := hu.2.1 r hr
  have hgs : groupsOf pl = r.1 := by simp [groupsOf, hr]
  refine ⟨⟨hu.1.1, hu.1.2.1, by rw [hu.1.2.2, hh]⟩, fun e => by simp [hh] at e,
    fun _ => ⟨hu.2.2.1, hu.2.2.2.1 (by omega), hbf.idAt, ?_, ?_, ?_,
    hu.2.2.2.2.2.1 (by omega), hu.2.2.2.2.2.2.1 (by omega), hu.2.2.2.2.2.2.2 (by omega)⟩⟩
  · rw [hbf.idLen]; simp [commitOf]; congr 1; omega
  · rw [hu.2.2.2.2.1 (by omega)]; simp [commitOf, hgl]
  · intro g hg
    simp only [commitOf, hgs] at hg ⊢
    exact hsl g hg

/-- **The scanner's reading of a commit is `scanCommit`.** If it goes on, `jok` is one when the payload holds a commit a
correct store writes. Then `jrec` is the commit's type and the area holds its fields. -/
theorem decode_frag (o : Oracle σ) (h : DecIn A o' pl s0) {fail : List Syntax.PStmt} (hfl : LowKK fail)
    (hfd : declared fail = []) : Frag o (ScanProg.decode fail) (Like s0) (DecOut A s0 o' pl) :=
  frag_append (frag_append (frag_append (frag_append (frag_append (frag_append (frag_append (frag_append
    (decA_frag o h) (decB_frag o h)) (decC_frag o h)) (decD_frag o h hfl hfd)) (decE_frag o h hfl hfd))
    (decF_frag o h)) (decG_frag o h)) (decH_frag o h hfl hfd)) (decI_frag o h)

/-- …and that commit is `scanCommit`'s, so `decodeCommit`'s. -/
theorem decOut_commit {u : PancakeState σ} (hu : DecOut A s0 o' pl u) :
    u.locals "jok" = some (bw (decodeCommit pl).isSome) ∧ ∀ c, decodeCommit pl = some c →
      u.locals "jrec" = some (BitVec.ofNat 64 commitType) ∧ CommitAt A o' pl c u := by
  have e := scan_okH pl
  rw [scanCommit_eq] at e
  refine ⟨by rw [hu.1.2.2, e]; cases okHOf pl <;> rfl, fun c hc => ?_⟩
  rw [e] at hc
  cases hh : okHOf pl
  · rw [hh] at hc; cases hc
  · rw [hh, if_pos rfl, Option.some.injEq] at hc
    subst hc
    exact hu.2.2 hh

/-- …and its Message-ID is the payload's octets after the sequence number and the count. They lie in the window at the
place `CommitAt` gives. -/
theorem id_octets {c : Commit} (hc : decodeCommit pl = some c) :
    c.messageId = (pl.drop 9).take c.messageId.length ∧ 9 + c.messageId.length ≤ pl.length := by
  have e := scan_okH pl
  rw [scanCommit_eq] at e
  rw [e] at hc
  split at hc
  · rename_i hok
    cases hc
    have hok' : okCOf pl = true := by simp [okHOf, okGOf, okFOf, gokOf] at hok; exact hok.1.1.1.1
    simp [okCOf] at hok'
    exact ⟨by simp [commitOf], by simp [commitOf]; omega⟩
  · cases hc

/-- The reading of a commit lowers before anything when `fail` does. -/
theorem lowKK_decode {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (ScanProg.decode fail) := by
  have hk : ∀ x hi, LowKK [ScanProg.kept fail x hi] := fun x hi => lowKK_ite rfl hfl (fun k => ⟨k, rfl⟩)
  have hany : ∀ {xs : List Syntax.PStmt} (c : PancakeProg), Block.lowerK xs .skip = some c → LowKK xs :=
    fun c hc => lowK_any _ hc
  have hgroups : LowKK (ScanProg.groupsPart fail) := lowKK_append (xs := [_]) (hany _ rfl)
    (lowKK_while rfl (lowKK_append (xs := [_]) (hk _ _) (hany _ rfl)))
  have htail : LowKK (ScanProg.tailPart fail) := lowKK_append (xs := [_]) (hk _ _) (hany _ rfl)
  have hpairs : LowKK (ScanProg.pairsPart fail) := lowKK_append (xs := [_]) (hany _ rfl)
    (lowKK_while rfl (lowKK_append (xs := [_]) (hany _ rfl) (lowKK_append (xs := [_])
      (lowKK_while rfl (lowKK_append (lowKK_namesAlike hfl) (hany _ rfl))) (hany _ rfl))))
  exact lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append
    (lowKK_append (hany _ rfl) (hany _ rfl)) (hany _ rfl)) hgroups) htail) (hany _ rfl)) (hany _ rfl)) hpairs)
    (hany _ rfl)

end Decode

/-- A commit's groups are sixteen at most. -/
theorem decode_groups {pl : Bytes} {c : Commit} (h : decodeCommit pl = some c) : c.groups.length ≤ 16 := by
  have e := scan_okH pl
  rw [scanCommit_eq] at e
  rw [e] at h
  split at h
  · rename_i hok
    cases h
    have hc : okCOf pl = true := by simp [okHOf, okGOf, okFOf, gokOf] at hok; exact hok.1.1.1.1
    have hgl : (groupsOf pl).length = gcOf pl := by
      obtain ⟨a, b, hr⟩ : ∃ a b, scanGroups pl (gcOf pl) (10 + mlOf pl) = some (a, b) := by
        simp [okHOf, okGOf, okFOf, gokOf, Option.isSome_iff_exists] at hok; exact hok.1.1.1.2
      simp [groupsOf, hr]; exact (scanGroups_le hr).1
    simp [okCOf] at hc
    simp only [commitOf]; omega
  · cases h

/-- A commit's fields kept where only other words changed. -/
theorem commitAt_of {A : Word} {o' : Nat} {pl : Bytes} {c : Commit} {u u' : PancakeState σ}
    (hc : CommitAt A o' pl c u) (hg : c.groups.length ≤ 16)
    (h : ∀ x, sSeq ≤ x → x < sKey → x % 8 = 0 → u'.memory (at_ A x) = u.memory (at_ A x)) : CommitAt A o' pl c u' := by
  have hn := nums
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hc
  have k : ∀ x, sSeq ≤ x → x < sKey → x % 8 = 0 → ∀ v, u.memory (at_ A x) = v → u'.memory (at_ A x) = v :=
    fun x a b c v e => (h x a b c).trans e
  refine ⟨k _ (by decide) (by decide) (by decide) _ h1, k _ (by decide) (by decide) (by decide) _ h2,
    k _ (by decide) (by decide) (by decide) _ h3, k _ (by decide) (by decide) (by decide) _ h4, fun g hgl => ?_,
    k _ (by decide) (by decide) (by decide) _ h6, k _ (by decide) (by decide) (by decide) _ h7,
    k _ (by decide) (by decide) (by decide) _ h8⟩
  obtain ⟨s, e1, e2, e3, e4, e5⟩ := h5 g hgl
  have hs := Nat.lt_of_lt_of_le hgl hg
  have b1 : sSeq ≤ sGroups + 24 * g := by simp only [sSeq, sGroups]; omega
  have hg16 : sGroups = 136 := rfl
  exact ⟨s, k _ b1 (by omega) (by omega) _ e1, k _ (by simp only [sSeq]; omega) (by omega) (by omega) _ e2,
    k _ (by simp only [sSeq]; omega) (by omega) (by omega) _ e3, e4, e5⟩

end DN.News.ScanRun
