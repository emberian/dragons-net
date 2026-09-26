-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Dsl.Action
import DN.Compiler.Bytes
import DN.Compiler.Clock

/-!
# DN.Dsl.Correct

The compiled code of every action does what `Act.run` says (`Act.compile_run`), and the
exported function built from it returns the reply's length with the reply in the output buffer
and nothing else changed, or refuses before writing anything (`respond_correct`,
`respond_refuses`); `emit` accepts only actions these cover (`emit_ok`). Proved once, by
induction over the language: Lean fails to derive a functional induction principle for
`PancakeSem`, so each statement runs the code up to the code that follows it.
-/

namespace DN.Dsl

open DN.Compiler DN.Compiler.Syntax DN.Compiler.Lower DN.Compiler.Region DN.Compiler.Bytes

/-! ## Bytes and indicator words -/

theorem ofNat_toNat_setWidth8 (b : BitVec 8) : (BitVec.ofNat 64 b.toNat).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := b.isLt
  omega

theorem widen_eq_iff (x b : BitVec 8) : x.setWidth 64 = BitVec.ofNat 64 b.toNat ↔ x = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    apply BitVec.eq_of_toNat_eq
    have hx := x.isLt
    have hb := b.isLt
    omega
  · rintro rfl
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem indicator_and (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : Word) &&& (if q then 1 else 0 : Word)) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- What `List.isPrefixOf` means, by length and by position. -/
theorem isPrefixOf_iff : ∀ (kw inp : List (BitVec 8)),
    kw.isPrefixOf inp = true ↔ kw.length ≤ inp.length ∧ ∀ i, i < kw.length → inp[i]! = kw[i]!
  | [], _ => by simp [List.isPrefixOf]
  | _ :: _, [] => by simp [List.isPrefixOf]
  | k :: ks, x :: xs => by
    rw [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq, isPrefixOf_iff ks xs]
    constructor
    · rintro ⟨rfl, hlen, hall⟩
      refine ⟨by simp; omega, fun i hi => ?_⟩
      cases i with
      | zero => rfl
      | succ j => simpa using hall j (by simp at hi; omega)
    · rintro ⟨hlen, hall⟩
      refine ⟨(hall 0 (by simp)).symm, by simp at hlen; omega, fun j hj => ?_⟩
      simpa using hall (j + 1) (by simp; omega)

/-! ## The state the generated code works in

`Rep inpA outA inp cap pos written s`: the parameters are bound, the input bytes are at `inpA`,
the bytes written so far are at `outA`, `pos` holds the cursor, and the whole output buffer is
addressable and apart from the input. At an action boundary `pos` is `written.length`. -/

variable {σ : Type}

structure Rep (inpA outA : Word) (inp : List (BitVec 8)) (cap pos : Nat)
    (written : List (BitVec 8)) (s : PancakeState σ) : Prop where
  inp_local : s.locals "inp" = some inpA
  inlen_local : s.locals "inlen" = some (BitVec.ofNat 64 inp.length)
  out_local : s.locals "out" = some outA
  pos_local : s.locals "pos" = some (BitVec.ofNat 64 pos)
  flag_bound : ∃ w, s.locals "m" = some w
  input : memBytesAt s.memory s.memaddrs s.be inpA inp
  output : memBytesAt s.memory s.memaddrs s.be outA written
  room : ∀ j, j < cap → s.memaddrs (byteAlign (outA + BitVec.ofNat 64 j)) = true
  apart : ∀ i j, i < inp.length → j < cap →
    inpA + BitVec.ofNat 64 i ≠ outA + BitVec.ofNat 64 j
  inp_small : inp.length < 2 ^ 63
  cap_small : cap < 2 ^ 63
  fits : written.length ≤ cap

/-- What a step of the generated code leaves alone: everything but the two working names and
the first `lim` bytes of the output buffer. -/
structure Keeps (outA : Word) (lim : Nat) (s t : PancakeState σ) : Prop where
  memaddrs : t.memaddrs = s.memaddrs
  be : t.be = s.be
  clock : t.clock = s.clock
  ffi : t.ffi = s.ffi
  base : t.baseAddr = s.baseAddr
  locals : ∀ x, x ≠ "pos" → x ≠ "m" → t.locals x = s.locals x
  outside : ∀ a, (∀ j, j < lim → a ≠ outA + BitVec.ofNat 64 j) →
    memLoadByte t.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a

theorem Keeps.refl (outA : Word) (lim : Nat) (s : PancakeState σ) : Keeps outA lim s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem Keeps.mono {outA : Word} {lim lim' : Nat} {s t : PancakeState σ} (hle : lim ≤ lim')
    (h : Keeps outA lim s t) : Keeps outA lim' s t :=
  ⟨h.memaddrs, h.be, h.clock, h.ffi, h.base, h.locals,
    fun a ha => h.outside a (fun j hj => ha j (Nat.lt_of_lt_of_le hj hle))⟩

theorem Keeps.trans {outA : Word} {lim : Nat} {s t u : PancakeState σ}
    (h1 : Keeps outA lim s t) (h2 : Keeps outA lim t u) : Keeps outA lim s u := by
  refine ⟨h2.memaddrs.trans h1.memaddrs, h2.be.trans h1.be, h2.clock.trans h1.clock,
    h2.ffi.trans h1.ffi, h2.base.trans h1.base,
    fun x hp hm => (h2.locals x hp hm).trans (h1.locals x hp hm), fun a ha => ?_⟩
  have := h2.outside a ha
  rw [h1.memaddrs, h1.be] at this
  exact this.trans (h1.outside a ha)

/-! ## One statement in front of the rest

A statement that is not a declaration lowers to a `Seq` in front of the rest, or to itself when
nothing follows. Either way, running it and then the rest is running the rest from where it
stopped. -/

theorem run_cons (o : Oracle σ) {x : PStmt} {cx : PancakeProg} (hx : lowerStmt1 x = some cx)
    (hnd : ∀ nm e, x ≠ .dec nm e) {rest : List PStmt} {crest : PancakeProg}
    (hrest : lowerStmtsFold rest = some crest) {s t : PancakeState σ}
    (hrun : PancakeSem o cx s = (none, t)) (hclk : t.clock ≤ s.clock) :
    ∃ c, lowerStmtsFold (x :: rest) = some c ∧ PancakeSem o c s = PancakeSem o crest t := by
  cases rest with
  | nil =>
    simp only [lowerStmtsFold, Option.some.injEq] at hrest
    subst hrest
    refine ⟨cx, by simp [lowerStmtsFold, hx], ?_⟩
    rw [hrun, PancakeSem]
  | cons y ys =>
    refine ⟨.seq cx crest, ?_, seq_step o hrun hclk⟩
    cases x with
    | dec nm e => exact absurd rfl (hnd nm e)
    | _ => simp [lowerStmtsFold, hx, hrest]

/-! ## Writing one byte -/

theorem memBytesAt_putByte_other {m : Word → Word} {dm : Word → Bool} {be : Bool}
    {base a : Word} {w : List (BitVec 8)} {b : BitVec 8} (hw : memBytesAt m dm be base w)
    (hne : ∀ i, i < w.length → base + BitVec.ofNat 64 i ≠ a) :
    memBytesAt (putByte m be a b) dm be base w := by
  intro i hi
  rw [load_putByte_diff m dm be a b _ (hne i hi)]
  exact hw i hi

theorem memBytesAt_snoc {m : Word → Word} {dm : Word → Bool} {be : Bool} {base : Word}
    {w : List (BitVec 8)} {b : BitVec 8} (hw : memBytesAt m dm be base w)
    (hdom : dm (byteAlign (base + BitVec.ofNat 64 w.length)) = true) (hlen : w.length < 2 ^ 64) :
    memBytesAt (putByte m be (base + BitVec.ofNat 64 w.length) b) dm be base (w ++ [b]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hlt : i < w.length
  · rw [load_putByte_diff m dm be _ b _
      (region_addr_inj base i w.length (by omega) hlen (by omega)), hw i hlt]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hlt]
  · have hi' : i = w.length := by omega
    subst hi'
    rw [load_putByte_same m dm be _ b hdom]
    simp

/-! ## The code lowers -/

theorem lowers_cons {x : PStmt} {cx : PancakeProg} (hx : lowerStmt1 x = some cx)
    (hnd : ∀ nm e, x ≠ .dec nm e) {rest : List PStmt} {crest : PancakeProg}
    (hrest : lowerStmtsFold rest = some crest) : ∃ c, lowerStmtsFold (x :: rest) = some c := by
  cases rest with
  | nil => exact ⟨cx, by simp [lowerStmtsFold, hx]⟩
  | cons y ys =>
    cases x with
    | dec nm e => exact absurd rfl (hnd nm e)
    | _ => exact ⟨.seq cx crest, by simp [lowerStmtsFold, hx, hrest]⟩

theorem litStmts_lowers : ∀ (bs : List (BitVec 8)) (off : Nat) (rest : List PStmt)
    (crest : PancakeProg), lowerStmtsFold rest = some crest →
    ∃ c, lowerStmtsFold (litStmts off bs rest) = some c
  | [], off, rest, crest, h => lowers_cons (x := .assign "pos" (eAdd (v "pos") (n off)))
      rfl (by intro _ _ h; cases h) h
  | b :: bs, off, rest, crest, h => by
    obtain ⟨c, hc⟩ := litStmts_lowers bs (off + 1) rest crest h
    exact lowers_cons (x := .storeb (outAt off) (n b.toNat)) rfl (by intro _ _ h; cases h) hc

theorem matchExpr_lowers : ∀ (kw : List (BitVec 8)) (off : Nat),
    ∃ e, lowerExp (matchExpr off kw) = some e
  | [], _ => ⟨_, rfl⟩
  | b :: bs, off => by
    obtain ⟨e, he⟩ := matchExpr_lowers bs (off + 1)
    exact ⟨_, by simp [matchExpr, eAnd, eEq, inpAt, eAdd, n, v, lowerExp, he]; rfl⟩

theorem Act.compile_lowers : ∀ (a : Act) (rest : List PStmt) (crest : PancakeProg),
    lowerStmtsFold rest = some crest → ∃ c, lowerStmtsFold (a.compile rest) = some c
  | .lit bytes, rest, crest, h => litStmts_lowers bytes 0 rest crest h
  | .seq first second, rest, crest, h => by
    obtain ⟨c2, h2⟩ := Act.compile_lowers second rest crest h
    exact Act.compile_lowers first _ c2 h2
  | .ifPrefix keyword thn els, rest, crest, h => by
    obtain ⟨ct, ht⟩ := Act.compile_lowers thn [] .skip (by simp [lowerStmtsFold])
    obtain ⟨ce, he⟩ := Act.compile_lowers els [] .skip (by simp [lowerStmtsFold])
    obtain ⟨em, hem⟩ := matchExpr_lowers keyword 0
    obtain ⟨c3, h3⟩ := lowers_cons (x := .ite (v "m") (thn.compile []) (els.compile []))
      (cx := .cond (.var "m") ct ce) (by simp [lowerStmt1, v, lowerExp, ht, he])
      (by intro _ _ h; cases h) h
    obtain ⟨c2, h2⟩ := lowers_cons
      (x := .ite (eLe (n keyword.length) (v "inlen")) [.assign "m" (matchExpr 0 keyword)] [])
      (cx := .cond (.cmp .notLess (.var "inlen") (.const (BitVec.ofNat 64 keyword.length)))
        (.assign "m" em) .skip)
      (by simp [lowerStmt1, lowerStmtsFold, eLe, n, v, lowerExp, hem]) (by intro _ _ h; cases h) h3
    exact lowers_cons (x := .assign "m" (n 0)) rfl (by intro _ _ h; cases h) h2

/-! ## How each step changes the state -/

section Steps

variable {inpA outA : Word} {inp : List (BitVec 8)} {cap : Nat}

theorem Rep.setPos {L : Nat} {w : List (BitVec 8)} {s : PancakeState σ}
    (h : Rep inpA outA inp cap L w s) (P : Nat) :
    Rep inpA outA inp cap P w { s with locals := setLocal s.locals "pos" (BitVec.ofNat 64 P) } where
  inp_local := by simp [setLocal, h.inp_local]
  inlen_local := by simp [setLocal, h.inlen_local]
  out_local := by simp [setLocal, h.out_local]
  pos_local := by simp [setLocal]
  flag_bound := by
    obtain ⟨u, hu⟩ := h.flag_bound
    exact ⟨u, by simp [setLocal, hu]⟩
  input := h.input
  output := h.output
  room := h.room
  apart := h.apart
  inp_small := h.inp_small
  cap_small := h.cap_small
  fits := h.fits

theorem Rep.setFlag {L : Nat} {w : List (BitVec 8)} {s : PancakeState σ}
    (h : Rep inpA outA inp cap L w s) (val : Word) :
    Rep inpA outA inp cap L w { s with locals := setLocal s.locals "m" val } where
  inp_local := by simp [setLocal, h.inp_local]
  inlen_local := by simp [setLocal, h.inlen_local]
  out_local := by simp [setLocal, h.out_local]
  pos_local := by simp [setLocal, h.pos_local]
  flag_bound := ⟨val, by simp [setLocal]⟩
  input := h.input
  output := h.output
  room := h.room
  apart := h.apart
  inp_small := h.inp_small
  cap_small := h.cap_small
  fits := h.fits

theorem Keeps.setLocal {lim : Nat} {x : String} (hx : x = "pos" ∨ x = "m") (s : PancakeState σ)
    (val : Word) : Keeps outA lim s { s with locals := setLocal s.locals x val } :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun y hp hm => by
    rcases hx with rfl | rfl
    · exact setLocal_ne _ _ _ hp
    · exact setLocal_ne _ _ _ hm, fun _ _ => rfl⟩

/-- Writing the next output byte: at `outA + written.length`, inside the buffer. -/
theorem Rep.store {L : Nat} {w : List (BitVec 8)} {s : PancakeState σ}
    (h : Rep inpA outA inp cap L w s) (b : BitVec 8) (hlt : w.length < cap) :
    Rep inpA outA inp cap L (w ++ [b])
      { s with memory := putByte s.memory s.be (outA + BitVec.ofNat 64 w.length) b } where
  inp_local := h.inp_local
  inlen_local := h.inlen_local
  out_local := h.out_local
  pos_local := h.pos_local
  flag_bound := h.flag_bound
  input := memBytesAt_putByte_other h.input (fun i hi => h.apart i w.length hi hlt)
  output := memBytesAt_snoc h.output (h.room w.length hlt) (by have := h.cap_small; omega)
  room := h.room
  apart := h.apart
  inp_small := h.inp_small
  cap_small := h.cap_small
  fits := by simp; omega

theorem Keeps.store {lim : Nat} {s : PancakeState σ} {j : Nat} (hj : j < lim) (b : BitVec 8) :
    Keeps outA lim s
      { s with memory := putByte s.memory s.be (outA + BitVec.ofNat 64 j) b } :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun a ha =>
    load_putByte_diff s.memory s.memaddrs s.be _ b a (ha j hj)⟩

end Steps

/-! ## Writing a literal -/

theorem lit_run (o : Oracle σ) {inpA outA : Word} {inp : List (BitVec 8)} {cap L : Nat} :
    ∀ (bs : List (BitVec 8)) (off : Nat) (w : List (BitVec 8)) (rest : List PStmt)
      (crest c : PancakeProg) (s : PancakeState σ),
      lowerStmtsFold rest = some crest → lowerStmtsFold (litStmts off bs rest) = some c →
      w.length = L + off → Rep inpA outA inp cap L w s → w.length + bs.length ≤ cap →
      ∃ t, Rep inpA outA inp cap (w ++ bs).length (w ++ bs) t ∧
        Keeps outA (w ++ bs).length s t ∧ PancakeSem o c s = PancakeSem o crest t
  | [], off, w, rest, crest, c, s, hrest, hc, hw, hrep, _ => by
    have hsmall := hrep.cap_small
    have hfits := hrep.fits
    have hval : eval s (.op .add (.var "pos") (.const (BitVec.ofNat 64 off)))
        = some (BitVec.ofNat 64 w.length) := by
      simp only [eval, hrep.pos_local]
      rw [ofNat_add_small L off (by omega), hw]
    have hrun := sem_assign (oracle := o) hval hrep.pos_local
    obtain ⟨c', hc', hsem⟩ := run_cons o (x := .assign "pos" (eAdd (v "pos") (n off)))
      (cx := .assign "pos" (.op .add (.var "pos") (.const (BitVec.ofNat 64 off)))) rfl
      (by intro _ _ h; cases h) hrest hrun (Nat.le_refl _)
    have hcc : c = c' := by
      have h1 : lowerStmtsFold (litStmts off [] rest) = some c' := hc'
      rw [hc] at h1
      exact Option.some.inj h1
    subst hcc
    refine ⟨_, ?_, Keeps.setLocal (Or.inl rfl) s _, hsem⟩
    simpa using hrep.setPos w.length
  | b :: bs, off, w, rest, crest, c, s, hrest, hc, hw, hrep, hfit => by
    have hlt : w.length < cap := by simp at hfit; omega
    have hsmall := hrep.cap_small
    obtain ⟨c1, hc1⟩ := litStmts_lowers bs (off + 1) rest crest hrest
    have haddr : eval s (.op .add (.op .add (.var "out") (.var "pos"))
        (.const (BitVec.ofNat 64 off))) = some (outA + BitVec.ofNat 64 w.length) := by
      simp only [eval, hrep.out_local, hrep.pos_local]
      rw [BitVec.add_assoc, ofNat_add_small L off (by omega), hw]
    have hstore : memStoreByte s.memory s.memaddrs s.be (outA + BitVec.ofNat 64 w.length)
        ((BitVec.ofNat 64 b.toNat).setWidth 8)
        = some (putByte s.memory s.be (outA + BitVec.ofNat 64 w.length) b) := by
      rw [ofNat_toNat_setWidth8]
      exact memStore_eq _ _ _ _ _ (hrep.room w.length hlt)
    have hsrc : eval s (.const (BitVec.ofNat 64 b.toNat)) = some (BitVec.ofNat 64 b.toNat) := by
      simp [eval]
    have hrun := evaluate_storeByte o s haddr hsrc hstore
    obtain ⟨c', hc', hsem⟩ := run_cons o (x := .storeb (outAt off) (n b.toNat))
      (cx := .storeByte (.op .add (.op .add (.var "out") (.var "pos"))
        (.const (BitVec.ofNat 64 off))) (.const (BitVec.ofNat 64 b.toNat)))
      rfl (by intro _ _ h; cases h) hc1 hrun (Nat.le_refl _)
    have hcc : c = c' := by
      have h1 : lowerStmtsFold (litStmts off (b :: bs) rest) = some c' := hc'
      rw [hc] at h1
      exact Option.some.inj h1
    subst hcc
    obtain ⟨t, hrep', hkeep, hsem'⟩ := lit_run o bs (off + 1) (w ++ [b]) rest crest c1 _ hrest hc1
      (by simp; omega) (hrep.store b hlt) (by simp at hfit ⊢; omega)
    have happ : w ++ [b] ++ bs = w ++ b :: bs := by simp
    rw [happ] at hrep' hkeep
    exact ⟨t, hrep', (Keeps.store (by simp) b).trans hkeep, hsem.trans hsem'⟩

/-! ## The keyword test -/

theorem eval_guard {s : PancakeState σ} {inp : List (BitVec 8)} {k : Nat}
    (hinlen : s.locals "inlen" = some (BitVec.ofNat 64 inp.length)) (hi : inp.length < 2 ^ 63)
    (hk : k < 2 ^ 63) :
    eval s (.cmp .notLess (.var "inlen") (.const (BitVec.ofNat 64 k)))
      = some (if k ≤ inp.length then 1 else 0) := by
  simp only [eval, hinlen, signedLt_ofNat _ _ hi hk]
  by_cases h : inp.length < k
  · simp [h, show ¬ k ≤ inp.length by omega]
  · simp [h, show k ≤ inp.length by omega]

theorem eval_match {s : PancakeState σ} {inpA : Word} {inp : List (BitVec 8)}
    (hinp : s.locals "inp" = some inpA) (hmem : memBytesAt s.memory s.memaddrs s.be inpA inp) :
    ∀ (kw : List (BitVec 8)) (off : Nat) (e : PancakeExp), lowerExp (matchExpr off kw) = some e →
      off + kw.length ≤ inp.length →
      eval s e = some (if (∀ i, i < kw.length → inp[off + i]! = kw[i]!) then 1 else 0)
  | [], _, e, he, _ => by
    have he' : e = .const (BitVec.ofNat 64 1) := by
      simp only [matchExpr, n, lowerExp] at he
      exact (Option.some.inj he).symm
    subst he'
    simp [eval]
  | b :: bs, off, e, he, hlen => by
    obtain ⟨er, her⟩ := matchExpr_lowers bs (off + 1)
    have hshape : lowerExp (matchExpr off (b :: bs)) = some (.op .and_
        (.cmp .equal (.loadByte (.op .add (.var "inp") (.const (BitVec.ofNat 64 off))))
          (.const (BitVec.ofNat 64 b.toNat))) er) := by
      simp only [matchExpr, eAnd, eEq, inpAt, eAdd, n, v, lowerExp, her]
    rw [hshape] at he
    have he' := Option.some.inj he
    subst he'
    have hl : off < inp.length := by simp at hlen; omega
    have hrest := eval_match hinp hmem bs (off + 1) er her (by simp at hlen; omega)
    simp only [eval, hinp, hmem off hl, hrest, widen_eq_iff, indicator_and]
    congr 1
    by_cases hall : ∀ i, i < (b :: bs).length → inp[off + i]! = (b :: bs)[i]!
    · rw [if_pos hall, if_pos]
      refine ⟨by simpa using hall 0 (by simp), fun j hj => ?_⟩
      have := hall (j + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
    · rw [if_neg hall, if_neg]
      rintro ⟨h0, hr⟩
      apply hall
      intro i hi
      cases i with
      | zero => simpa using h0
      | succ j =>
        have := hr j (by simp at hi; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-! ## Branching -/

theorem sem_skip (o : Oracle σ) (s : PancakeState σ) : PancakeSem o .skip s = (none, s) := by
  rw [PancakeSem]

theorem sem_cond (o : Oracle σ) {s : PancakeState σ} {e : PancakeExp} {c1 c2 : PancakeProg}
    {w : Word} (h : eval s e = some w) :
    PancakeSem o (.cond e c1 c2) s = PancakeSem o (if w ≠ 0 then c1 else c2) s := by
  rw [PancakeSem, h]

/-- The flag the keyword test leaves. -/
def flag (kw inp : List (BitVec 8)) : Word := if kw.isPrefixOf inp then 1 else 0

theorem guard_run (o : Oracle σ) {inpA outA : Word} {inp : List (BitVec 8)} {cap L : Nat}
    {w : List (BitVec 8)} (kw : List (BitVec 8)) (hk : kw.length < 2 ^ 63) {em : PancakeExp}
    (hem : lowerExp (matchExpr 0 kw) = some em) {s : PancakeState σ}
    (h : Rep inpA outA inp cap L w s) (hm : s.locals "m" = some 0) :
    ∃ t, PancakeSem o (.cond (.cmp .notLess (.var "inlen") (.const (BitVec.ofNat 64 kw.length)))
        (.assign "m" em) .skip) s = (none, t) ∧
      Rep inpA outA inp cap L w t ∧ Keeps outA 0 s t ∧ t.locals "m" = some (flag kw inp) := by
  have hg := eval_guard h.inlen_local h.inp_small hk
  by_cases hlen : kw.length ≤ inp.length
  · rw [if_pos hlen] at hg
    have hmv := eval_match h.inp_local h.input kw 0 em hem (by omega)
    have hval : (if (∀ i, i < kw.length → inp[0 + i]! = kw[i]!) then (1 : Word) else 0)
        = flag kw inp := by
      simp only [flag, Nat.zero_add]
      by_cases hall : ∀ i, i < kw.length → inp[i]! = kw[i]!
      · rw [if_pos hall, if_pos ((isPrefixOf_iff kw inp).2 ⟨hlen, hall⟩)]
      · rw [if_neg hall, if_neg (fun hp => hall ((isPrefixOf_iff kw inp).1 hp).2)]
    rw [hval] at hmv
    refine ⟨_, ?_, h.setFlag (flag kw inp), Keeps.setLocal (Or.inr rfl) s _, by simp [setLocal]⟩
    rw [sem_cond o hg, if_pos (by decide)]
    exact sem_assign hmv hm
  · rw [if_neg hlen] at hg
    refine ⟨s, ?_, h, Keeps.refl outA 0 s, ?_⟩
    · rw [sem_cond o hg, if_neg (by decide), sem_skip]
    · rw [hm, flag, if_neg (fun hp => hlen ((isPrefixOf_iff kw inp).1 hp).1)]

/-! ## Every action -/

/-- The code of an action, run in front of `rest`, writes what `Act.run` says and then runs
`rest`; it touches nothing but `pos`, `m` and the output buffer. -/
theorem Act.compile_run (o : Oracle σ) (inpA outA : Word) (inp : List (BitVec 8)) (cap : Nat) :
    ∀ (a : Act) (rest : List PStmt) (crest c : PancakeProg) (out : List (BitVec 8))
      (s : PancakeState σ),
      a.Fits → lowerStmtsFold rest = some crest → lowerStmtsFold (a.compile rest) = some c →
      Rep inpA outA inp cap out.length out s → out.length + a.maxLen ≤ cap →
      ∃ t, Rep inpA outA inp cap (a.run inp out).length (a.run inp out) t ∧
        Keeps outA (a.run inp out).length s t ∧ PancakeSem o c s = PancakeSem o crest t
  | .lit bytes, rest, crest, c, out, s, _, hrest, hc, hrep, hfit => by
    obtain ⟨t, hrep', hkeep, hsem⟩ := lit_run o bytes 0 out rest crest c s hrest hc (by simp) hrep
      (by simpa [Act.maxLen] using hfit)
    exact ⟨t, by simpa [Act.run] using hrep', by simpa [Act.run] using hkeep, hsem⟩
  | .seq first second, rest, crest, c, out, s, hfits, hrest, hc, hrep, hfit => by
    obtain ⟨c2, hc2⟩ := Act.compile_lowers second rest crest hrest
    have hl := Act.run_length_le first inp out
    simp only [Act.maxLen] at hfit
    obtain ⟨t1, hrep1, hkeep1, hsem1⟩ :=
      Act.compile_run o inpA outA inp cap first _ c2 c out s hfits.1 hc2 hc hrep (by omega)
    obtain ⟨t2, hrep2, hkeep2, hsem2⟩ :=
      Act.compile_run o inpA outA inp cap second rest crest c2 _ t1 hfits.2 hrest hc2 hrep1
        (by omega)
    exact ⟨t2, hrep2, (hkeep1.mono (Act.length_le_run second inp _)).trans hkeep2,
      hsem1.trans hsem2⟩
  | .ifPrefix kw thn els, rest, crest, c, out, s, hfits, hrest, hc, hrep, hfit => by
    obtain ⟨hk, hft, hfe⟩ := hfits
    simp only [Act.maxLen] at hfit
    obtain ⟨ct, hct⟩ := Act.compile_lowers thn [] .skip lowerStmtsFold_nil
    obtain ⟨ce, hce⟩ := Act.compile_lowers els [] .skip lowerStmtsFold_nil
    obtain ⟨em, hem⟩ := matchExpr_lowers kw 0
    obtain ⟨u, hu⟩ := hrep.flag_bound
    have h1 := sem_assign (oracle := o) (x := "m") (e := .const (BitVec.ofNat 64 0))
      (v := BitVec.ofNat 64 0) rfl hu
    have hrep1 := hrep.setFlag (BitVec.ofNat 64 0)
    have hkeep1 := Keeps.setLocal (outA := outA)
      (lim := ((Act.ifPrefix kw thn els).run inp out).length) (Or.inr rfl) s (BitVec.ofNat 64 0)
    obtain ⟨s2, h2, hrep2, hkeep2, hm2⟩ := guard_run o kw hk hem hrep1 (by simp [setLocal])
    have hbr : ∃ t, Rep inpA outA inp cap ((Act.ifPrefix kw thn els).run inp out).length
        ((Act.ifPrefix kw thn els).run inp out) t ∧
        Keeps outA ((Act.ifPrefix kw thn els).run inp out).length s2 t ∧
        PancakeSem o (.cond (.var "m") ct ce) s2 = (none, t) := by
      have hv : eval s2 (.var "m") = some (flag kw inp) := hm2
      rw [sem_cond o hv]
      by_cases hp : kw.isPrefixOf inp = true
      · rw [if_pos (by simp [flag, hp])]
        obtain ⟨t, hrt, hkt, hst⟩ := Act.compile_run o inpA outA inp cap thn [] .skip ct out s2
          hft lowerStmtsFold_nil hct hrep2 (by omega)
        rw [sem_skip] at hst
        exact ⟨t, by simpa [Act.run, hp] using hrt, by simpa [Act.run, hp] using hkt, hst⟩
      · rw [if_neg (by simp [flag, hp])]
        obtain ⟨t, hrt, hkt, hst⟩ := Act.compile_run o inpA outA inp cap els [] .skip ce out s2
          hfe lowerStmtsFold_nil hce hrep2 (by omega)
        rw [sem_skip] at hst
        exact ⟨t, by simpa [Act.run, hp] using hrt, by simpa [Act.run, hp] using hkt, hst⟩
    obtain ⟨t, hrt, hkt, hst⟩ := hbr
    obtain ⟨c3, hc3, hs3⟩ := run_cons o (x := .ite (v "m") (thn.compile []) (els.compile []))
      (cx := .cond (.var "m") ct ce) (by simp [lowerStmt1, v, lowerExp, hct, hce])
      (by intro _ _ h; cases h) hrest hst (Nat.le_of_eq hkt.clock)
    obtain ⟨c2, hc2, hs2⟩ := run_cons o
      (x := .ite (eLe (n kw.length) (v "inlen")) [.assign "m" (matchExpr 0 kw)] [])
      (cx := .cond (.cmp .notLess (.var "inlen") (.const (BitVec.ofNat 64 kw.length)))
        (.assign "m" em) .skip)
      (by simp [lowerStmt1, lowerStmtsFold, eLe, n, v, lowerExp, hem]) (by intro _ _ h; cases h)
      hc3 h2 (Nat.le_of_eq hkeep2.clock)
    obtain ⟨c1, hc1, hs1⟩ := run_cons o (x := .assign "m" (n 0))
      (cx := .assign "m" (.const (BitVec.ofNat 64 0))) rfl (by intro _ _ h; cases h) hc2 h1
      (Nat.le_refl _)
    have hcc : c = c1 := by
      have e : lowerStmtsFold ((Act.ifPrefix kw thn els).compile rest) = some c1 := hc1
      rw [hc] at e
      exact Option.some.inj e
    subst hcc
    exact ⟨t, hrt, hkeep1.trans ((hkeep2.mono (Nat.zero_le _)).trans hkt),
      hs1.trans (hs2.trans hs3)⟩

/-! ## The exported function -/

theorem Act.compile_ne_nil : ∀ (a : Act) (rest : List PStmt), a.compile rest ≠ []
  | .lit [], _ => by simp [Act.compile, litStmts]
  | .lit (_ :: _), _ => by simp [Act.compile, litStmts]
  | .ifPrefix _ _ _, _ => by simp [Act.compile]
  | .seq first second, rest => Act.compile_ne_nil first _

/-- The lowered body of `respond name a`, given the lowered code of the action. -/
def respondProg (a : Act) (cb : PancakeProg) : PancakeProg :=
  .cond (.cmp .less (.var "inlen") (.const (BitVec.ofNat 64 0))) (.ret (.const (BitVec.ofNat 64 refusal)))
    (.cond (.cmp .less (.var "cap") (.const (BitVec.ofNat 64 0))) (.ret (.const (BitVec.ofNat 64 refusal)))
      (.cond (.cmp .less (.var "cap") (.const (BitVec.ofNat 64 a.maxLen)))
        (.ret (.const (BitVec.ofNat 64 refusal)))
        (.dec "pos" (.const (BitVec.ofNat 64 0)) (.dec "m" (.const (BitVec.ofNat 64 0)) cb))))

theorem respond_lower (name : String) (a : Act) {cb : PancakeProg}
    (hb : lowerStmtsFold (a.compile [.ret (v "pos")]) = some cb) :
    lower (respond name a) = some (respondProg a cb) := by
  obtain ⟨x, xs, hx⟩ : ∃ x xs, a.compile [.ret (v "pos")] = x :: xs := by
    cases h : a.compile [.ret (v "pos")] with
    | nil => exact absurd h (Act.compile_ne_nil a _)
    | cons x xs => exact ⟨x, xs, rfl⟩
  simp only [lower, respond, List.foldr, Kernels.rejectNegative, List.cons_append,
    List.nil_append, hx]
  rw [hx] at hb
  simp [respondProg, lowerStmtsFold, lowerStmt1, lowerExp, eLt, n, v, hb]

/-- The state after the two declarations. -/
def entryState (s : PancakeState σ) : PancakeState σ :=
  { s with
    locals := setLocal (setLocal s.locals "pos" (BitVec.ofNat 64 0)) "m" (BitVec.ofNat 64 0) }

theorem Rep.entry {inpA outA : Word} {inp : List (BitVec 8)} {cap : Nat} {s : PancakeState σ}
    (hinp : s.locals "inp" = some inpA)
    (hinlen : s.locals "inlen" = some (BitVec.ofNat 64 inp.length))
    (hout : s.locals "out" = some outA)
    (hin : memBytesAt s.memory s.memaddrs s.be inpA inp)
    (hroom : ∀ j, j < cap → s.memaddrs (byteAlign (outA + BitVec.ofNat 64 j)) = true)
    (hapart : ∀ i j, i < inp.length → j < cap →
      inpA + BitVec.ofNat 64 i ≠ outA + BitVec.ofNat 64 j)
    (hsmall : inp.length < 2 ^ 63) (hcsmall : cap < 2 ^ 63) :
    Rep inpA outA inp cap ([] : List (BitVec 8)).length [] (entryState s) where
  inp_local := by simp [entryState, setLocal, hinp]
  inlen_local := by simp [entryState, setLocal, hinlen]
  out_local := by simp [entryState, setLocal, hout]
  pos_local := by simp [entryState, setLocal]
  flag_bound := ⟨BitVec.ofNat 64 0, by simp [entryState, setLocal]⟩
  input := hin
  output := by intro i hi; simp at hi
  room := hroom
  apart := hapart
  inp_small := hsmall
  cap_small := hcsmall
  fits := by simp

theorem sem_ret_const (o : Oracle σ) (s : PancakeState σ) (w : Word) :
    PancakeSem o (.ret (.const w)) s = (some (.return_ w), emptyLocals s) := by
  rw [PancakeSem]
  rfl

/-- Every call the function refuses, it refuses before writing anything. -/
theorem respond_refuses (o : Oracle σ) (name : String) (a : Act) {c : PancakeProg}
    (hc : lower (respond name a) = some c) {s : PancakeState σ} {wi wc : Word}
    (hi : s.locals "inlen" = some wi) (hcp : s.locals "cap" = some wc)
    (hbad : signedLt wi 0 = true ∨ signedLt wc 0 = true ∨
      signedLt wc (BitVec.ofNat 64 a.maxLen) = true) :
    PancakeSem o c s = (some (.return_ (BitVec.ofNat 64 refusal)), emptyLocals s) := by
  obtain ⟨cb, hcb⟩ := Act.compile_lowers a [.ret (v "pos")] (.ret (.var "pos")) rfl
  rw [respond_lower name a hcb] at hc
  cases Option.some.inj hc
  have g1 : eval s (.cmp .less (.var "inlen") (.const (BitVec.ofNat 64 0)))
      = some (if signedLt wi 0 then 1 else 0) := by
    simp only [eval, hi]
    rfl
  have g2 : eval s (.cmp .less (.var "cap") (.const (BitVec.ofNat 64 0)))
      = some (if signedLt wc 0 then 1 else 0) := by
    simp only [eval, hcp]
    rfl
  have g3 : eval s (.cmp .less (.var "cap") (.const (BitVec.ofNat 64 a.maxLen)))
      = some (if signedLt wc (BitVec.ofNat 64 a.maxLen) then 1 else 0) := by
    simp only [eval, hcp]
  simp only [respondProg]
  rw [sem_cond o g1]
  by_cases h1 : signedLt wi 0 = true
  · rw [if_pos h1, if_pos (by decide), sem_ret_const]
  rw [if_neg h1, if_neg (by decide), sem_cond o g2]
  by_cases h2 : signedLt wc 0 = true
  · rw [if_pos h2, if_pos (by decide), sem_ret_const]
  have h3 : signedLt wc (BitVec.ofNat 64 a.maxLen) = true := by
    rcases hbad with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h
  rw [if_neg h2, if_neg (by decide), sem_cond o g3, if_pos h3, if_pos (by decide), sem_ret_const]

/-- **The function, run.** Given an input at `inpA` and room for `cap ≥ maxLen` bytes at `outA`
apart from it, the function returns the length of what the action produces, below the refusal
value, with those bytes at `outA`; it changes no memory outside them, and no permission, byte
order, clock or FFI state. -/
theorem respond_correct (o : Oracle σ) (name : String) (a : Act) {c : PancakeProg}
    (hc : lower (respond name a) = some c) (hfits : a.Fits) (hmax : a.maxLen < refusal)
    {inpA outA : Word} {inp : List (BitVec 8)} {cap : Nat} {s : PancakeState σ}
    (hinp : s.locals "inp" = some inpA)
    (hinlen : s.locals "inlen" = some (BitVec.ofNat 64 inp.length))
    (hout : s.locals "out" = some outA) (hcap : s.locals "cap" = some (BitVec.ofNat 64 cap))
    (hin : memBytesAt s.memory s.memaddrs s.be inpA inp)
    (hroom : ∀ j, j < cap → s.memaddrs (byteAlign (outA + BitVec.ofNat 64 j)) = true)
    (hapart : ∀ i j, i < inp.length → j < cap →
      inpA + BitVec.ofNat 64 i ≠ outA + BitVec.ofNat 64 j)
    (hsmall : inp.length < 2 ^ 63) (hcsmall : cap < 2 ^ 63) (hfit : a.maxLen ≤ cap) :
    ∃ t, PancakeSem o c s = (some (.return_ (BitVec.ofNat 64 (a.run inp []).length)), t) ∧
      (a.run inp []).length < refusal ∧
      memBytesAt t.memory t.memaddrs t.be outA (a.run inp []) ∧
      (∀ addr, (∀ j, j < (a.run inp []).length → addr ≠ outA + BitVec.ofNat 64 j) →
        memLoadByte t.memory s.memaddrs s.be addr = memLoadByte s.memory s.memaddrs s.be addr) ∧
      t.memaddrs = s.memaddrs ∧ t.be = s.be ∧ t.ffi = s.ffi ∧ t.clock = s.clock := by
  obtain ⟨cb, hcb⟩ := Act.compile_lowers a [.ret (v "pos")] (.ret (.var "pos")) rfl
  rw [respond_lower name a hcb] at hc
  cases Option.some.inj hc
  have hml : a.maxLen < 2 ^ 63 := by unfold refusal at hmax; omega
  have g1 : eval s (.cmp .less (.var "inlen") (.const (BitVec.ofNat 64 0))) = some 0 := by
    simp only [eval, hinlen, signedLt_ofNat inp.length 0 hsmall (by decide)]
    simp
  have g2 : eval s (.cmp .less (.var "cap") (.const (BitVec.ofNat 64 0))) = some 0 := by
    simp only [eval, hcap, signedLt_ofNat cap 0 hcsmall (by decide)]
    simp
  have g3 : eval s (.cmp .less (.var "cap") (.const (BitVec.ofNat 64 a.maxLen))) = some 0 := by
    simp only [eval, hcap, signedLt_ofNat cap a.maxLen hcsmall hml]
    simp [show ¬ cap < a.maxLen by omega]
  simp only [respondProg]
  rw [sem_cond o g1, if_neg (by decide), sem_cond o g2, if_neg (by decide), sem_cond o g3,
    if_neg (by decide)]
  have hrep := Rep.entry hinp hinlen hout hin hroom hapart hsmall hcsmall
  obtain ⟨t, hrt, hkt, hst⟩ := Act.compile_run o inpA outA inp cap a [.ret (v "pos")]
    (.ret (.var "pos")) cb [] _ hfits rfl hcb hrep (by simpa using hfit)
  have hret : PancakeSem o (.ret (.var "pos")) t
      = (some (.return_ (BitVec.ofNat 64 (a.run inp []).length)), emptyLocals t) := by
    rw [PancakeSem]
    simp only [eval, hrt.pos_local]
  rw [hret] at hst
  rw [sem_dec o (e := .const (BitVec.ofNat 64 0)) rfl
    (sem_dec o (s := { s with locals := setLocal s.locals "pos" (BitVec.ofNat 64 0) }) (v := "m")
      (e := .const (BitVec.ofNat 64 0)) rfl hst)]
  have hlen := Act.run_length_le a inp []
  refine ⟨_, rfl, by simp at hlen; omega, hrt.output, fun addr ha => hkt.outside addr ha,
    hkt.memaddrs, hkt.be, hkt.ffi, hkt.clock⟩

/-- The same statement as a refinement, the form `Certificate` takes. Composing certificates
builds a `Seq` in the model, which is not how `respond` prints a program. -/
theorem Act.compile_refinesClk (o : Oracle σ) (inpA outA : Word) (inp out : List (BitVec 8))
    (cap : Nat) (a : Act) {c : PancakeProg} (hfits : a.Fits)
    (hc : lowerStmtsFold (a.compile []) = some c) (hfit : out.length + a.maxLen ≤ cap) :
    Clock.RefinesClk o c (Rep inpA outA inp cap out.length out)
      (fun s t => Rep inpA outA inp cap (a.run inp out).length (a.run inp out) t ∧
        Keeps outA (a.run inp out).length s t) := by
  intro s hrep
  obtain ⟨t, hrt, hkt, hst⟩ :=
    Act.compile_run o inpA outA inp cap a [] .skip c out s hfits lowerStmtsFold_nil hc hrep hfit
  rw [sem_skip] at hst
  exact ⟨t, hst, ⟨hrt, hkt⟩, Nat.le_of_eq hkt.clock⟩

/-- What `emit` accepts, the theorems above cover. -/
theorem emit_ok {name src : String} {a : Act} (h : emit name a = .ok src) :
    a.Fits ∧ a.maxLen < refusal ∧ ∃ c, lower (respond name a) = some c := by
  unfold emit at h
  by_cases hf : a.fitsB = true
  · by_cases hm : refusal ≤ a.maxLen
    · simp [hf, hm] at h
    · obtain ⟨cb, hcb⟩ := Act.compile_lowers a [.ret (v "pos")] (.ret (.var "pos")) rfl
      exact ⟨Act.fits_of_fitsB a hf, by omega, _, respond_lower name a hcb⟩
  · simp [hf] at h

end DN.Dsl
