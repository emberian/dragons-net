-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionRun
import DN.News.FramerCode
import DN.Compiler.Block

/-!
# DN.Server.SessionFrame

The session's framers, proven as the session has them. `serve` frames held octets as `FramerCode.lineFrag_run` proves
(`framing_safeR`), and `postFeed` decides as `PostSpec.frameOctet` (`octet_frameOctet`). The turn's invariants are
premises (`atCheck_witness`, `atOctet_witness`); later loop statements are not proven here.
-/

namespace DN.Server.SessionFrame

open DN.Compiler DN.Compiler.WpRet DN.Server DN.Server.SessionLayout DN.Server.SessionRun
  DN.News DN.News.FrameSpec DN.News.Framer DN.News.FramerProg DN.News.FramerCode

variable {σ : Type}

/-! ## The line framer -/

/-- **The line framer, then whatever follows.** The block at `st` holds a fitting framer state; the locals name it, the
octets, their count and position. What follows runs on `lineFrag_run`'s state, same code and domain, the framer's ticks
spent; or the run times out. -/
theorem lineFrag_safeR (o : Oracle σ) (lim : Nat) (hlim : lim < 2 ^ 62) (hpos : 0 < lim)
    {P P' Q : PancakeState σ → Prop} {R : Ret} {k : PancakeProg}
    (hpre : ∀ s, P s → ∃ (st p : Word) (q : List Byte) (i0 : Nat) (A : LineState),
      Fits lim A ∧ i0 ≤ q.length ∧ q.length < 2 ^ 62 ∧
      s.locals "blk" = some st ∧ s.locals "p" = some p ∧
      s.locals "n" = some (BitVec.ofNat 64 q.length) ∧ s.locals "i" = some (BitVec.ofNat 64 i0) ∧
      (∀ v, v ∈ ["len", "cr", "bad", "kind", "kept", "b"] → ∃ w, s.locals v = some w) ∧
      Holds s st A ∧ Chunk s p q ∧ Room lim s st ∧ st.toNat % 8 = 0 ∧
      st.toNat + 40 + lim ≤ 2 ^ 64 ∧
      (∀ j j', j < lim → j' < q.length → st + 40#64 + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 j') ∧
      ∀ s', LineAfter lim s s' st (i0 + (frameOnce lim A (q.drop i0)).1)
        (frameOnce lim A (q.drop i0)).2.1 (frameOnce lim A (q.drop i0)).2.2 → Safe.Same s s' →
        s'.clock = s.clock - (frameOnce lim A (q.drop i0)).1 → P' s')
    (hk : SafeR o P' k R Q) : SafeR o P (lineFragP lim k) R Q := by
  intro s hs
  obtain ⟨st, p, q, i0, A, hA, hi0, hq, hst, hp, hn, hi, hw, hH, hC, hR, hal, hfit, hsep, hnext⟩ :=
    hpre s hs
  have h := lineFrag_run o lim hlim hpos s st p q i0 A hA hi0 hq hst hp hn hi hw hH hC hR hal hfit hsep
  by_cases hc : (frameOnce lim A (q.drop i0)).1 ≤ s.clock
  · obtain ⟨s', hclk, hafter, hrun⟩ := h.1 hc
    have hsame : Safe.Same s s' := by
      have := Safe.sem_same o s.clock (lineFragP lim .skip) s (Nat.le_refl _)
      rwa [hrun .skip, PancakeSem.eq_1] at this
    rw [hrun k]
    exact hk s' (hnext s' hafter hsame hclk)
  · obtain ⟨t, ht⟩ := h.2 (by omega) k
    rw [ht]
    rfl

/-- **A connection's held octets follow its framer's block**, so none of them is one the block
keeps. -/
theorem held_apart (st : Word) (lim len : Nat) (h : lim + len < 2 ^ 64) :
    ∀ j j', j < lim → j' < len →
      st + 40#64 + BitVec.ofNat 64 j ≠ (st + 40#64 + BitVec.ofNat 64 lim) + BitVec.ofNat 64 j' := by
  intro j j' hj hj' he
  rw [BitVec.add_assoc (st + 40#64), ← BitVec.ofNat_add] at he
  rw [BitVec.add_comm (st + 40#64), BitVec.add_comm (st + 40#64)] at he
  have := congrArg BitVec.toNat ((BitVec.add_left_inj _).mp he)
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- In a connection's record the held octets start where the framer's block and the octets it
keeps end. -/
theorem held_at (cb : Word) :
    cb + BitVec.ofNat 64 cHeld =
      (cb + BitVec.ofNat 64 cFramer) + 40#64 + BitVec.ofNat 64 News.SessionSpec.lineLimit := by
  rw [BitVec.add_assoc, BitVec.add_assoc, show (40#64 : Word) = BitVec.ofNat 64 40 from rfl,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  rfl

/-! ## The line framer in `serve` -/

/-- Where connection `c`'s record starts in the session's words. -/
def recordAt (b : Word) (c : Nat) : Word := b + BitVec.ofNat 64 (tableOff + c * connSlot)

/-- …its line framer's block… -/
def blockAt (b : Word) (c : Nat) : Word := recordAt b c + BitVec.ofNat 64 cFramer

/-- …and the octets it holds. -/
def heldAt (b : Word) (c : Nat) : Word := recordAt b c + BitVec.ofNat 64 cHeld

/-- What `serve` has where it checks connection `c`'s framer block before framing held octets `q` from `i0`. The locals
name them, and the block holds the framer's state `A` in addressable words. -/
structure AtCheck (b : Word) (c : Nat) (q : List Byte) (i0 : Nat) (A : LineState)
    (s : PancakeState σ) : Prop where
  blk : s.locals "blk" = some (blockAt b c)
  p : s.locals "p" = some (heldAt b c)
  n : s.locals "n" = some (BitVec.ofNat 64 q.length)
  i : s.locals "i" = some (BitVec.ofNat 64 i0)
  i0 : i0 ≤ q.length
  len : q.length ≤ data
  holds : Holds s (blockAt b c) A
  fits : Fits News.SessionSpec.lineLimit A
  chunk : Chunk s (heldAt b c) q
  room : Room News.SessionSpec.lineLimit s (blockAt b c)
  al : (blockAt b c).toNat % 8 = 0
  fit : (blockAt b c).toNat + 40 + News.SessionSpec.lineLimit ≤ 2 ^ 64

/-- The framer's locals. -/
def lineLocals : List String := ["len", "cr", "bad", "kind", "kept", "b"]

/-- **The check `serve` makes of the framer's block passes** on a block the framer keeps. -/
theorem serve_kept (o : Oracle σ) (R : Ret) (b : Word) (c : Nat) (q : List Byte) (i0 : Nat)
    (A : LineState) {P : PancakeState σ → Prop} (hP : ∀ s, P s → AtCheck b c q i0 A s) :
    SafeR o P (keptG (.loadWord (.var "blk")) News.SessionSpec.lineLimit) R P :=
  keptG_pass o R (by decide) fun s h => by
    have h := hP s h
    exact ⟨A.len, h.fits.2.1, by simp [eval, h.blk, h.room.1, h.holds.1]⟩

/-- **`serve` frames a connection's held octets as the line framer does**, the framer's locals bound. What follows runs
on the state `lineFrag_run` describes. -/
theorem serve_frame (o : Oracle σ) (b : Word) (c : Nat) (q : List Byte) (i0 : Nat) (A : LineState)
    {P P' Q : PancakeState σ → Prop} {R : Ret} {k : PancakeProg}
    (hP : ∀ s, P s → AtCheck b c q i0 A s ∧ Bound lineLocals s)
    (hnext : ∀ s s', P s →
      LineAfter News.SessionSpec.lineLimit s s' (blockAt b c)
        (i0 + (frameOnce News.SessionSpec.lineLimit A (q.drop i0)).1)
        (frameOnce News.SessionSpec.lineLimit A (q.drop i0)).2.1
        (frameOnce News.SessionSpec.lineLimit A (q.drop i0)).2.2 → Safe.Same s s' →
      s'.clock = s.clock - (frameOnce News.SessionSpec.lineLimit A (q.drop i0)).1 → P' s')
    (hk : SafeR o P' k R Q) :
    SafeR o P (lineFragP News.SessionSpec.lineLimit k) R Q := by
  refine lineFrag_safeR o _ (by decide) (by decide) (fun s hs => ?_) hk
  obtain ⟨h, hb⟩ := hP s hs
  have hdata : data < 2 ^ 62 := by decide
  refine ⟨blockAt b c, heldAt b c, q, i0, A, h.fits, h.i0, by have := h.len; omega, h.blk, h.p, h.n,
    h.i, hb, h.holds, h.chunk, h.room, h.al, h.fit, ?_, fun s' => hnext s s' hs⟩
  have hsep := held_apart (blockAt b c) News.SessionSpec.lineLimit q.length
    (by have h1 := h.len; have h2 : News.SessionSpec.lineLimit + data < 2 ^ 64 := (by decide); omega)
  rw [heldAt, held_at]
  exact hsep

/-- **The place and the framer's locals declared, then the framer**: what follows runs on `lineFrag_run`'s state, `i0`
the start. An ending ignoring those locals is the declarations' ending too. -/
theorem framing_safeR (o : Oracle σ) (b : Word) (c : Nat) (q : List Byte) (i0 : Nat) (A : LineState)
    {P P' Q : PancakeState σ → Prop} {R : Ret} {k : PancakeProg}
    (hP : ∀ s, P s → AtCheck b c q i0 A s)
    (hPset : ∀ s y w, P s → y ∈ "i0" :: lineLocals → P { s with locals := setLocal s.locals y w })
    (hQ : ∀ t y v, Q t → y ∈ "i0" :: lineLocals → Q (Wp.restore t y v))
    (hnext : ∀ s s', P s → s.locals "i0" = some (BitVec.ofNat 64 i0) →
      LineAfter News.SessionSpec.lineLimit s s' (blockAt b c)
        (i0 + (frameOnce News.SessionSpec.lineLimit A (q.drop i0)).1)
        (frameOnce News.SessionSpec.lineLimit A (q.drop i0)).2.1
        (frameOnce News.SessionSpec.lineLimit A (q.drop i0)).2.2 → Safe.Same s s' →
      s'.clock = s.clock - (frameOnce News.SessionSpec.lineLimit A (q.drop i0)).1 → P' s')
    (hk : SafeR o P' k R Q) :
    SafeR o P (.dec "i0" (.var "i") (zeros lineLocals (lineFragP News.SessionSpec.lineLimit k))) R Q := by
  refine dec (P' := fun s => P s ∧ s.locals "i0" = some (BitVec.ofNat 64 i0)) (Q' := Q)
    (fun s hs => ⟨BitVec.ofNat 64 i0, (hP s hs).i, hPset s "i0" _ hs (by simp), by simp [setLocal]⟩) ?_
    (fun s t _ hq => hQ t "i0" (s.locals "i0") hq (by simp))
  refine zeros_runQ lineLocals (fun s y w ⟨hs, hi⟩ hy => ⟨hPset s y w hs (List.mem_cons_of_mem _ hy), ?_⟩)
    (fun t y v hq hy => hQ t y v hq (List.mem_cons_of_mem _ hy)) ?_
  · have : y ≠ "i0" := by
      simp only [lineLocals, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [setLocal, Ne.symm this, hi]
  exact serve_frame o b c q i0 A (fun s ⟨⟨hs, _⟩, hb⟩ => ⟨hP s hs, hb⟩)
    (fun s s' ⟨⟨hs, hi⟩, _⟩ => hnext s s' hs hi) hk

/-- `serve`'s loop body where octets are held: the block's check, the start, the framer's locals and the framer. Then
the rest. -/
def framing (rest : List Syntax.PStmt) : List Syntax.PStmt :=
  [SessionStore.keptIn (SessionStore.ld (Syntax.v "blk")) News.SessionSpec.lineLimit,
   .dec "i0" (Syntax.v "i")] ++ lineDecs ++ lineFrag News.SessionSpec.lineLimit ++ rest

/-- What `serve`'s loop body runs after the framer. -/
def serveRest : List Syntax.PStmt :=
  (match (Session.serve[7]? : Option Syntax.PStmt) with
   | some (Syntax.PStmt.while _ [Syntax.PStmt.ite _ _ els]) => els
   | _ => []).drop 19

/-- **`serve` names the framer's block, the held octets, their number and the place, and checks
them**… -/
theorem serve_head :
    Session.serve.take 7 =
      [.dec "blk" (Syntax.atOff (Syntax.v "cb") cFramer), .dec "p" (Syntax.atOff (Syntax.v "cb") cHeld),
       .dec "n" (SessionStore.fld "cb" cHeldLen), .dec "i" (SessionStore.fld "cb" cHeldPos),
       .dec "sv" (Syntax.n 1), SessionStore.keptIn (Syntax.v "n") data,
       SessionStore.keptIn (Syntax.v "i") data] := rfl

/-- **…and its loop, while the place is not the held octets' end, frames them so.** -/
theorem serve_loop :
    Session.serve[7]? = some (.while (Syntax.v "sv")
      [.ite (Syntax.eEq (Syntax.v "i") (Syntax.v "n")) [.assign "sv" (Syntax.n 0)]
        (framing (serveRest.headD (.ret (Syntax.n 0)) :: serveRest.tail))]) := rfl

/-! ## The block framer in `postFeed` -/

/-- An octet `postFeed` takes: read from the held octets at `i`, the phase and mark from the post's slot. The count is
emptied, then the phase logic runs. -/
def octet (rest : List Syntax.PStmt) : List Syntax.PStmt :=
  [.assign "b" (.loadb (Syntax.eAdd (Syntax.v "p") (Syntax.v "i"))), SessionStore.inc "i",
   .assign "ph" (SessionStore.zw zPh), .assign "bad" (SessionStore.zw zBad),
   .assign "size" (Syntax.n 0), .assign "kind" (Syntax.n 0)] ++ logicS 2 ++ rest

/-- …as it lowers, `k` after it. -/
def octetP (k : PancakeProg) : PancakeProg :=
  .seq (.assign "b" (.loadByte (.op .add (.var "p") (.var "i"))))
  (.seq (.assign "i" (.op .add (.var "i") (.const 1)))
  (.seq (.assign "ph" (.loadWord (.op .add (.var "zs") (.const (BitVec.ofNat 64 zPh)))))
  (.seq (.assign "bad" (.loadWord (.op .add (.var "zs") (.const (BitVec.ofNat 64 zBad)))))
  (.seq (.assign "size" (.const 0))
  (.seq (.assign "kind" (.const 0))
  (.seq (.assign "pre" (.const 0))
  (.seq (.assign "post" (.const 0))
  (.seq (phaseP 2) k))))))))

/-- What `postFeed` has at an octet: the octet `y` where `p` and `i` point. The phase and mark of `S` lie in the slot
`zs` names; the logic's locals are bound. -/
structure AtOctet (S : BlockState) (y : Byte) (pw iw zs : Word) (s : PancakeState σ) : Prop where
  p : s.locals "p" = some pw
  i : s.locals "i" = some iw
  byte : memLoadByte s.memory s.memaddrs s.be (pw + iw) = some y
  slot : s.locals "zs" = some zs
  phA : s.memaddrs (zs + BitVec.ofNat 64 zPh) = true
  ph : s.memory (zs + BitVec.ofNat 64 zPh) = BitVec.ofNat 64 (phaseCode S.phase)
  badA : s.memaddrs (zs + BitVec.ofNat 64 zBad) = true
  bad : s.memory (zs + BitVec.ofNat 64 zBad) = bw S.bad
  bound : ∀ v, v ∈ ["b", "ph", "bad", "size", "kind", "held", "pre", "post"] →
    ∃ w, s.locals v = some w

/-- An assignment and what follows run as what follows on the assigned state. -/
theorem assign_seq (o : Oracle σ) {x : String} {e : PancakeExp} {k : PancakeProg}
    {s : PancakeState σ} {val old : Value} (he : eval s e = some val) (hx : s.locals x = some old) :
    PancakeSem o (.seq (.assign x e) k) s =
      PancakeSem o k { s with locals := setLocal s.locals x val } := by
  rw [Components.seq_run, PancakeSem.eq_3]
  simp [he, hx]

/-- The locals an octet's statements write. -/
def octetWrites : List String := ["b", "i", "ph", "bad", "size", "kind", "held", "pre", "post"]

/-- The plan reads only the phase and the mark. -/
theorem plan_emptied (S : BlockState) (y : Byte) : plan { S with size := 0, buf := [] } y = plan S y := by
  unfold plan; rfl

/-- **`postFeed` runs an octet through the block framer's phase logic**, the frame emptied of its octets. What follows
runs with memory, code and other locals unchanged, the octet read and the place moved. The plan's decision is in the
logic's locals. -/
theorem octet_run (o : Oracle σ) (S : BlockState) (y : Byte) (pw iw zs : Word) (s : PancakeState σ)
    (h : AtOctet S y pw iw zs s) :
    ∃ s', (∀ k, PancakeSem o (octetP k) s = PancakeSem o k s') ∧
      s'.memory = s.memory ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.clock = s.clock ∧
      s'.ffi = s.ffi ∧ s'.baseAddr = s.baseAddr ∧ s'.code = s.code ∧
      (∀ v, v ∉ octetWrites → s'.locals v = s.locals v) ∧
      s'.locals "i" = some (iw + 1) ∧ s'.locals "b" = some (y.setWidth 64) ∧
      s'.locals "size" = some 0 ∧
      if (plan S y).ends then
        s'.locals "pre" = some 0#64 ∧ s'.locals "post" = some 0#64 ∧ s'.locals "ph" = some 0#64 ∧
        s'.locals "bad" = some 0#64 ∧
        s'.locals "kind" = some (BitVec.ofNat 64 (blockCode (result 2 { S with size := 0, buf := [] }).kind)) ∧
        s'.locals "held" = some (BitVec.ofNat 64 (heldLen 2 { S with size := 0, buf := [] }))
      else
        s'.locals "pre" = some (bw (plan S y).pre) ∧ s'.locals "post" = some (bw (plan S y).post) ∧
        s'.locals "ph" = some (BitVec.ofNat 64 (phaseCode (plan S y).phase)) ∧
        s'.locals "bad" = some (bw (plan S y).bad) ∧ s'.locals "kind" = some 0 ∧
        s'.locals "held" = s.locals "held" := by
  obtain ⟨hp, hi, hy, hzs, hphA, hph, hbadA, hbad, hbd⟩ := h
  obtain ⟨wb, hwb⟩ := hbd "b" (by simp)
  obtain ⟨wph, hwph⟩ := hbd "ph" (by simp)
  obtain ⟨wbad, hwbad⟩ := hbd "bad" (by simp)
  obtain ⟨wsize, hwsize⟩ := hbd "size" (by simp)
  obtain ⟨wkind, hwkind⟩ := hbd "kind" (by simp)
  obtain ⟨wheld, hwheld⟩ := hbd "held" (by simp)
  obtain ⟨wpre, hwpre⟩ := hbd "pre" (by simp)
  obtain ⟨wpost, hwpost⟩ := hbd "post" (by simp)
  let s8 : PancakeState σ := { s with locals :=
    (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal s.locals
      "b" (y.setWidth 64)) "i" (iw + 1)) "ph" (BitVec.ofNat 64 (phaseCode S.phase))) "bad" (bw S.bad))
      "size" 0) "kind" 0) "pre" 0) "post" 0) }
  have hin : PhaseIn s8 { S with size := 0, buf := [] } y :=
    ⟨by simp [s8, setLocal], by simp [s8, setLocal], by simp [s8, setLocal], by simp [s8, setLocal],
     by simp [s8, setLocal], by simp [s8, setLocal], ⟨0, by simp [s8, setLocal]⟩,
     ⟨wheld, by simp [s8, setLocal, hwheld]⟩⟩
  obtain ⟨s', hs', hout⟩ := phase_run o 2 (by decide) s8 { S with size := 0, buf := [] } y
    (by simp) hin
  have hsame : Safe.Same s8 s' := by
    have := Safe.sem_same o s8.clock (phaseP 2) s8 (Nat.le_refl _)
    rwa [hs'] at this
  obtain ⟨hm, hma, hbe, hcl, hffi, hba, hloc, hplan⟩ := hout
  refine ⟨s', fun k => ?_, hm, hma, hbe, hcl, hffi, hba, hsame.2.2.2, fun v hv => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [octetP]
    rw [assign_seq o (val := y.setWidth 64) (old := wb) (by simp [eval, hp, hi, hy]) hwb,
      assign_seq o (val := iw + 1) (old := iw) (by simp [eval, setLocal, hi]) (by simp [setLocal, hi]),
      assign_seq o (val := BitVec.ofNat 64 (phaseCode S.phase)) (old := wph)
        (by simp [eval, setLocal, hzs, hphA, hph]) (by simp [setLocal, hwph]),
      assign_seq o (val := bw S.bad) (old := wbad) (by simp [eval, setLocal, hzs, hbadA, hbad])
        (by simp [setLocal, hwbad]),
      assign_seq o (val := 0) (old := wsize) rfl (by simp [setLocal, hwsize]),
      assign_seq o (val := 0) (old := wkind) rfl (by simp [setLocal, hwkind]),
      assign_seq o (val := 0) (old := wpre) rfl (by simp [setLocal, hwpre]),
      assign_seq o (val := 0) (old := wpost) rfl (by simp [setLocal, hwpost]),
      Components.seq_run, hs']
  · simp only [octetWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hv
    rw [hloc v h8 h9 h3 h4 h5 h6 h7]
    simp [s8, setLocal, h1, h2, h3, h4, h5, h6, h8, h9]
  · rw [hloc "i" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s8, setLocal]
  · rw [hloc "b" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s8, setLocal]
  · rw [plan_emptied] at hplan
    by_cases hend : (plan S y).ends
    · simp only [hend, if_true] at hplan
      rw [hplan.2.2.2.2.1]; simp [s8, setLocal]
    · simp only [hend, Bool.false_eq_true, if_false] at hplan
      rw [hplan.2.2.2.2.1]; simp [s8, setLocal]
  · rw [plan_emptied] at hplan
    by_cases hend : (plan S y).ends
    · simp only [hend, if_true] at hplan ⊢
      exact ⟨hplan.1, hplan.2.1, hplan.2.2.1, hplan.2.2.2.1, hplan.2.2.2.2.2.1, hplan.2.2.2.2.2.2⟩
    · simp only [hend, Bool.false_eq_true, if_false] at hplan ⊢
      refine ⟨hplan.1, hplan.2.1, hplan.2.2.1, hplan.2.2.2.1, ?_, ?_⟩
      · rw [hplan.2.2.2.2.2.1]; simp [s8, setLocal]
      · rw [hplan.2.2.2.2.2.2]; simp [s8, setLocal, hwheld]

/-- **What the logic decides is `PostSpec.frameOctet`'s**: the frame's next phase and mark. At the block's end its
verdict; before it the octets it adds, a CR held back and the octet. -/
theorem octet_frameOctet (S : BlockState) (y : Byte) :
    (PostSpec.frameOctet S y).1.phase = (plan S y).phase ∧
      (PostSpec.frameOctet S y).1.bad = (plan S y).bad ∧
      (PostSpec.frameOctet S y).2.2 =
        (if (plan S y).ends then some ((result 2 { S with size := 0, buf := [] }).kind == .accepted)
          else none) ∧
      ((plan S y).ends = false →
        (PostSpec.frameOctet S y).2.1 =
          (if (plan S y).pre then [CR] else []) ++ (if (plan S y).post then [y] else [])) := by
  unfold PostSpec.frameOctet
  rw [blockStep_plan, plan_emptied]
  cases hend : (plan S y).ends
  · simp only [Bool.false_eq_true, if_false]
    refine ⟨by simp [BlockState.at], by simp [BlockState.at], by simp, fun _ => ?_⟩
    cases (plan S y).pre <;> cases (plan S y).post <;> simp [putIf, put, BlockState.at]
  · simp only [if_true]
    unfold plan at hend ⊢
    cases hph : S.phase <;> simp only [hph] at hend ⊢ <;> (repeat' split at hend) <;>
      simp_all [BlockState.fresh]

/-- What `postFeed` runs after an octet's logic. -/
def feedRest : List Syntax.PStmt :=
  (match (SessionStore.postFeed.body[18]? : Option Syntax.PStmt) with
   | some (Syntax.PStmt.while _ [Syntax.PStmt.ite _ thn _]) => thn
   | _ => []).drop 9

/-- **`postFeed` names connection `c`'s record, the post's slot, held octets, count and place**, and declares the
logic's locals… -/
theorem feed_head :
    SessionStore.postFeed.body.take 18 =
      [SessionStore.keptIn (Syntax.v "c") (conns - 1),
       .dec "cb" (Syntax.eAdd (SessionStore.at_ tableOff) (Syntax.eMul (Syntax.v "c") (Syntax.n connSlot))),
       SessionStore.keptIn (Syntax.v "k") (posts - 1),
       .dec "zs" (Syntax.eAdd (SessionStore.at_ slotsOff) (Syntax.eMul (Syntax.v "k") (Syntax.n slotLen))),
       .dec "p" (Syntax.atOff (Syntax.v "cb") cHeld), .dec "nn" (SessionStore.fld "cb" cHeldLen),
       .dec "i" (SessionStore.fld "cb" cHeldPos), SessionStore.keptIn (Syntax.v "nn") data,
       SessionStore.keptIn (Syntax.v "i") data, .dec "ph" (Syntax.n 0), .dec "bad" (Syntax.n 0),
       .dec "size" (Syntax.n 0), .dec "kind" (Syntax.n 0), .dec "held" (Syntax.n 0),
       .dec "b" (Syntax.n 0), .dec "pre" (Syntax.n 0), .dec "post" (Syntax.n 0),
       .dec "go" (Syntax.n 1)] := rfl

/-- **…and its loop, while it takes octets, takes each so.** -/
theorem feed_loop :
    SessionStore.postFeed.body[18]? = some (.while (Syntax.v "go")
      [.ite (Syntax.eAnd (Syntax.eLt (Syntax.v "i") (Syntax.v "nn")) SessionStore.takesE)
        (octet (feedRest.headD (.ret (Syntax.n 0)) :: feedRest.tail)) [.assign "go" (Syntax.n 0)]]) :=
  rfl

/-! ## The premises can hold -/

/-- A base that puts connection zero's framer's block at address zero. -/
def base0 : Word := -(BitVec.ofNat 64 (tableOff + 0 * connSlot) + BitVec.ofNat 64 cFramer)

theorem blockAt_base0 : blockAt base0 0 = 0 := by
  simp only [blockAt, recordAt, base0]
  rw [BitVec.add_assoc, BitVec.add_left_neg]
  rfl

/-- The record's locals in a heap of zeros, every word addressable, one held octet of zero. -/
def frameState : PancakeState Unit :=
  { bareState () with locals := fun x =>
      if x = "blk" then some (blockAt base0 0) else if x = "p" then some (heldAt base0 0)
      else if x = "n" then some 1 else if x = "i" then some 0 else none }

theorem atCheck_witness : AtCheck base0 0 [0#8] 0 .fresh frameState where
  blk := by simp [frameState]
  p := by simp [frameState]
  n := by simp [frameState]
  i := by simp [frameState]
  i0 := Nat.zero_le _
  len := by decide
  holds := holds_zero _ _ rfl rfl rfl
  fits := by unfold Fits; decide
  chunk := fun j h => by
    obtain rfl : j = 0 := by simp at h; omega
    rw [heldAt, held_at, show recordAt base0 0 + BitVec.ofNat 64 cFramer = blockAt base0 0 from rfl,
      blockAt_base0]
    show memLoadByte (fun _ => 0) (fun _ => true) false
      (0 + 40#64 + BitVec.ofNat 64 News.SessionSpec.lineLimit + 0#64) = some 0#8
    decide
  room := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  al := by rw [blockAt_base0]; rfl
  fit := by rw [blockAt_base0]; decide

/-- An octet of zero at the start, the slot a fresh frame's, in a heap of zeros. -/
def octetState : PancakeState Unit :=
  { bareState () with locals := fun x =>
      if x ∈ ["p", "i", "zs", "b", "ph", "bad", "size", "kind", "held", "pre", "post"] then some 0
      else none }

theorem atOctet_witness : AtOctet .fresh 0#8 0 0 0 octetState where
  p := by simp [octetState]
  i := by simp [octetState]
  byte := by decide
  slot := by simp [octetState]
  phA := rfl
  ph := rfl
  badA := rfl
  bad := rfl
  bound := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by simp [octetState]⟩

end DN.Server.SessionFrame
