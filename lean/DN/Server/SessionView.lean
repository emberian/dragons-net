-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionClassify

/-!
# DN.Server.SessionView

`viewClassify` keeps its contract `FnOk`: on a line of words, if it returns, it gives back zero and leaves in the
return word the code of the reply `CommandSpec.answerIn` gives OVER, HDR, XOVER and XHDR (`viewClassify_ok`). The own
words it writes lie apart from the line and the texts it reads (`not_vWords`); what they hold is not shown. The
fragments hold if they go on. `classify_premises` shows `classify_run`'s premises met together.
-/

namespace DN.Server.SessionClassify

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Bytes DN.Compiler.Preservation DN.Compiler.Frag DN.Server
  DN.News DN.News.WordsRun DN.News.FrameSpec DN.Server.SessionText DN.Server.SessionWords
open DN.Server.SessionLayout (framerHead texts textAt ownOff ownTexts ownRet ownVSel ownVs ownVl ownLo ownHi ownFs
  ownFl ownNamed ownWs ownWl ownStore conns tableOff connSlot cFramer)
open DN.News.FramerCode (bw)
open DN.Server.SessionCheck (zeroState)

variable {σ : Type}

/-! ## `viewClassify` -/

/-! ### The words it writes lie apart from those it reads -/

/-- The own words `viewClassify` writes. -/
def vOffs : List Nat := [ownVSel, ownVs, ownVl, ownLo, ownHi, ownFs, ownFl]

/-- The addresses of those words. -/
def vWords (b : Word) : List Word := vOffs.map fun x => b + BitVec.ofNat 64 (ownOff + x)

theorem vOffs_facts : ∀ X ∈ vOffs, (ownOff + X) % 8 = 0 ∧ ownOff + X + 8 ≤ ownOff + ownTexts := by decide +kernel

/-- A place `x` past the own words is none of `vWords`. -/
theorem not_vWords {b : Word} (hb : b.toNat % 8 = 0) {x : Nat} (hx : ownOff + ownTexts ≤ x) (h64 : x < 2 ^ 64) :
    byteAlign (b + BitVec.ofNat 64 x) ∉ vWords b := by
  simp only [vWords, List.mem_map, not_exists, not_and]
  intro X hX e
  obtain ⟨h1, h2⟩ := vOffs_facts X hX
  exact own_far hb h1 (by omega) h64 e.symm

theorem vOffs_cls : ∀ X ∈ vOffs, X ∈ clsOffs := by decide

theorem vWords_cls (b : Word) : ∀ a ∈ vWords b, a ∈ clsWords b := by
  intro a ha
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp ha
  exact List.mem_map.mpr ⟨X, vOffs_cls X hX, rfl⟩

section ViewTree
open DN.Compiler.Syntax DN.Server.Session
open DN.Server.SessionStore (ne or2 ifs at_ ld keptIn inc give)
open DN.Server.SessionLayout (ownOff ownVs ownVl ownLo ownHi ownFs ownFl ownVSel cFramer conns)
open DN.News.SessionSpec (lineLimit)

/-- An own word set. -/
def vset (o : Nat) (e : PExpr) : PStmt := .store (at_ (ownOff + o)) e
/-- The reply's code set. -/
def vsay (r : News.CommandSpec.Reply) : PStmt := .assign "r" (n (replyCode r))

/-- A message-id, where `ids` is one, or a range: `sel` one or two and their places or bounds kept, else zero. -/
def vpick (s l ids : PExpr) : List PStmt :=
  [.assign "ok" (n 0), ifs ids (messageIdCheckAt s l),
   .ite (v "ok") [.assign "sel" (n 1), vset ownVs s, vset ownVl l]
     (rangeCheckAt s l ++ [ifs (v "ok") [.assign "sel" (n 2), vset ownLo (v "lo"), vset ownHi (v "hi")]])]

/-- OVER's and XOVER's arguments: none, or a message-id or a range. -/
def overTree : List PStmt :=
  [ifs (eEq (v "args") (n 0)) [.assign "good" (n 1)],
   ifs (eEq (v "args") (n 1))
     (vpick (v "s1") (v "l1") (eEq (v "cmd") (n 17)) ++ [.assign "good" (ne (v "sel") (n 0))]),
   ifs (v "good") [vsay (.over false .current)]]

/-- A field's reply: served where it is no metadata item, or `:bytes` or `:lines`. -/
def fieldServe : List PStmt :=
  [vset ownFs (v "s1"), vset ownFl (v "l1"), .dec "served" (eEq (v "meta") (n 0))] ++
    wordIsAt "s1" "l1" SessionStore.tMetaBytes ++ [ifs (v "eqk") [.assign "served" (n 1)]] ++
    wordIsAt "s1" "l1" SessionStore.tMetaLines ++ [ifs (v "eqk") [.assign "served" (n 1)]] ++
    [.ite (v "served") [vsay (.hdr false [] .current)] [vsay .fieldRefused]]

/-- HDR's field: a header's name or a metadata item's, and whether it is served. -/
def fieldTree : List PStmt :=
  [.dec "f0" (kept (v "s1")), .dec "meta" (eEq (v "f0") (n 58)),
   .assign "ok" (eLe (eAdd (n 1) (v "meta")) (v "l1")), .assign "jq" (v "meta"),
   .while (eAnd (v "ok") (eLt (v "jq") (v "l1")))
     [.dec "cz" (kept (eAdd (v "s1") (v "jq"))),
      .assign "ok" (or2 (between 33 57 (v "cz")) (between 59 126 (v "cz"))), inc "jq"],
   ifs (v "ok") fieldServe]

/-- HDR's and XHDR's arguments: a field, and a message-id or a range or nothing. -/
def hdrTree : List PStmt :=
  [ifs (eEq (v "args") (n 1)) [.assign "good" (n 1)],
   ifs (eEq (v "args") (n 2)) (vpick (v "s2") (v "l2") (n 1) ++ [.assign "good" (ne (v "sel") (n 0))]),
   ifs (v "good") fieldTree]

/-- The connection and its line, bounds checked. -/
def viewHead : List PStmt :=
  [keptIn (v "c") (conns - 1), .dec "blk" (atOff (record (v "c")) cFramer),
   .dec "kept" (ld (atOff (v "blk") 32)), keptIn (v "kept") lineLimit]

/-- The words' places and lengths, bounds checked. -/
def viewKept : List PStmt :=
  [keptIn (v "s1") lineLimit, keptIn (v "l1") lineLimit, keptIn (v "s2") lineLimit, keptIn (v "l2") lineLimit,
   keptIn (v "s3") lineLimit, keptIn (v "l3") lineLimit]

/-- The locals the branches use. -/
def viewDecs : List PStmt :=
  [.dec "args" (eSub (v "w") (n 1)), .dec "r" (n (replyCode .syntax)), .dec "ok" (n 0),
   .dec "val" (n 0), .dec "jq" (n 0), .dec "lo" (n 0), .dec "hi" (n 0), .dec "sel" (n 0),
   .dec "good" (n 0), .dec "eqk" (n 0)]

/-- `viewClassify` up to its last words. -/
def viewBody : List PStmt := viewHead ++ scanWords 4 ++ viewKept ++ viewDecs ++
  [.ite (or2 (eEq (v "cmd") (n 17)) (eEq (v "cmd") (n 19))) overTree hdrTree, vset ownVSel (v "sel")]

theorem view_eq : Session.viewClassify.body = viewBody ++ give (v "r") := rfl

end ViewTree

/-! ### Places in the session's words -/

/-- The locals `viewClassify` declares. -/
def vNames : List String :=
  ["blk", "kept", "w", "s0", "l0", "s1", "l1", "s2", "l2", "s3", "l3", "inw", "ws", "q", "cq", "args", "r", "ok", "val",
   "jq", "lo", "hi", "sel", "good", "eqk", "cz", "dn", "dp", "f0", "meta", "served"]

/-- Within `viewClassify` once its locals are declared, from its entry `e`: every word but `vWords` as at `e`, the
line's block and length, the words' count and places, the arguments' count, the locals bound. -/
structure VAt (b : Word) (ci : Nat) (L : List Byte) (e u : PancakeState σ) : Prop where
  loc : ∀ y, y ∉ vNames → u.locals y = e.locals y
  memory : ∀ a, a ∉ vWords b → u.memory a = e.memory a
  memaddrs : u.memaddrs = e.memaddrs
  be : u.be = e.be
  base : u.baseAddr = e.baseAddr
  code : u.code = e.code
  blk : u.locals "blk" = some (SessionFrame.blockAt b ci)
  kept : u.locals "kept" = some (BitVec.ofNat 64 L.length)
  w : u.locals "w" = some (BitVec.ofNat 64 (spans L).length)
  s1 : u.locals "s1" = some (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).1)
  l1 : u.locals "l1" = some (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).2)
  s2 : u.locals "s2" = some (BitVec.ofNat 64 ((spans L).getD 2 (0, 0)).1)
  l2 : u.locals "l2" = some (BitVec.ofNat 64 ((spans L).getD 2 (0, 0)).2)
  args : u.locals "args" = some (BitVec.ofNat 64 ((spans L).length - 1))
  r : u.locals "r" = some (BitVec.ofNat 64 (Session.replyCode .syntax))
  ok : ∃ v, u.locals "ok" = some v
  val : ∃ v, u.locals "val" = some v
  jq : ∃ v, u.locals "jq" = some v
  lo : ∃ v, u.locals "lo" = some v
  hi : ∃ v, u.locals "hi" = some v
  sel : ∃ v, u.locals "sel" = some v
  good : ∃ v, u.locals "good" = some v
  eqk : ∃ v, u.locals "eqk" = some v

theorem vat_clock (b : Word) (ci : Nat) (L : List Byte) (e : PancakeState σ) : Safe.ClockFree (VAt b ci L e) :=
  fun _ _ h => { h with }

theorem vat_and {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {q : Assn σ} (hq : Safe.ClockFree q) :
    Safe.ClockFree (fun u => VAt b ci L e u ∧ q u) := fun u k h => ⟨vat_clock b ci L e u k h.1, hq u k h.2⟩

/-- The line's octets read through the words written. -/
theorem vat_line {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ} (he : VEntry b ci K L e)
    (h : VAt b ci L e u) : LineIn (SessionFrame.blockAt b ci) L u := by
  have hsh := he.short
  have h8 := SessionAppend.block_facts.limit
  refine ⟨h.blk, h.kept, fun j hj => ?_, by omega⟩
  obtain ⟨i1, i2⟩ := SessionAppend.block_in (x := 40 + j) he.hci (by rw [SessionAppend.block_facts.head]; omega)
  have hs := SessionAppend.size_lt
  have hb := he.bytes j hj
  rw [add_ofNat, SessionAppend.blockAt_off] at hb ⊢
  rw [h.memaddrs, h.be, load_of_word (h.memory _ (not_vWords he.hb (by omega) (by omega)))]
  exact hb

/-- The texts read through the words written. -/
theorem vat_texts {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ} (he : VEntry b ci K L e)
    (h : VAt b ci L e u) : SessionAppend.TextsIn b u.memory u.memaddrs u.be := by
  intro k hk i hi
  have hb := he.texts k hk i hi
  have ht := SessionAppend.text_below hk
  obtain ⟨T, hT⟩ := SessionAppend.lay
  have hl : (texts.getD k []).length = Session.textLen k := rfl
  rw [hT.eq] at ht
  have := hT.room
  rw [add_ofNat] at hb ⊢
  rw [h.memaddrs, h.be, load_of_word (h.memory _ (not_vWords he.hb (by omega) (by omega)))]
  exact hb

/-- A bound check that holds: nothing happens. -/
theorem keptIn_skip (o : Oracle σ) {x : String} {hi : Nat} (hhi : hi < 2 ^ 63) {P : Assn σ}
    (hcl : Safe.ClockFree P) (hP : ∀ s, P s → ∃ n, s.locals x = some (BitVec.ofNat 64 n) ∧ n ≤ hi) :
    Frag o [SessionStore.keptIn (Syntax.v x) hi] P P :=
  frag_oneR (SessionRun.keptIn_lower rfl hi) rfl hcl fun R => SessionRun.keptG_pass o R hhi fun s h => by
    obtain ⟨n, hn, hle⟩ := hP s h; exact ⟨n, hle, by simp only [eval]; exact hn⟩

/-- After the head of `viewClassify`: its block and the line's length bound, the rest as at `e`. -/
def VHead (b : Word) (ci : Nat) (L : List Byte) (e u : PancakeState σ) : Prop :=
  u.locals "blk" = some (SessionFrame.blockAt b ci) ∧ u.locals "kept" = some (BitVec.ofNat 64 L.length) ∧
    (∀ y, y ∉ ["blk", "kept"] → u.locals y = e.locals y) ∧ u.memory = e.memory ∧ u.memaddrs = e.memaddrs ∧
    u.be = e.be ∧ u.baseAddr = e.baseAddr ∧ u.code = e.code

/-- **`viewClassify`'s head**: connection `ci`'s block and the line's length. -/
theorem vhead_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) : Frag o viewHead (Like e) (VHead b ci L e) := by
  have hci := he.hci
  have hsh := he.short
  obtain ⟨_, _, _, h4, h5, _, _, h8⟩ := SessionAppend.block_facts
  let P1 : Assn σ := fun u => u.locals "blk" = some (SessionFrame.blockAt b ci) ∧
    (∀ y, y ∉ ["blk"] → u.locals y = e.locals y) ∧ u.memory = e.memory ∧ u.memaddrs = e.memaddrs ∧
    u.be = e.be ∧ u.baseAddr = e.baseAddr ∧ u.code = e.code
  have f1 := keptIn_skip o (x := "c") (hi := conns - 1) (by omega) (like_clock e) fun s h =>
    ⟨ci, by rw [h.locals]; exact he.c, by omega⟩
  have f2 : Frag o [.dec "blk" (Syntax.atOff (Session.record (Syntax.v "c")) cFramer)] (Like e) P1 :=
    frag_dec o SessionCheck.blk_lower fun s h => ⟨SessionFrame.blockAt b ci, by
        rw [SessionCheck.blk_eval (h.base.trans he.base) (by rw [h.locals]; exact he.c), SessionCheck.gnBlock_eq],
      by simp [setLocal], fun y hy => by simp at hy; simp [setLocal, hy, h.locals], h.memory, h.memaddrs, h.be,
      h.base, h.code⟩
  -- the line's length, from the block's word
  obtain ⟨i1, i2⟩ := SessionAppend.block_in (x := 32) hci (by rw [SessionAppend.block_facts.head, h8]; omega)
  have hal : (SessionAppend.tOff + ci * connSlot + cFramer + 32) % 8 = 0 := by
    obtain ⟨T, hT⟩ := SessionAppend.lay
    have a1 := SessionAppend.block_facts.framerAl
    have a2 := SessionAppend.block_facts.slotAl
    have := hT.aligned
    rw [hT.eq]
    have : ci * connSlot % 8 = 0 := by rw [Nat.mul_mod, a2]; simp
    omega
  have hadr : e.memaddrs (SessionFrame.blockAt b ci + BitVec.ofNat 64 32) = true := by
    have := SessionAppend.nums.own64
    rw [SessionAppend.blockAt_off]; exact he.hcov.2 _ (by simp only [Analyzer.floor]; omega) i2 hal
  have f3 : Frag o [.dec "kept" (SessionStore.ld (Syntax.atOff (Syntax.v "blk") 32))] P1 (VHead b ci L e) :=
    frag_dec o (E := .loadWord (.op .add (.var "blk") (.const (BitVec.ofNat 64 32)))) rfl fun s h =>
      ⟨BitVec.ofNat 64 L.length, by
        simp only [eval, h.1, h.2.2.2.1, hadr, if_true, h.2.2.1, he.kept],
      by simp [setLocal, h.1], by simp [setLocal], fun y hy => by
        simp at hy; simp [setLocal, hy.2]; exact h.2.1 y (by simp [hy.1]), h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  have f4 := keptIn_skip o (x := "kept") (hi := News.SessionSpec.lineLimit) (by rw [h8]; decide)
    (P := VHead b ci L e) (fun _ _ h => h) fun s h => ⟨L.length, h.2.1, hsh⟩
  exact frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 (frag_append (xs := [_]) f3 f4))

/-- After the scan: its words from the head's state `u1`. -/
def VScan (b : Word) (ci : Nat) (L : List Byte) (e u : PancakeState σ) : Prop :=
  ∃ u1, VHead b ci L e u1 ∧ WordsAt L (scanNmFrom 0 4) u1 u

theorem vscan_clock (b : Word) (ci : Nat) (L : List Byte) (e : PancakeState σ) : Safe.ClockFree (VScan b ci L e) :=
  fun _ _ ⟨u1, h1, h2⟩ => ⟨u1, h1, { h2 with }⟩

theorem vscan_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) : Frag o (Session.scanWords 4) (VHead b ci L e) (VScan b ci L e) :=
  frag_each o (lowK_any _ (k := .skip) (c := _) rfl) fun u1 h1 => by
    have hl : LineIn (SessionFrame.blockAt b ci) L u1 := ⟨h1.1, h1.2.1, fun j hj => by
      rw [h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1]; exact he.bytes j hj, by
      have := he.short; simp [News.SessionSpec.lineLimit] at this; omega⟩
    exact frag_conseq (scanWords_frag o 4 nm4_ok (by decide) (by decide) hl) (fun _ h => h)
      fun u hu => ⟨u1, h1, hu⟩

/-- The six bound checks of the second to fourth words. -/
theorem vkept_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) : Frag o viewKept (VScan b ci L e) (VScan b ci L e) := by
  have h8 := SessionAppend.block_facts.limit
  have hsh := he.short
  have sl : ∀ (j : Nat) (hj : j < 4) (sel : String × String → String), (sel = Prod.fst ∨ sel = Prod.snd) →
      ∀ s, VScan b ci L e s → ∃ n, s.locals (sel (scanNmFrom 0 4)[j]) = some (BitVec.ofNat 64 n) ∧
        n ≤ News.SessionSpec.lineLimit := fun j hj sel hs s ⟨u1, _, h2⟩ => by
    have := h2.slots j (by simp [scanNmFrom]; omega)
    have hb := spans_getD_le L j
    rcases hs with rfl | rfl
    · exact ⟨_, this.1, by omega⟩
    · exact ⟨_, this.2, by omega⟩
  have k : ∀ (j : Nat) (hj : j < 4) (sel : String × String → String), (sel = Prod.fst ∨ sel = Prod.snd) →
      Frag o [SessionStore.keptIn (Syntax.v (sel (scanNmFrom 0 4)[j])) News.SessionSpec.lineLimit]
        (VScan b ci L e) (VScan b ci L e) := fun j hj sel hs =>
    keptIn_skip o (by rw [h8]; decide) (vscan_clock b ci L e) (sl j hj sel hs)
  exact frag_append (xs := [_]) (k 1 (by decide) Prod.fst (Or.inl rfl)) (frag_append (xs := [_])
    (k 1 (by decide) Prod.snd (Or.inr rfl)) (frag_append (xs := [_]) (k 2 (by decide) Prod.fst (Or.inl rfl))
    (frag_append (xs := [_]) (k 2 (by decide) Prod.snd (Or.inr rfl)) (frag_append (xs := [_])
    (k 3 (by decide) Prod.fst (Or.inl rfl)) (k 3 (by decide) Prod.snd (Or.inr rfl))))))

/-- After `args` and `r`: from a scanned state `u2`. -/
def VArgs (b : Word) (ci : Nat) (L : List Byte) (e u : PancakeState σ) : Prop :=
  ∃ u2, VScan b ci L e u2 ∧ (∀ y, y ∉ ["args", "r"] → u.locals y = u2.locals y) ∧
    u.locals "args" = some (BitVec.ofNat 64 ((spans L).length - 1)) ∧
    u.locals "r" = some (BitVec.ofNat 64 (Session.replyCode .syntax)) ∧
    u.memory = u2.memory ∧ u.memaddrs = u2.memaddrs ∧ u.be = u2.be ∧ u.baseAddr = u2.baseAddr ∧ u.code = u2.code

/-- The locals `VAt` asks to be bound, those `viewClassify` declares zero. -/
def vBound : List String := ["ok", "val", "jq", "lo", "hi", "sel", "good", "eqk"]

theorem vdecs_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ}
    (hw1 : 1 ≤ (spans L).length) (hsh : L.length < 2 ^ 62) : Frag o viewDecs (VScan b ci L e)
      (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0) := by
  have hsp := spans_length L
  have f1 : Frag o [.dec "args" (Syntax.eSub (Syntax.v "w") (Syntax.n 1))] (VScan b ci L e)
      (fun u => ∃ u2, VScan b ci L e u2 ∧ (∀ y, y ∉ ["args"] → u.locals y = u2.locals y) ∧
        u.locals "args" = some (BitVec.ofNat 64 ((spans L).length - 1)) ∧
        u.memory = u2.memory ∧ u.memaddrs = u2.memaddrs ∧ u.be = u2.be ∧ u.baseAddr = u2.baseAddr ∧
        u.code = u2.code) :=
    frag_dec o (E := .op .sub (.var "w") (.const 1)) rfl fun s h => ⟨_, by
      obtain ⟨u1, _, h2⟩ := h
      simp only [eval, h2.hw]
      rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, SessionCheck.sub_small _ 1 hw1 (by omega)],
      s, h, fun y hy => by simp at hy; simp [setLocal, hy], by simp [setLocal], rfl, rfl, rfl, rfl, rfl⟩
  have f2 : Frag o [.dec "r" (Syntax.n (Session.replyCode .syntax))]
      (fun u => ∃ u2, VScan b ci L e u2 ∧ (∀ y, y ∉ ["args"] → u.locals y = u2.locals y) ∧
        u.locals "args" = some (BitVec.ofNat 64 ((spans L).length - 1)) ∧
        u.memory = u2.memory ∧ u.memaddrs = u2.memaddrs ∧ u.be = u2.be ∧ u.baseAddr = u2.baseAddr ∧
        u.code = u2.code) (VArgs b ci L e) :=
    frag_dec o (E := .const (BitVec.ofNat 64 (Session.replyCode .syntax))) rfl fun s ⟨u2, h, hl, ha, rest⟩ =>
      ⟨BitVec.ofNat 64 (Session.replyCode .syntax), rfl, u2, h, fun y hy => by
      simp at hy; simp only [setLocal, if_neg hy.2]; exact hl y (by simp [hy.1]),
      by simp [setLocal, ha], by simp [setLocal], rest⟩
  let zs := vBound
  have f3 : Frag o (zs.map fun x => .dec x (Syntax.n 0)) (VArgs b ci L e)
      (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0) :=
    frag_each o (lowKK_decs zs) fun u3 h3 => frag_conseq (decs_frag o u3 zs []) (fun u (hu : Like u3 u) =>
        ⟨fun _ h => by simp at h, fun y _ => by rw [hu.locals], hu.memory, hu.memaddrs, hu.be, hu.ffi, hu.base,
          hu.code⟩) fun u hu => by
      simp only [List.nil_append] at hu
      obtain ⟨u2, ⟨u1, h1, h2⟩, hl3, hargs, hr, hm, hd, hbe, hba, hc⟩ := h3
      have z : ∀ y, y ∉ zs → u.locals y = u3.locals y := hu.frame
      have a3 : ∀ y, y ∉ zs → y ∉ ["args", "r"] → u.locals y = u2.locals y := fun y a b => (z y a).trans (hl3 y b)
      have sl1 := h2.slots 1 (by decide)
      have sl2 := h2.slots 2 (by decide)
      have d1 : ∀ y ∈ zs, y ∈ vNames := by decide
      have d2 : ∀ y ∈ scanNames (scanNmFrom 0 4), y ∈ vNames := by decide
      have back : ∀ y, y ∉ zs → y ∉ ["args", "r"] → y ∉ scanNames (scanNmFrom 0 4) → u.locals y = u1.locals y :=
        fun y a b c => (a3 y a b).trans (h2.frame y c)
      refine ⟨⟨fun y hy => ?_, fun a _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩, hu.zero "sel" (by decide), hu.zero "good" (by decide)⟩
      · rw [back y (fun e => hy (d1 y e)) (fun e => hy (by simp at e; rcases e with rfl | rfl <;> decide))
          (fun e => hy (d2 y e))]
        exact h1.2.2.1 y (fun e => hy (by simp at e; rcases e with rfl | rfl <;> decide))
      · rw [hu.memory, hm, h2.memory, h1.2.2.2.1]
      · rw [hu.memaddrs, hd, h2.memaddrs, h1.2.2.2.2.1]
      · rw [hu.be, hbe, h2.be, h1.2.2.2.2.2.1]
      · rw [hu.base, hba, h2.base, h1.2.2.2.2.2.2.1]
      · rw [hu.code, hc, h2.code, h1.2.2.2.2.2.2.2]
      · rw [back "blk" (by decide) (by decide) (by decide)]; exact h1.1
      · rw [back "kept" (by decide) (by decide) (by decide)]; exact h1.2.1
      · rw [a3 "w" (by decide) (by decide)]; exact h2.hw
      · rw [a3 "s1" (by decide) (by decide)]; exact sl1.1
      · rw [a3 "l1" (by decide) (by decide)]; exact sl1.2
      · rw [a3 "s2" (by decide) (by decide)]; exact sl2.1
      · rw [a3 "l2" (by decide) (by decide)]; exact sl2.2
      · rw [z "args" (by decide)]; exact hargs
      · rw [z "r" (by decide)]; exact hr
      all_goals exact ⟨0, hu.zero _ (by decide)⟩
  exact frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 f3)

/-! ### Steps within `viewClassify` -/

/-- The locals `VAt` fixes. -/
def vFixed : List String := ["blk", "kept", "w", "s1", "l1", "s2", "l2", "args", "r"]

theorem vat_but {b : Word} {ci : Nat} {L : List Byte} {e u0 u : PancakeState σ} (h : VAt b ci L e u0)
    {xs : List String} (h2 : SessionCheck.ButFor xs u0 u) (hxs : ∀ y ∈ xs, y ∈ vNames ∧ y ∉ vFixed)
    (hk : ∀ y ∈ vBound, (u0.locals y).isSome → (u.locals y).isSome) : VAt b ci L e u := by
  have fx : ∀ y ∈ vFixed, u.locals y = u0.locals y := fun y hy => h2.locals y fun e => (hxs y e).2 hy
  have bd : ∀ y ∈ vBound, (∃ v, u0.locals y = some v) → ∃ v, u.locals y = some v := fun y hy hv =>
    Option.isSome_iff_exists.mp (hk y hy (Option.isSome_iff_exists.mpr hv))
  exact ⟨fun y hy => by rw [h2.locals y fun e => hy (hxs y e).1]; exact h.loc y hy,
    fun a ha => by rw [h2.memory]; exact h.memory a ha, h2.memaddrs.trans h.memaddrs, h2.be.trans h.be,
    h2.base.trans h.base, h2.code.trans h.code, by rw [fx "blk" (by decide)]; exact h.blk,
    by rw [fx "kept" (by decide)]; exact h.kept, by rw [fx "w" (by decide)]; exact h.w,
    by rw [fx "s1" (by decide)]; exact h.s1, by rw [fx "l1" (by decide)]; exact h.l1,
    by rw [fx "s2" (by decide)]; exact h.s2, by rw [fx "l2" (by decide)]; exact h.l2,
    by rw [fx "args" (by decide)]; exact h.args, by rw [fx "r" (by decide)]; exact h.r, bd "ok" (by decide) h.ok,
    bd "val" (by decide) h.val, bd "jq" (by decide) h.jq, bd "lo" (by decide) h.lo, bd "hi" (by decide) h.hi,
    bd "sel" (by decide) h.sel, bd "good" (by decide) h.good, bd "eqk" (by decide) h.eqk⟩

theorem vat_set {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : VAt b ci L e u) {x : String}
    (hx : x ∈ vNames ∧ x ∉ vFixed) (v : Value) : VAt b ci L e (setL u x v) :=
  vat_but h (SessionCheck.but_set (SessionCheck.but_refl [x] u) (by simp) v)
    (fun y hy => by simp at hy; subst hy; exact hx) fun y _ hy => by
      simp only [setL, setLocal]; split <;> simp_all

/-- An own word `viewClassify` writes, written. -/
theorem vat_store {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : VAt b ci L e u) {X : Nat}
    (hX : X ∈ vOffs) {m : Word → Word} (hm : ∀ a, a ≠ b + BitVec.ofNat 64 (ownOff + X) → m a = u.memory a) :
    VAt b ci L e { u with memory := m } := by
  have hmem : ∀ a, a ∉ vWords b → m a = e.memory a := fun a ha => by
    have hne : a ≠ b + BitVec.ofNat 64 (ownOff + X) := fun heq => ha (by
      rw [heq]; simp only [vWords, List.mem_map]; exact ⟨X, hX, rfl⟩)
    rw [hm a hne]; exact h.memory a ha
  exact { h with memory := hmem }

theorem vOffs_addr {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ} (he : VEntry b ci K L e)
    (h : VAt b ci L e u) {X : Nat} (hX : X ∈ vOffs) : u.memaddrs (b + BitVec.ofNat 64 (ownOff + X)) = true := by
  obtain ⟨T, hT⟩ := SessionAppend.lay
  obtain ⟨h1, h2⟩ := vOffs_facts X hX
  have := hT.above
  have := SessionAppend.nums.own64
  rw [h.memaddrs]
  exact SessionAppend.own_addr he.hcov h1 (by omega) (by rw [hT.eq]; omega)

theorem vset_lower {X : Nat} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) :
    Lower.lowerStmt1 (vset X e) = some (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + X)))) E) := by
  have h0 : ownOff + X ≠ 0 := by have := SessionAppend.nums.own64; omega
  simp [vset, Lower.lowerStmt1, SessionAppend.at_lower h0, he]

/-- **An own word written** with `e`'s value. -/
theorem vset_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) {X : Nat} (hX : X ∈ vOffs) {x : Syntax.PExpr} {E : PancakeExp}
    (hx : Lower.lowerExp x = some E) {P : Assn σ} (hP : ∀ u, P u → VAt b ci L e u ∧ ∃ v, eval u E = some v)
    {P' : Assn σ} (hcl : Safe.ClockFree P')
    (hP' : ∀ u m, P u → (∀ a, a ≠ b + BitVec.ofNat 64 (ownOff + X) → m a = u.memory a) →
      P' { u with memory := m }) : Frag o [vset X x] P P' :=
  frag_one (vset_lower hx) rfl rfl hcl (Safe.store fun u hu => by
    obtain ⟨h, v, hv⟩ := hP u hu
    refine ⟨b + BitVec.ofNat 64 (ownOff + X), v,
      fun k => if k = b + BitVec.ofNat 64 (ownOff + X) then v else u.memory k,
      by simp only [eval, h.base, he.base], hv, ?_, hP' u _ hu fun a ha => ?_⟩
    · simp only [memStoreWord, vOffs_addr he h hX, if_true]
    · simp only [if_neg ha])

/-- **The message-id check of a word** within `viewClassify`. -/
theorem vmid_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {sn ln : String}
    (hsn : sn ∉ SessionCheck.midNames) (hln : ln ∉ SessionCheck.midNames)
    {S : Word} {w : List Byte} {P : Assn σ}
    (hP : ∀ u, P u → VAt b ci L e u ∧ WordAt sn ln (SessionFrame.blockAt b ci) S w u) :
    Frag o (Session.messageIdCheckAt (Syntax.v sn) (Syntax.v ln)) P
      (fun u => ∃ u0, P u0 ∧ SessionCheck.MidPost w u0 u ∧ Safe.Keeps u0 u) := by
  have hc := SessionCheck.messageIdCheck_lower (σ := Unit) (s := Syntax.v sn) (l := Syntax.v ln) rfl rfl []
    (bareState ())
  refine frag_pinned o (by simp [Session.messageIdCheckAt])
    (by simp [Session.messageIdCheckAt, Syntax.PStmt.isDec]) hc rfl
    (fun _ _ _ h => ⟨⟨{ h.1.1 with }, h.1.2⟩, h.2⟩) fun s hp => ?_
  obtain ⟨hv, hw⟩ := hP s hp
  obtain ⟨c', hc', hsafe⟩ := SessionCheck.messageIdCheck_safe o (s := Syntax.v sn) (l := Syntax.v ln) rfl rfl
    hsn hln (SessionFrame.blockAt b ci) S w s
  rw [hc] at hc'; cases hc'
  exact Safe.safe_keeps (Safe.conseq hsafe
    (fun u (hu : u = s) => ⟨hu, hu ▸ ⟨hw.start, hw.len, hw.blk, hw.bytes, hw.short, hv.ok, hv.jq⟩⟩) fun _ h => h)

/-- **The range check of a word** within `viewClassify`. -/
theorem vrng_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {sn ln : String}
    (hsn : sn ∉ SessionCheck.rngNames) (hln : ln ∉ SessionCheck.rngNames)
    {S : Word} {w : List Byte} {P : Assn σ}
    (hP : ∀ u, P u → VAt b ci L e u ∧ WordAt sn ln (SessionFrame.blockAt b ci) S w u) :
    Frag o (Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln)) P
      (fun u => ∃ u0, P u0 ∧ SessionCheck.RngPost w u0 u ∧
        ∀ y ∈ vBound, (u0.locals y).isSome → (u.locals y).isSome) := by
  let body := (Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln)).drop 2
  have hsplit : Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln) =
      .dec "dn" (Syntax.n 0) :: .dec "dp" (Syntax.n 0) :: body := rfl
  have hB : Lower.lowerStmtsFold body = some _ := rfl
  have hfold : Lower.lowerStmtsFold (Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln)) =
      some (.dec "dn" (.const (BitVec.ofNat 64 0)) (.dec "dp" (.const (BitVec.ofNat 64 0)) _)) := rfl
  rw [hsplit]
  refine frag_dec2 o rfl rfl (by simp [body, Session.rangeCheckAt]) (by simp [body, Session.rangeCheckAt,
    Syntax.PStmt.isDec]) hB (fun u y w hy ⟨u0, h0, hr, hk⟩ => ⟨u0, h0, ?_, fun z hz hb => ?_⟩) fun R s hp => ?_
  · exact SessionCheck.rngPost_restore hr hy w
  · have : z ≠ y := by
      rintro rfl; simp only [vBound] at hz; simp at hy; rcases hy with rfl | rfl <;> simp at hz
    simp only [restore, resVar, if_neg this]; exact hk z hz hb
  obtain ⟨hv, hw⟩ := hP s hp
  obtain ⟨c', hc', hsafe⟩ := SessionCheck.rangeCheck_safe o (s := Syntax.v sn) (l := Syntax.v ln) rfl rfl
    hsn hln (SessionFrame.blockAt b ci) S w s
  rw [hfold] at hc'; cases hc'
  have hk := Safe.safe_keeps (Safe.conseq hsafe (fun u (hu : u = s) => ⟨hu, hu ▸ ⟨hw.start, hw.len, hw.blk, hw.bytes,
    hw.short, hv.ok, hv.val, hv.jq, hv.lo, hv.hi⟩⟩) fun _ h => h)
  exact WpRet.conseq (WpRet.ofSafe R rfl hk) (fun u (hu : u = s) => hu) (fun _ _ h => h)
    (fun u h => ⟨s, hp, h.1, fun y _ hy => h.2 y hy⟩) s rfl

theorem vat_restore {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : VAt b ci L e u) {y : String}
    (hy : y ∈ vNames ∧ y ∉ vFixed ∧ y ∉ vBound) (v : Option Value) : VAt b ci L e (restore u y v) :=
  vat_but (xs := [y]) h ⟨fun x hx => by
      have : x ≠ y := fun e => hx (by simp [e])
      simp only [restore, resVar, if_neg this], rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun x hx => by simp at hx; subst hx; exact ⟨hy.1, hy.2.1⟩) fun x hx hb => by
      have : x ≠ y := fun e => hy.2.2 (e ▸ hx)
      simp only [restore, resVar, if_neg this]; exact hb

/-- What `vpick` leaves in `sel`: one for a message-id where `p` asks for one, two for a range, else zero. -/
def selOf (p : Bool) (a : List Byte) : Nat :=
  if p && CommandSpec.isMessageId a then 1 else if (CommandSpec.range? a).isSome then 2 else 0

/-- **A message-id or a range**: if it goes on, which one it is in `sel`. -/
theorem vpick_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) {sn ln : String} (hsn : sn ∉ SessionCheck.rngNames ∧ sn ∉ SessionCheck.midNames)
    (hln : ln ∉ SessionCheck.rngNames ∧ ln ∉ SessionCheck.midNames) {S : Word} {w : List Byte}
    (hW : ∀ u, VAt b ci L e u → WordAt sn ln (SessionFrame.blockAt b ci) S w u)
    {ids : Syntax.PExpr} {IDS : PancakeExp} (hids : Lower.lowerExp ids = some IDS) {p : Bool}
    (hI : ∀ u, VAt b ci L e u → eval u IDS = some (bw p)) :
    Frag o (vpick (Syntax.v sn) (Syntax.v ln) ids) (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0)
      (fun u => VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))) := by
  let M1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "ok" = some 0
  have f1 : Frag o [.assign "ok" (Syntax.n 0)] (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0) M1 :=
    frag_one (a := .assign "ok" (.const (BitVec.ofNat 64 0))) rfl rfl rfl
      (vat_and fun _ _ h => h) (Safe.assign fun u ⟨h, hs⟩ => by
        obtain ⟨v, hv⟩ := h.ok
        exact ⟨0, v, rfl, hv, vat_set h (by decide) 0, by simp [setLocal, hs], by simp [setLocal]⟩)
  let M2 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧
    u.locals "ok" = some (bw (p && CommandSpec.isMessageId w))
  have f2 : Frag o [SessionStore.ifs ids (Session.messageIdCheckAt (Syntax.v sn) (Syntax.v ln))] M1 M2 := by
    refine frag_ite o hids (vat_and fun _ _ h => h) (fun s h => ⟨_, hI s h.1⟩) ?_
      (fun _ _ _ _ h => by simp [declared, Session.messageIdCheckAt] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, h.2.1, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_conseq (vmid_frag o hsn.2 hln.2 (S := S) (w := w)
        (P := fun s => M1 s ∧ eval s IDS ≠ some 0) fun u h => ⟨h.1.1, hW u h.1.1⟩) (fun _ h => h)
        fun u ⟨u0, ⟨h0, hc⟩, hm, hk⟩ => ⟨vat_but h0.1 hm.1 (by decide) (fun y _ hy => hk y hy), ?_, ?_⟩
      · rw [hm.1.locals "sel" (by decide)]; exact h0.2.1
      · have hp : p = true := by rw [hI u0 h0.1] at hc; exact SessionCheck.bw_ne0 hc
        rw [hm.2, hp]; rfl
    · rw [hI s h.1] at hc
      rw [h.2.2, SessionCheck.bw_eq0 hc]; rfl
  -- a message-id kept, or a range checked and kept
  let Q : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))
  have hQ : Safe.ClockFree Q := vat_and fun _ _ h => h
  have hQr : ∀ u y v, Q u → y ∈ ["dn", "dp"] → Q (restore u y v) := fun u y v h hy => by
    simp at hy
    have hne : y ≠ "sel" := by rcases hy with rfl | rfl <;> decide
    refine ⟨vat_restore h.1 (by rcases hy with rfl | rfl <;> decide) v, ?_⟩
    simp only [restore, resVar, if_neg (Ne.symm hne)]; exact h.2
  have sq : ∀ {P : Assn σ} (X : Nat) (hX : X ∈ vOffs) (x : String) {V : Nat}, (∀ u, P u → VAt b ci L e u ∧
      (∃ v, u.locals x = some v) ∧ u.locals "sel" = some (BitVec.ofNat 64 V)) →
      Frag o [vset X (Syntax.v x)] P (fun u => VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 V)) :=
    fun {P} X hX x {V} hP => vset_frag o he hX (x := Syntax.v x) (E := .var x) rfl
      (fun u h => ⟨(hP u h).1, (hP u h).2.1⟩)
      (vat_and fun _ _ h => h) fun u m h hm => ⟨vat_store (hP u h).1 hX hm, (hP u h).2.2⟩
  refine frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 ?_)
  refine frag_ite o (C := .var "ok") rfl hQ (fun s h => ⟨_, h.2.2⟩) ?_ (fun _ _ _ _ h => by simp [declared, vset] at h)
    ?_ (fun u y v h hy => hQr u y v h (by
      rw [declared_append, show declared (Session.rangeCheckAt (Syntax.v sn) (Syntax.v ln)) = ["dn", "dp"] from rfl]
        at hy
      simpa [declared, SessionStore.ifs] using hy))
  · -- a message-id where one is asked for
    refine frag_pure ((p && CommandSpec.isMessageId w) = true) (fun s ⟨h, hc⟩ => by
      simp only [eval, h.2.2] at hc; exact SessionCheck.bw_ne0 hc) (lowK_any _ (k := .skip) (c := _) rfl) fun hpm => ?_
    have e1 : selOf p w = 1 := by simp [selOf, hpm]
    refine frag_append (xs := [_]) (frag_one (a := .assign "sel" (.const (BitVec.ofNat 64 1))) rfl rfl rfl
      (P' := fun u => VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))) hQ
      (Safe.assign fun u h => ?_))
      (frag_append (xs := [_]) (sq ownVs (by decide) sn fun u h => ⟨h.1, ⟨_, (hW u h.1).start⟩, h.2⟩)
        (sq ownVl (by decide) ln fun u h => ⟨h.1, ⟨_, (hW u h.1).len⟩, h.2⟩))
    obtain ⟨v, hv⟩ := h.1.1.sel
    exact ⟨_, v, rfl, hv, vat_set h.1.1 (by decide) _, by simp [setLocal, e1]⟩
  have hpm0 : ∀ s, M2 s ∧ eval s (.var "ok") = some 0 → (p && CommandSpec.isMessageId w) = false :=
    fun s ⟨h, hc⟩ => by simp only [eval, h.2.2] at hc; exact SessionCheck.bw_eq0 hc
  refine frag_pure ((p && CommandSpec.isMessageId w) = false) hpm0 (lowK_any _ (k := .skip) (c := _) rfl)
    fun hpm => ?_
  have fr := vrng_frag o hsn.1 hln.1 (S := S) (w := w) (P := fun s => M2 s ∧ eval s (.var "ok") = some 0)
    fun u h => ⟨h.1.1, hW u h.1.1⟩
  let M3 : Assn σ := fun u => ∃ u0, (M2 u0 ∧ eval u0 (.var "ok") = some 0) ∧ SessionCheck.RngPost w u0 u ∧
    ∀ y ∈ vBound, (u0.locals y).isSome → (u.locals y).isSome
  have m3 : ∀ u, M3 u → VAt b ci L e u ∧ u.locals "sel" = some 0 ∧
      u.locals "ok" = some (bw (CommandSpec.range? w).isSome) ∧ ∀ lo hi, CommandSpec.range? w = some (lo, hi) →
        u.locals "lo" = some (BitVec.ofNat 64 lo) ∧ u.locals "hi" = some (BitVec.ofNat 64 hi) :=
    fun u ⟨u0, ⟨h0, _⟩, hr, hk⟩ => ⟨vat_but h0.1 hr.1 (by decide) hk,
      by rw [hr.1.locals "sel" (by decide)]; exact h0.2.1, hr.2.1, hr.2.2⟩
  refine frag_append fr (frag_ite o (C := .var "ok") rfl hQ (fun s h => ⟨_, (m3 s h).2.2.1⟩) ?_
    (fun _ _ _ _ h => by simp [declared, vset] at h) (frag_nil o fun s ⟨h, hc⟩ => ?_)
    (fun _ _ _ _ h => by simp [declared] at h))
  · refine frag_pure ((CommandSpec.range? w).isSome = true) (fun s ⟨h, hc⟩ => by
      simp only [eval, (m3 s h).2.2.1] at hc; exact SessionCheck.bw_ne0 hc) (lowK_any _ (k := .skip) (c := _) rfl)
      fun hrs => ?_
    have e2 : selOf p w = 2 := by simp [selOf, hpm, hrs]
    obtain ⟨⟨lo, hi⟩, hlh⟩ := Option.isSome_iff_exists.mp hrs
    refine frag_append (xs := [_]) (frag_one (a := .assign "sel" (.const (BitVec.ofNat 64 2))) rfl rfl rfl
      (P' := fun u => (VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))) ∧
        u.locals "lo" = some (BitVec.ofNat 64 lo) ∧ u.locals "hi" = some (BitVec.ofNat 64 hi))
      (fun u k h => ⟨hQ u k h.1, h.2⟩) (Safe.assign fun u h => ?_))
      (frag_append (xs := [_]) (vset_frag o he (X := ownLo) (by decide) (x := Syntax.v "lo") (E := .var "lo") rfl
        (P' := fun u => (VAt b ci L e u ∧ u.locals "sel" = some (BitVec.ofNat 64 (selOf p w))) ∧
          u.locals "hi" = some (BitVec.ofNat 64 hi)) (fun u h => ⟨h.1.1, _, h.2.1⟩)
        (fun u k h => ⟨hQ u k h.1, h.2⟩) fun u m h hm => ⟨⟨vat_store h.1.1 (by decide) hm, h.1.2⟩, h.2.2⟩)
        (sq ownHi (by decide) "hi" fun u h => ⟨h.1.1, ⟨_, h.2⟩, h.1.2⟩))
    obtain ⟨v, hv⟩ := (m3 u h.1).1.sel
    obtain ⟨hlo, hhi⟩ := (m3 u h.1).2.2.2 lo hi hlh
    exact ⟨_, v, rfl, hv, ⟨vat_set (m3 u h.1).1 (by decide) _, by simp [setLocal, e2]⟩,
      by simp [setLocal, hlo], by simp [setLocal, hhi]⟩
  · have hrs : (CommandSpec.range? w).isSome = false := by
      simp only [eval, (m3 s h).2.2.1] at hc; exact SessionCheck.bw_eq0 hc
    have e0 : selOf p w = 0 := by simp [selOf, hpm, hrs]
    exact ⟨(m3 s h).1, by rw [e0]; exact (m3 s h).2.1⟩

/-! ### OVER and XOVER -/

/-- `viewClassify` before its last words: every word but `vWords` as at `e`, `r` holding `R`. -/
def VEnd (b : Word) (e : PancakeState σ) (R : Nat) (u : PancakeState σ) : Prop :=
  (∀ a, a ∉ vWords b → u.memory a = e.memory a) ∧ u.locals "r" = some (BitVec.ofNat 64 R) ∧
    (∃ v, u.locals "sel" = some v) ∧ u.memaddrs = e.memaddrs ∧ u.baseAddr = e.baseAddr ∧ u.be = e.be ∧ u.code = e.code

theorem vend_clock (b : Word) (e : PancakeState σ) (R : Nat) : Safe.ClockFree (VEnd b e R) := fun _ _ h => h

theorem vend_restore {b : Word} {e u : PancakeState σ} {R : Nat} (h : VEnd b e R u) {y : String}
    (hy : y ≠ "r" ∧ y ≠ "sel") (v : Option Value) : VEnd b e R (restore u y v) := by
  obtain ⟨h1, h2, ⟨s, h3⟩, h4⟩ := h
  exact ⟨h1, by simp only [restore, resVar, if_neg (Ne.symm hy.1)]; exact h2,
    ⟨s, by simp only [restore, resVar, if_neg (Ne.symm hy.2)]; exact h3⟩, h4⟩

theorem vend_of {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : VAt b ci L e u) :
    VEnd b e (Session.replyCode .syntax) u :=
  ⟨h.memory, h.r, h.sel, h.memaddrs, h.base, h.be, h.code⟩

/-- The reply `X` set at the end. -/
theorem vsay_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} (X : CommandSpec.Reply)
    {R : Nat} {P : Assn σ} (hP : ∀ u, P u → VAt b ci L e u ∧ Session.replyCode X = R) :
    Frag o [vsay X] P (VEnd b e R) :=
  frag_one (a := .assign "r" (.const (BitVec.ofNat 64 (Session.replyCode X)))) rfl rfl rfl (vend_clock b e R)
    (Safe.assign fun u hu => by
      obtain ⟨h, hX⟩ := hP u hu
      refine ⟨_, _, rfl, h.r, ?_⟩
      obtain ⟨s, hs⟩ := h.sel
      exact ⟨h.memory, by simp [setLocal, hX], ⟨s, by simp [setLocal, hs]⟩, h.memaddrs, h.base, h.be, h.code⟩)

theorem vargs_eval {b : Word} {ci : Nat} {L : List Byte} {e u : PancakeState σ} (h : VAt b ci L e u)
    (hsh : L.length < 2 ^ 62) (k : Nat) (hk : k < 2 ^ 63) :
    eval u (.cmp .equal (.var "args") (.const (BitVec.ofNat 64 k))) =
      some (bw (decide ((spans L).length - 1 = k))) := by
  have := spans_length L
  exact SessionCheck.eval_eq (by omega) (by omega) (by simp only [eval]; exact h.args) rfl

theorem vcmd {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ} (he : VEntry b ci K L e)
    (h : VAt b ci L e u) : u.locals "cmd" = some (BitVec.ofNat 64 K) := by
  rw [h.loc "cmd" (by decide)]; exact he.cmd

theorem ne0_eval {u : PancakeState σ} {x : String} {n : Nat} (hn : n < 2 ^ 63)
    (h : u.locals x = some (BitVec.ofNat 64 n)) :
    eval u (.cmp .equal (.cmp .equal (.var x) (.const (BitVec.ofNat 64 0))) (.const (BitVec.ofNat 64 0))) =
      some (bw (decide (n ≠ 0))) := by
  have e1 := SessionCheck.eval_eq (t := u) (a := .var x) (b := .const (BitVec.ofNat 64 0)) (x := n) (y := 0)
    (by omega) (by decide) (by simp only [eval]; exact h) rfl
  simp only [eval] at e1 ⊢
  rw [e1]
  by_cases e : n = 0 <;> simp [e, bw]

theorem ans_over {c : CommandSpec.Cmd} (hc : c = .over ∨ c = .xover) (args : List (List Byte)) :
    (args.length = 0 → Session.replyCode (CommandSpec.answerIn c args) = 41) ∧
    (args.length = 1 → Session.replyCode (CommandSpec.answerIn c args) =
      if selOf (decide (c = .over)) (args.getD 0 []) ≠ 0 then 41 else 7) ∧
    (2 ≤ args.length → Session.replyCode (CommandSpec.answerIn c args) = 7) := by
  rcases hc with rfl | rfl <;> rcases args with _ | ⟨a, _ | ⟨a2, rest⟩⟩ <;>
    simp [CommandSpec.answerIn, CommandSpec.answer, Session.replyCode] <;>
    (cases hm : CommandSpec.isMessageId a <;> cases hr : CommandSpec.range? a <;>
      simp [selOf, hm, hr])

/-- The word of `viewClassify`'s line at place `j`, in `s{j}` and `l{j}`, for `j` 1 or 2. -/
theorem vword1 {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ} (he : VEntry b ci K L e)
    (h : VAt b ci L e u) (h2 : 2 ≤ (spans L).length) :
    WordAt "s1" "l1" (SessionFrame.blockAt b ci) (BitVec.ofNat 64 ((spans L).getD 1 (0, 0)).1)
      (cut L ((spans L).getD 1 (0, 0))) u :=
  wordAt_of (vat_line he h) (spans_getD_mem (by omega)) h.s1 h.l1

theorem vword2 {b : Word} {ci K : Nat} {L : List Byte} {e u : PancakeState σ} (he : VEntry b ci K L e)
    (h : VAt b ci L e u) (h3 : 3 ≤ (spans L).length) :
    WordAt "s2" "l2" (SessionFrame.blockAt b ci) (BitVec.ofNat 64 ((spans L).getD 2 (0, 0)).1)
      (cut L ((spans L).getD 2 (0, 0))) u :=
  wordAt_of (vat_line he h) (spans_getD_mem (by omega)) h.s2 h.l2

theorem selOf_lt (p : Bool) (a : List Byte) : selOf p a < 3 := by unfold selOf; split <;> (try split) <;> omega

/-- **OVER's and XOVER's branch**: if it goes on, the code of the reply `answerIn` gives. -/
theorem over_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {c : CommandSpec.Cmd}
    (hc : c = .over ∨ c = .xover) (he : VEntry b ci (cmdCode (some c)) L e) :
    Frag o overTree (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0)
      (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
  have hsh : L.length < 2 ^ 62 := by have := he.short; simp [News.SessionSpec.lineLimit] at this; omega
  let A := (spans L).length - 1
  have hlen : (argsOf L).length = A := by simp [argsOf, A]
  let a := cut L ((spans L).getD 1 (0, 0))
  have ha : (argsOf L).getD 0 [] = a := argsOf_head L
  obtain ⟨r0, r1, r2⟩ := ans_over hc (argsOf L)
  rw [hlen] at r0 r1 r2; rw [ha] at r1
  let p := decide (c = .over)
  have hp : ∀ u, VAt b ci L e u → eval u (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 17))) = some (bw p) :=
    fun u h => by
      rw [SessionCheck.eval_eq (x := cmdCode (some c)) (y := 17) (by have := cmdCode_lt (some c); omega) (by decide)
        (by simp only [eval]; exact vcmd he h) rfl]
      rcases hc with rfl | rfl <;> rfl
  -- no argument
  let G0 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧
    u.locals "good" = some (bw (decide (A = 0)))
  have f1 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 0)) [.assign "good" (Syntax.n 1)]]
      (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0) G0 := by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 0))) rfl
      (vat_and fun _ _ h => h) (fun s h => ⟨_, vargs_eval h.1 hsh 0 (by decide)⟩) ?_
      (fun _ _ _ _ h => by simp [declared] at h) (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, h.2.1, ?_⟩)
      (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_one (a := .assign "good" (.const (BitVec.ofNat 64 1))) rfl rfl rfl
        (vat_and fun _ _ h => h) (Safe.assign fun u ⟨h, hc⟩ => ?_)
      rw [vargs_eval h.1 hsh 0 (by decide)] at hc
      have e0 := of_decide_eq_true (SessionCheck.bw_ne0 hc)
      exact ⟨_, _, rfl, h.2.2, vat_set h.1 (by decide) _, by simp [setLocal, h.2.1],
        by simp [setLocal, e0, A]; rfl⟩
    · rw [vargs_eval h.1 hsh 0 (by decide)] at hc
      rw [h.2.2, SessionCheck.bw_eq0 hc]; rfl
  -- one argument: a message-id where OVER asks for one, or a range
  let gv := decide (A = 0) || (decide (A = 1) && decide (selOf p a ≠ 0))
  let G1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "good" = some (bw gv)
  have f2 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 1))
      (vpick (Syntax.v "s1") (Syntax.v "l1") (Syntax.eEq (Syntax.v "cmd") (Syntax.n 17)) ++
        [.assign "good" (SessionStore.ne (Syntax.v "sel") (Syntax.n 0))])] G0 G1 := by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) rfl
      (vat_and fun _ _ h => h) (fun s h => ⟨_, vargs_eval h.1 hsh 1 (by decide)⟩) ?_
      (fun _ _ _ _ h => by simp [declared, vpick, SessionStore.ifs] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_pure (A = 1) (fun s ⟨h, hc⟩ => by
        rw [vargs_eval h.1 hsh 1 (by decide)] at hc; exact of_decide_eq_true (SessionCheck.bw_ne0 hc))
        (lowK_any _ (k := .skip) (c := _) rfl) fun hA1 => ?_
      refine frag_append (frag_conseq (vpick_frag o he (sn := "s1") (ln := "l1") (by decide) (by decide)
        (fun u h => vword1 he h (by omega)) rfl hp) (fun s ⟨h, _⟩ => ⟨h.1, h.2.1⟩) fun _ h => h)
        (frag_one (a := .assign "good" (.cmp .equal (.cmp .equal (.var "sel") (.const (BitVec.ofNat 64 0)))
          (.const (BitVec.ofNat 64 0)))) rfl rfl rfl (vat_and fun _ _ h => h)
          (Safe.assign fun u h => ?_))
      obtain ⟨v, hv⟩ := h.1.good
      refine ⟨_, v, ne0_eval (by have := selOf_lt p (cut L ((spans L).getD 1 (0, 0))); omega) h.2, hv,
        vat_set h.1 (by decide) _, ?_⟩
      simp only [setLocal, if_pos, gv, hA1, a]
      simp
    · rw [vargs_eval h.1 hsh 1 (by decide)] at hc
      have h1 : ¬A = 1 := of_decide_eq_false (SessionCheck.bw_eq0 hc)
      rw [h.2.2]; show _ = some (bw (decide (A = 0) || (decide (A = 1) && _)))
      rw [show decide (A = 1) = false from decide_eq_false h1]; simp
  have f3 : Frag o [SessionStore.ifs (Syntax.v "good") [vsay (.over false .current)]] G1
      (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
    refine frag_ite o (C := .var "good") rfl (vend_clock _ _ _) (fun s h => ⟨_, h.2⟩)
      (vsay_frag o _ fun u ⟨h, hc⟩ => ⟨h.1, ?_⟩) (fun _ _ _ _ h => by simp [declared, vsay] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · simp only [eval, h.2] at hc
      have := SessionCheck.bw_ne0 hc
      simp only [gv, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with e0 | ⟨e1, e2⟩
      · rw [r0 e0]; rfl
      · rw [r1 e1, if_pos e2]; rfl
    · simp only [eval, h.2] at hc
      have := SessionCheck.bw_eq0 hc
      simp only [gv, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
      have hR : Session.replyCode (CommandSpec.answerIn c (argsOf L)) = Session.replyCode .syntax := by
        rcases this with ⟨n0, n1 | n2⟩
        · rw [r2 (by omega)]; rfl
        · have : A = 1 ∨ 2 ≤ A := by omega
          rcases this with e1 | e2
          · rw [r1 e1, if_neg (by simpa using n2)]; rfl
          · rw [r2 e2]; rfl
      rw [hR]; exact vend_of h.1
  exact frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 f3)

/-! ### HDR and XHDR -/

/-- HDR's field check after `i` octets, `m` one when the field starts with a colon. -/
def fieldOk (f : List Byte) (m i : Nat) : Bool :=
  decide (1 + m ≤ f.length) && ((f.drop m).take (i - m)).all CommandSpec.isNotColon

/-- Whether a field starts with a colon, as `meta` holds it. -/
def metaOf (f : List Byte) : Nat := if f.getD 0 0 = 58#8 then 1 else 0

theorem fieldOk_full (f : List Byte) : fieldOk f (metaOf f) f.length = CommandSpec.isFieldName f := by
  cases f with
  | nil => simp [fieldOk, metaOf, CommandSpec.isFieldName]
  | cons b rest =>
    by_cases h : b = 58#8
    · subst h
      simp only [fieldOk, metaOf, List.getD_cons_zero, if_true, CommandSpec.isFieldName, List.length_cons]
      simp
      cases rest <;> simp
    · simp only [fieldOk, metaOf, List.getD_cons_zero, if_neg h, CommandSpec.isFieldName, List.length_cons]
      simp [h]

theorem fieldOk_step {f : List Byte} {m i : Nat} (hm : m ≤ i) (hi : i < f.length) :
    fieldOk f m (i + 1) = (fieldOk f m i && CommandSpec.isNotColon f[i]) := by
  simp only [fieldOk]
  rw [show i + 1 - m = (i - m) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show m + (i - m) = i by omega, List.getElem?_eq_getElem hi]
  simp [Bool.and_assoc]

theorem fieldOk_mono {f : List Byte} {m i j : Nat} (hij : i ≤ j) (h : fieldOk f m j = true) :
    fieldOk f m i = true := by
  simp only [fieldOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun x hx => h.2 x (List.take_subset_take_left _ (by omega) hx)⟩

theorem notColon_lower {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) :
    Lower.lowerExp (SessionStore.or2 (Session.between 33 57 e) (Session.between 59 126 e)) =
      some (SessionCheck.or2E (SessionCheck.betweenE (BitVec.ofNat 64 33) (BitVec.ofNat 64 57) E)
        (SessionCheck.betweenE (BitVec.ofNat 64 59) (BitVec.ofNat 64 126) E)) := by
  simp [SessionStore.or2, Session.between, SessionCheck.or2E, SessionCheck.betweenE, SessionCheck.leE, Syntax.eAnd,
    Syntax.eLe, Syntax.eLt, Syntax.eAdd, Syntax.n, Lower.lowerExp, he]

theorem notColon_eval {s : PancakeState σ} {E : PancakeExp} {y : Byte} (h : eval s E = some (y.setWidth 64)) :
    eval s (SessionCheck.or2E (SessionCheck.betweenE (BitVec.ofNat 64 33) (BitVec.ofNat 64 57) E)
      (SessionCheck.betweenE (BitVec.ofNat 64 59) (BitVec.ofNat 64 126) E)) =
      some (bw (CommandSpec.isNotColon y)) := by
  have hy := y.isLt
  rw [setWidth8_64] at h
  rw [SessionCheck.eval_or2 (SessionCheck.eval_between (by omega) (by decide) (by decide) h rfl rfl)
    (SessionCheck.eval_between (by omega) (by decide) (by decide) h rfl rfl)]
  simp [CommandSpec.isNotColon]

theorem metaOf_eq {f : List Byte} (h : 0 < f.length) :
    bw (decide (f[0].toNat = 58)) = BitVec.ofNat 64 (metaOf f) := by
  simp only [metaOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  by_cases e : f[0] = 58#8
  · simp [e, bw]
  · have : f[0].toNat ≠ 58 := fun h' => e (BitVec.eq_of_toNat_eq (by simp [h']))
    simp [e, this, bw]

theorem metaOf_le (f : List Byte) : metaOf f ≤ 1 := by unfold metaOf; split <;> omega

/-- **HDR's field name check is `CommandSpec.isFieldName`**, of the second word, if it goes on. -/
theorem fcheck_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h2 : 2 ≤ (spans L).length) :
    Frag o (fieldTree.take 5) (VAt b ci L e) (fun u => VAt b ci L e u ∧
      u.locals "meta" = some (BitVec.ofNat 64 (metaOf (cut L ((spans L).getD 1 (0, 0))))) ∧
      u.locals "ok" = some (bw (CommandSpec.isFieldName (cut L ((spans L).getD 1 (0, 0)))))) := by
  let p := (spans L).getD 1 (0, 0)
  let f := cut L p
  have hpm : p ∈ spans L := by
    exact spans_getD_mem (by omega)
  have hf1 : 0 < f.length := by rw [cut_length (spans_bound L p hpm)]; have := spans_pos L p hpm; omega
  have hsh : L.length < 2 ^ 62 := by have := he.short; simp [News.SessionSpec.lineLimit] at this; omega
  have hfl : f.length < 2 ^ 62 := by
    have e1 : f.length = p.2 := cut_length (spans_bound L p hpm)
    have := spans_bound L p hpm; omega
  let m := metaOf f
  have hm1 := metaOf_le f
  let F1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "f0" = some (f[0].setWidth 64)
  have g1 : Frag o [.dec "f0" (Session.kept (Syntax.v "s1"))] (VAt b ci L e) F1 :=
    frag_dec o (E := .loadByte (.op .add (.op .add (.var "blk") (.const (BitVec.ofNat 64 framerHead))) (.var "s1")))
      (by simp [Session.kept, Syntax.eAdd, Syntax.v, Syntax.n, Lower.lowerExp]) fun u h => by
      have hw := vword1 he h h2
      have hb := hw.bytes 0 hf1
      rw [show (BitVec.ofNat 64 p.1) + BitVec.ofNat 64 0 = BitVec.ofNat 64 p.1 by simp] at hb
      refine ⟨f[0].setWidth 64, ?_, vat_set h (by decide) _, by simp [setLocal]⟩
      simp only [eval, h.blk, h.s1, show framerHead = 40 from rfl]
      rw [hb]
  let F2 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m)
  have g2 : Frag o [.dec "meta" (Syntax.eEq (Syntax.v "f0") (Syntax.n 58))] F1 F2 :=
    frag_dec o (E := .cmp .equal (.var "f0") (.const (BitVec.ofNat 64 58))) rfl fun u h => by
      have hy := (f[0]).isLt
      refine ⟨_, SessionCheck.eval_eq (x := f[0].toNat) (y := 58) (by omega) (by decide)
        (by simp only [eval, h.2, setWidth8_64]) rfl, vat_set h.1 (by decide) _, ?_⟩
      simp [setLocal, metaOf_eq hf1, m]
  let I (i : Nat) (u : PancakeState σ) : Prop := VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m) ∧
    u.locals "jq" = some (BitVec.ofNat 64 i) ∧ m ≤ i ∧ i ≤ f.length ∧ u.locals "ok" = some (bw (fieldOk f m i))
  have Iclock : ∀ i, Safe.ClockFree (I i) := fun _ => vat_and fun _ _ h => h
  have g3 : Frag o [.assign "ok" (Syntax.eLe (Syntax.eAdd (Syntax.n 1) (Syntax.v "meta")) (Syntax.v "l1")),
      .assign "jq" (Syntax.v "meta")] F2 (I m) := by
    refine frag_append (xs := [_]) (frag_one (a := .assign "ok" (SessionCheck.leE (.op .add (.const 1)
      (.var "meta")) (.var "l1"))) rfl rfl rfl (P' := fun u => F2 u ∧ u.locals "ok" = some (bw (fieldOk f m m)))
      (fun u k h => ⟨⟨vat_clock b ci L e u k h.1.1, h.1.2⟩, h.2⟩) (Safe.assign fun u h => ?_))
      (frag_one (a := .assign "jq" (.var "meta")) rfl rfl rfl (Iclock m) (Safe.assign fun u h => ?_))
    · obtain ⟨v, hv⟩ := h.1.ok
      have hl : u.locals "l1" = some (BitVec.ofNat 64 f.length) := by
        rw [h.1.l1, cut_length (spans_bound L p hpm)]
      refine ⟨_, v, SessionCheck.eval_le (x := 1 + m) (y := f.length) (by omega) (by omega)
        (by simp only [eval, h.2]; rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add])
        (by simp only [eval]; exact hl), hv, ⟨vat_set h.1 (by decide) _, by simp [setLocal, h.2]⟩, ?_⟩
      simp [setLocal, fieldOk]
    · obtain ⟨v, hv⟩ := h.1.1.jq
      exact ⟨_, v, by simp only [eval]; exact h.1.2, hv, vat_set h.1.1 (by decide) _, by simp [setLocal, h.1.2],
        by simp [setLocal], Nat.le_refl _, by omega, by simp [setLocal, h.2]⟩
  let body : List Syntax.PStmt := [.dec "cz" (Session.kept (Syntax.eAdd (Syntax.v "s1") (Syntax.v "jq"))),
    .assign "ok" (SessionStore.or2 (Session.between 33 57 (Syntax.v "cz")) (Session.between 59 126 (Syntax.v "cz"))),
    SessionStore.inc "jq"]
  have hbody : ∀ i, m ≤ i → i < f.length → fieldOk f m i = true → Frag o body (I i) (I (i + 1)) :=
      fun i hmi hi hp => by
    let M1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m) ∧
      u.locals "jq" = some (BitVec.ofNat 64 i) ∧ u.locals "cz" = some (f[i].setWidth 64)
    let M2 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m) ∧
      u.locals "jq" = some (BitVec.ofNat 64 i) ∧ u.locals "ok" = some (bw (CommandSpec.isNotColon f[i]))
    have b1 : Frag o [body[0]] (I i) M1 := frag_dec o (E := SessionCheck.kb (.var "s1") (.var "jq")) rfl fun s h => by
      have hw := vword1 he h.1 h2
      have hA : eval s (.op .add (.var "s1") (.var "jq")) = some (BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) := by
        simp only [eval, h.1.s1, h.2.2.1]; rfl
      refine ⟨_, SessionCheck.kb_eval h.1.blk hA (hw.bytes i hi), vat_set h.1 (by decide) _,
        by simp [setLocal, h.2.1], by simp [setLocal, h.2.2.1], by simp only [setLocal]; rfl⟩
    have b2 : Frag o [body[1]] M1 M2 := frag_one (a := .assign "ok" (SessionCheck.or2E
      (SessionCheck.betweenE (BitVec.ofNat 64 33) (BitVec.ofNat 64 57) (.var "cz"))
      (SessionCheck.betweenE (BitVec.ofNat 64 59) (BitVec.ofNat 64 126) (.var "cz"))))
      (by show Lower.lowerStmt1 (.assign "ok" _) = _
          simp only [Lower.lowerStmt1, notColon_lower (e := Syntax.v "cz") rfl]) rfl rfl
      (vat_and fun _ _ h => h) (Safe.assign fun u h => by
        obtain ⟨v, hv⟩ := h.1.ok
        exact ⟨_, v, notColon_eval (by simp only [eval]; exact h.2.2.2), hv, vat_set h.1 (by decide) _,
          by simp [setLocal, h.2.1], by simp [setLocal, h.2.2.1], by simp [setLocal]⟩)
    have b3 : Frag o [body[2]] M2 (I (i + 1)) :=
      frag_one (a := .assign "jq" (.op .add (.var "jq") (.const 1))) rfl rfl rfl (Iclock (i + 1))
        (Safe.assign fun u h => ⟨BitVec.ofNat 64 (i + 1), _, by simp only [eval, h.2.2.1]; rw [BitVec.ofNat_add]; rfl,
          h.2.2.1, vat_set h.1 (by decide) _, by simp [setLocal, h.2.1], by simp [setLocal],
          by omega, by omega, by simp [setLocal, h.2.2.2, fieldOk_step hmi hi, hp]⟩)
    exact frag_append (xs := [_]) b1 (frag_append (xs := [_]) b2 b3)
  have hlow : LowKK body := lowK_any _ (k := .skip) (c := _) rfl
  let COND : PancakeExp := .op .and_ (.var "ok") (.cmp .less (.var "jq") (.var "l1"))
  have hl1 : ∀ u, VAt b ci L e u → u.locals "l1" = some (BitVec.ofNat 64 f.length) := fun u h => by
    rw [h.l1, cut_length (spans_bound L p hpm)]
  have hcond : ∀ i u, I i u → eval u COND = some (bw (fieldOk f m i && decide (i < f.length))) := fun i u h =>
    SessionCheck.eval_and (by simp only [eval]; exact h.2.2.2.2.2)
      (SessionCheck.eval_lt (by omega) (by omega) (by simp only [eval]; exact h.2.2.1)
        (by simp only [eval]; exact hl1 u h.1))
  have g4 := frag_count o (c := Syntax.eAnd (Syntax.v "ok") (Syntax.eLt (Syntax.v "jq") (Syntax.v "l1"))) (C := COND)
    (by simp [Syntax.eAnd, Syntax.eLt, Syntax.v, Lower.lowerExp, COND]) hlow Iclock
    (fun i u y v h hy => by
      simp [body, declared, SessionStore.inc] at hy; subst hy
      refine ⟨vat_restore h.1 (by decide) v, ?_⟩
      simp only [restore, resVar, if_neg (by decide : ("meta" : String) ≠ "cz"),
        if_neg (by decide : ("jq" : String) ≠ "cz"), if_neg (by decide : ("ok" : String) ≠ "cz")]
      exact h.2) hcond
    (fun i hg => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      exact frag_pure (m ≤ i) (fun _ h => h.2.2.2.1) hlow fun hmi => hbody i hmi hg.2 hg.1) m
  refine frag_conseq (frag_append (xs := [_]) g1 (frag_append (xs := [_]) g2 (frag_append (xs := [_, _]) g3 g4)))
    (fun _ h => h) fun u ⟨i, h, hz⟩ => ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.2.2.2, ← fieldOk_full, count_exit (p := fieldOk f m) (fun _ _ hij h => fieldOk_mono hij h)
    h.2.2.2.2.1 hz]

/-- **A word's comparison with a text** within `viewClassify`, what else the state holds kept. -/
theorem vcmp_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h2 : 2 ≤ (spans L).length) {t : Nat} (ht : t < texts.length)
    {Q : PancakeState σ → Prop} (hQ : ∀ u u', Q u → SessionCheck.ButFor ["eqk", "jq"] u u' → Q u') :
    Frag o (Session.wordIsAt "s1" "l1" t) (fun u => VAt b ci L e u ∧ Q u) (fun u => VAt b ci L e u ∧ Q u ∧
      u.locals "eqk" = some
          (bw (decide ((cut L ((spans L).getD 1 (0, 0))).map CommandSpec.upper = texts.getD t [])))) :=
  frag_conseq (wordIsAt_any o (sn := "s1") (ln := "l1") (by decide) (by decide) ht (b := b)
    (P := fun u => VAt b ci L e u ∧ Q u) fun s h => ⟨vword1 he h.1 h2, h.1.base.trans he.base, vat_texts he h.1,
      h.1.eqk, h.1.jq⟩) (fun _ h => h) fun u ⟨s1, h1, hb, hj, hk⟩ =>
    ⟨vat_but h1.1 hb (by decide) fun y hy hs => by
      by_cases e1 : y = "eqk"
      · subst e1; simp [hk]
      · by_cases e2 : y = "jq"
        · subst e2; obtain ⟨v, hv⟩ := hj; simp [hv]
        · rw [hb.locals y (by simp [e1, e2])]; exact hs, hQ s1 u h1.2 hb, hk⟩

/-- HDR's reply to a field. -/
def hdrCode (f : List Byte) : Nat :=
  if CommandSpec.isFieldName f then (if CommandSpec.isServedField f then 42 else 47) else 7

theorem served_eq {f : List Byte} (h : 0 < f.length) : CommandSpec.isServedField f =
    (decide (metaOf f = 0) || decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaBytes []) ||
      decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaLines [])) := by
  have e1 : texts.getD SessionStore.tMetaBytes [] = CommandSpec.ascii ":BYTES" := rfl
  have e2 : texts.getD SessionStore.tMetaLines [] = CommandSpec.ascii ":LINES" := rfl
  rw [e1, e2]
  cases f with
  | nil => simp at h
  | cons x rest =>
    simp only [CommandSpec.isServedField, metaOf, List.head?_cons, List.getD_cons_zero]
    by_cases hx : x = 58#8 <;> simp [hx]

/-- `served` set where the field is a metadata item served. -/
theorem vserved_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} (sv uv : Bool) :
    Frag o [SessionStore.ifs (Syntax.v "eqk") [.assign "served" (Syntax.n 1)]]
      (fun u => VAt b ci L e u ∧ u.locals "served" = some (bw sv) ∧ u.locals "eqk" = some (bw uv))
      (fun u => VAt b ci L e u ∧ u.locals "served" = some (bw (sv || uv))) := by
  refine frag_ite o (C := .var "eqk") rfl (vat_and fun _ _ h => h)
    (fun s h => ⟨_, h.2.2⟩) ?_ (fun _ _ _ _ h => by simp [declared] at h)
    (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
  · refine frag_one (a := .assign "served" (.const (BitVec.ofNat 64 1))) rfl rfl rfl
      (vat_and fun _ _ h => h) (Safe.assign fun u ⟨h, hc⟩ => ?_)
    simp only [eval, h.2.2] at hc
    have := SessionCheck.bw_ne0 hc
    exact ⟨_, _, rfl, h.2.1, vat_set h.1 (by decide) _, by simp [setLocal, this]; rfl⟩
  · simp only [eval, h.2.2] at hc
    rw [h.2.1, SessionCheck.bw_eq0 hc, Bool.or_false]

theorem lowKK_serve : LowKK fieldServe :=
  lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append
    (lowKK_append (xs := [_]) (lowKK_one rfl (vset_lower (X := ownFs) rfl))
      (lowKK_append (xs := [_]) (lowKK_one rfl (vset_lower (X := ownFl) rfl)) (lowKK_dec rfl)))
    (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide))) (lowKK_one rfl rfl))
    (wordIsAt_low "s1" "l1" (by rw [texts_length]; decide)))
    (lowKK_one rfl rfl)) (lowKK_one rfl rfl)

theorem lowKK_field : LowKK fieldTree := by
  have hsplit : fieldTree = fieldTree.take 5 ++ fieldTree.drop 5 := (List.take_append_drop 5 _).symm
  rw [hsplit]
  exact lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl lowKK_serve fun k => ⟨k, rfl⟩)

/-- **HDR's field**: a header's name, or a metadata item's, and whether it is served: if it goes on, the code
`hdrCode`. -/
theorem field_frag (o : Oracle σ) {b : Word} {ci K : Nat} {L : List Byte} {e : PancakeState σ}
    (he : VEntry b ci K L e) (h2 : 2 ≤ (spans L).length) :
    Frag o fieldTree (VAt b ci L e) (VEnd b e (hdrCode (cut L ((spans L).getD 1 (0, 0))))) := by
  let p := (spans L).getD 1 (0, 0)
  let f := cut L p
  have hpm : p ∈ spans L := by
    exact spans_getD_mem (by omega)
  have hf1 : 0 < f.length := by rw [cut_length (spans_bound L p hpm)]; have := spans_pos L p hpm; omega
  have hsplit : fieldTree = fieldTree.take 5 ++ fieldTree.drop 5 := (List.take_append_drop 5 _).symm
  rw [hsplit]
  refine frag_append (fcheck_frag o he h2) ?_
  have hR : ∀ {Rn : Nat} {P : Assn σ}, (∀ u, P u → VAt b ci L e u) → (∀ u, P u → Rn = 7) →
      Frag o [] P (VEnd b e Rn) := fun hv h7 => frag_nil o fun u h => by rw [h7 u h]; exact vend_of (hv u h)
  refine frag_ite o (C := .var "ok") rfl (vend_clock _ _ _) (fun s h => ⟨_, h.2.2⟩) ?_ ?_
    (hR (fun u h => h.1.1) fun u ⟨h, hc⟩ => by
      simp only [eval, h.2.2] at hc
      have hn : CommandSpec.isFieldName f = false := SessionCheck.bw_eq0 hc
      show hdrCode f = 7
      simp only [hdrCode, hn]; rfl)
    (fun _ _ _ _ h => by simp [declared] at h)
  · refine frag_pure (CommandSpec.isFieldName f = true) (fun s ⟨h, hc⟩ => by
      simp only [eval, h.2.2] at hc; exact SessionCheck.bw_ne0 hc) lowKK_serve fun hfn => ?_
    let m := metaOf f
    let T1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "meta" = some (BitVec.ofNat 64 m)
    have st : ∀ (X : Nat) (hX : X ∈ vOffs) (x : String) {P : Assn σ}, (∀ u, P u → T1 u ∧ ∃ v, u.locals x = some v) →
        Frag o [vset X (Syntax.v x)] P T1 := fun X hX x {P} hP =>
      vset_frag o he hX (x := Syntax.v x) (E := .var x) rfl (fun u h => ⟨(hP u h).1.1, (hP u h).2⟩)
        (vat_and fun _ _ h => h) fun u m h hm => ⟨vat_store (hP u h).1.1 hX hm, (hP u h).1.2⟩
    let sv0 := decide (m = 0)
    have h3 : Frag o [.dec "served" (Syntax.eEq (Syntax.v "meta") (Syntax.n 0))] T1
        (fun u => VAt b ci L e u ∧ u.locals "served" = some (bw sv0)) :=
      frag_dec o (E := .cmp .equal (.var "meta") (.const (BitVec.ofNat 64 0))) rfl fun u h =>
        ⟨_, SessionCheck.eval_eq (x := m) (y := 0) (by have := metaOf_le f; omega) (by decide)
          (by simp only [eval]; exact h.2) rfl, vat_set h.1 (by decide) _, by simp [setLocal]; rfl⟩
    have hQ : ∀ (w : Value) (u u' : PancakeState σ), u.locals "served" = some w →
        SessionCheck.ButFor ["eqk", "jq"] u u' → u'.locals "served" = some w := fun w u u' h hb => by
      rw [hb.locals "served" (by decide)]; exact h
    have h4 := vcmp_frag o he h2 (t := SessionStore.tMetaBytes) (by rw [texts_length]; decide)
      (Q := fun u => u.locals "served" = some (bw sv0)) (hQ _)
    have h5 := vserved_frag o (b := b) (ci := ci) (L := L) (e := e) sv0
      (decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaBytes []))
    let sv1 := sv0 || decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaBytes [])
    have h6 := vcmp_frag o he h2 (t := SessionStore.tMetaLines) (by rw [texts_length]; decide)
      (Q := fun u => u.locals "served" = some (bw sv1)) (hQ _)
    have h7 := vserved_frag o (b := b) (ci := ci) (L := L) (e := e) sv1
      (decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaLines []))
    have hsv : (sv1 || decide (f.map CommandSpec.upper = texts.getD SessionStore.tMetaLines [])) =
        CommandSpec.isServedField f := by rw [served_eq hf1]
    have h8 : Frag o [.ite (Syntax.v "served") [vsay (.hdr false [] .current)] [vsay .fieldRefused]]
        (fun u => VAt b ci L e u ∧ u.locals "served" = some (bw (CommandSpec.isServedField f)))
        (VEnd b e (hdrCode f)) :=
      frag_ite o (C := .var "served") rfl (vend_clock _ _ _) (fun s h => ⟨_, h.2⟩)
        (vsay_frag o _ fun u ⟨h, hc⟩ => ⟨h.1, by
          simp only [eval, h.2] at hc; simp [hdrCode, hfn, SessionCheck.bw_ne0 hc, Session.replyCode]⟩)
        (fun _ _ _ _ h => by simp [declared, vsay] at h)
        (vsay_frag o _ fun u ⟨h, hc⟩ => ⟨h.1, by
          simp only [eval, h.2] at hc; simp [hdrCode, hfn, SessionCheck.bw_eq0 hc, Session.replyCode]⟩)
        (fun _ _ _ _ h => by simp [declared, vsay] at h)
    exact frag_append (frag_append (frag_append (frag_append (frag_append
      (frag_append (xs := [_]) (st ownFs (by decide) "s1" fun u h => ⟨⟨h.1.1, h.1.2.1⟩, _, h.1.1.s1⟩)
        (frag_append (xs := [_]) (st ownFl (by decide) "l1" fun u h => ⟨h, _, h.1.l1⟩) h3)) h4) h5) h6) h7)
      (frag_conseq h8 (fun u h => ⟨h.1, by rw [← hsv]; exact h.2⟩) fun _ h => h)
  · intro u y v h hy
    have : y = "served" := by
      simp [fieldServe, declared, vset, Session.wordIsAt, SessionStore.ifs] at hy; exact hy
    subst this; exact vend_restore h (by decide) v

theorem hdrOf_code (c : CommandSpec.Cmd) (f : List Byte) (s : CommandSpec.Sel) :
    Session.replyCode (CommandSpec.hdrOf c f s) = hdrCode f := by
  unfold CommandSpec.hdrOf hdrCode
  cases CommandSpec.isFieldName f <;> cases CommandSpec.isServedField f <;> rfl

theorem ans_hdr {c : CommandSpec.Cmd} (hc : c = .hdr ∨ c = .xhdr) (args : List (List Byte)) :
    (args.length = 1 → Session.replyCode (CommandSpec.answerIn c args) = hdrCode (args.getD 0 [])) ∧
    (args.length = 2 → Session.replyCode (CommandSpec.answerIn c args) =
      if selOf true (args.getD 1 []) ≠ 0 then hdrCode (args.getD 0 []) else 7) ∧
    (args.length ≠ 1 → args.length ≠ 2 → Session.replyCode (CommandSpec.answerIn c args) = 7) := by
  have two : ∀ f a, Session.replyCode (CommandSpec.answerIn c [f, a]) =
      if selOf true a ≠ 0 then hdrCode f else 7 := by
    intro f a
    have e : CommandSpec.answerIn c [f, a] = if CommandSpec.isMessageId a then CommandSpec.hdrOf c f (.id a)
        else match CommandSpec.range? a with
          | some (lo, hi) => CommandSpec.hdrOf c f (.range lo hi)
          | none => .syntax := by rcases hc with rfl | rfl <;> rfl
    rw [e]
    have rs : Session.replyCode .syntax = 7 := rfl
    cases hm : CommandSpec.isMessageId a
    · cases hr : CommandSpec.range? a with
      | none => simp [selOf, hm, hr, rs]
      | some v => obtain ⟨lo, hi⟩ := v; simp [selOf, hm, hr, hdrOf_code]
    · simp [selOf, hm, hdrOf_code]
  have one : ∀ f, Session.replyCode (CommandSpec.answerIn c [f]) = hdrCode f := by
    intro f
    have e : CommandSpec.answerIn c [f] = CommandSpec.hdrOf c f .current := by rcases hc with rfl | rfl <;> rfl
    rw [e, hdrOf_code]
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · rcases args with _ | ⟨f, _ | ⟨a, rest⟩⟩ <;> simp at h; exact one f
  · rcases args with _ | ⟨f, _ | ⟨a, _ | ⟨a3, rest⟩⟩⟩ <;> simp at h; exact two f a
  · rcases args with _ | ⟨f, _ | ⟨a, _ | ⟨a3, rest⟩⟩⟩
    · rcases hc with rfl | rfl <;> rfl
    · simp at h1
    · simp at h2
    · rcases hc with rfl | rfl <;> rfl

theorem argsOf_second (L : List Byte) : (argsOf L).getD 1 [] = cut L ((spans L).getD 2 (0, 0)) := by
  rcases h : spans L with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, rest⟩⟩⟩ <;> simp [argsOf, h, cut]

/-- **HDR's and XHDR's branch**: if it goes on, the code of the reply `answerIn` gives. -/
theorem hdr_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {c : CommandSpec.Cmd}
    (hc : c = .hdr ∨ c = .xhdr) (he : VEntry b ci (cmdCode (some c)) L e) :
    Frag o hdrTree (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0)
      (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
  have hsh : L.length < 2 ^ 62 := by have := he.short; simp [News.SessionSpec.lineLimit] at this; omega
  let A := (spans L).length - 1
  have hlen : (argsOf L).length = A := by simp [argsOf, A]
  let f := cut L ((spans L).getD 1 (0, 0))
  let a := cut L ((spans L).getD 2 (0, 0))
  obtain ⟨r1, r2, r3⟩ := ans_hdr hc (argsOf L)
  rw [hlen, argsOf_head] at r1
  rw [hlen, argsOf_head, argsOf_second] at r2
  rw [hlen] at r3
  -- one argument
  let G0 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧
    u.locals "good" = some (bw (decide (A = 1)))
  have f1 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 1)) [.assign "good" (Syntax.n 1)]]
      (fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0) G0 := by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 1))) rfl
      (vat_and fun _ _ h => h) (fun s h => ⟨_, vargs_eval h.1 hsh 1 (by decide)⟩) ?_
      (fun _ _ _ _ h => by simp [declared] at h) (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, h.2.1, ?_⟩)
      (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_one (a := .assign "good" (.const (BitVec.ofNat 64 1))) rfl rfl rfl
        (vat_and fun _ _ h => h) (Safe.assign fun u ⟨h, hc⟩ => ?_)
      rw [vargs_eval h.1 hsh 1 (by decide)] at hc
      have e0 := of_decide_eq_true (SessionCheck.bw_ne0 hc)
      exact ⟨_, _, rfl, h.2.2, vat_set h.1 (by decide) _, by simp [setLocal, h.2.1],
        by simp [setLocal, e0, A]; rfl⟩
    · rw [vargs_eval h.1 hsh 1 (by decide)] at hc
      rw [h.2.2, SessionCheck.bw_eq0 hc]; rfl
  -- two arguments: a message-id or a range
  let gv := decide (A = 1) || (decide (A = 2) && decide (selOf true a ≠ 0))
  let G1 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "good" = some (bw gv)
  have f2 : Frag o [SessionStore.ifs (Syntax.eEq (Syntax.v "args") (Syntax.n 2))
      (vpick (Syntax.v "s2") (Syntax.v "l2") (Syntax.n 1) ++
        [.assign "good" (SessionStore.ne (Syntax.v "sel") (Syntax.n 0))])] G0 G1 := by
    refine frag_ite o (C := .cmp .equal (.var "args") (.const (BitVec.ofNat 64 2))) rfl
      (vat_and fun _ _ h => h) (fun s h => ⟨_, vargs_eval h.1 hsh 2 (by decide)⟩) ?_
      (fun _ _ _ _ h => by simp [declared, vpick, SessionStore.ifs] at h)
      (frag_nil o fun s ⟨h, hc⟩ => ⟨h.1, ?_⟩) (fun _ _ _ _ h => by simp [declared] at h)
    · refine frag_pure (A = 2) (fun s ⟨h, hc⟩ => by
        rw [vargs_eval h.1 hsh 2 (by decide)] at hc; exact of_decide_eq_true (SessionCheck.bw_ne0 hc))
        (lowK_any _ (k := .skip) (c := _) rfl) fun hA2 => ?_
      refine frag_append (frag_conseq (vpick_frag o he (sn := "s2") (ln := "l2") (by decide) (by decide)
        (fun u h => vword2 he h (by omega)) (IDS := .const (BitVec.ofNat 64 1)) rfl (p := true)
        (fun u _ => rfl)) (fun s ⟨h, _⟩ => ⟨h.1, h.2.1⟩) fun _ h => h)
        (frag_one (a := .assign "good" (.cmp .equal (.cmp .equal (.var "sel") (.const (BitVec.ofNat 64 0)))
          (.const (BitVec.ofNat 64 0)))) rfl rfl rfl (vat_and fun _ _ h => h)
          (Safe.assign fun u h => ?_))
      obtain ⟨v, hv⟩ := h.1.good
      refine ⟨_, v, ne0_eval (by have := selOf_lt true (cut L ((spans L).getD 2 (0, 0))); omega) h.2, hv,
        vat_set h.1 (by decide) _, ?_⟩
      simp only [setLocal, gv, hA2, a]
      simp
    · have h1 : ¬A = 2 :=
        of_decide_eq_false (SessionCheck.bw_eq0 (by rw [vargs_eval h.1 hsh 2 (by decide)] at hc; exact hc))
      rw [h.2.2]; show _ = some (bw (decide (A = 1) || (decide (A = 2) && _)))
      rw [show decide (A = 2) = false from decide_eq_false h1]; simp
  have f3 : Frag o [SessionStore.ifs (Syntax.v "good") fieldTree] G1
      (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
    refine frag_ite o (C := .var "good") rfl (vend_clock _ _ _) (fun s h => ⟨_, h.2⟩) ?_
      (fun u y v h hy => vend_restore h (by
        rw [show declared fieldTree = ["f0", "meta"] from rfl] at hy; simp at hy; rcases hy with rfl | rfl <;>
            decide) v)
      (frag_nil o fun s ⟨h, hc⟩ => ?_) (fun _ _ _ _ h => by simp [declared] at h)
    · have hg : ∀ s, G1 s ∧ eval s (.var "good") ≠ some 0 → gv = true := fun s ⟨h, hc⟩ => by
        simp only [eval, h.2] at hc; exact SessionCheck.bw_ne0 hc
      refine frag_pure (gv = true) hg lowKK_field fun hgv => ?_
      have hgv' := hgv
      simp only [gv, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hgv'
      have h2 : 2 ≤ (spans L).length := by rcases hgv' with e1 | ⟨e1, _⟩ <;> omega
      have hR : Session.replyCode (CommandSpec.answerIn c (argsOf L)) = hdrCode f := by
        rcases hgv' with e1 | ⟨e1, e2⟩
        · exact r1 e1
        · rw [r2 e1, if_pos e2]
      rw [hR]
      exact frag_conseq (field_frag o he h2) (fun s h => h.1.1) fun _ h => h
    · simp only [eval, h.2] at hc
      have hgv := SessionCheck.bw_eq0 hc
      simp only [gv, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hgv
      have hR : Session.replyCode (CommandSpec.answerIn c (argsOf L)) = Session.replyCode .syntax := by
        rcases hgv with ⟨n1, n2 | n2⟩
        · exact r3 n1 n2
        · by_cases e2 : A = 2
          · rw [r2 e2, if_neg (by simpa using n2)]; rfl
          · exact r3 n1 e2
      rw [hR]; exact vend_of h.1
  exact frag_append (xs := [_]) f1 (frag_append (xs := [_]) f2 f3)

/-! ### `viewClassify` whole -/

theorem lowKK_hdr : LowKK hdrTree :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_append (xs := [_])
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl lowKK_field fun k => ⟨k, rfl⟩))

/-- `viewClassify` up to its last words: if it goes on, the reply's code in `r`. -/
theorem view_frag (o : Oracle σ) {b : Word} {ci : Nat} {L : List Byte} {e : PancakeState σ} {c : CommandSpec.Cmd}
    (hc : IsView c) (hw1 : 1 ≤ (spans L).length) (he : VEntry b ci (cmdCode (some c)) L e) :
    Frag o viewBody (Like e) (VEnd b e (Session.replyCode (CommandSpec.answerIn c (argsOf L)))) := by
  have hsh : L.length < 2 ^ 62 := by have := he.short; simp [News.SessionSpec.lineLimit] at this; omega
  let R := Session.replyCode (CommandSpec.answerIn c (argsOf L))
  let P0 : Assn σ := fun u => VAt b ci L e u ∧ u.locals "sel" = some 0 ∧ u.locals "good" = some 0
  have hK := cmdCode_lt (some c)
  have hor : ∀ u, P0 u → eval u (SessionCheck.or2E (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 17)))
      (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 19)))) =
      some (bw (decide (cmdCode (some c) = 17) || decide (cmdCode (some c) = 19))) := fun u h =>
    SessionCheck.eval_or2 (SessionCheck.eval_eq (by omega) (by decide) (by simp only [eval]; exact vcmd he h.1) rfl)
      (SessionCheck.eval_eq (by omega) (by decide) (by simp only [eval]; exact vcmd he h.1) rfl)
  have fi : Frag o [.ite (SessionStore.or2 (Syntax.eEq (Syntax.v "cmd") (Syntax.n 17))
      (Syntax.eEq (Syntax.v "cmd") (Syntax.n 19))) overTree hdrTree] P0 (VEnd b e R) := by
    refine frag_ite o (C := SessionCheck.or2E (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 17)))
      (.cmp .equal (.var "cmd") (.const (BitVec.ofNat 64 19)))) rfl (vend_clock _ _ _) (fun s h => ⟨_, hor s h⟩)
      ?_ (fun _ _ _ _ h => by simp [declared, overTree, SessionStore.ifs] at h) ?_
      (fun _ _ _ _ h => by simp [declared, hdrTree, SessionStore.ifs] at h)
    · refine frag_pure (c = .over ∨ c = .xover) (fun s ⟨h, hc'⟩ => ?_) (lowK_any _ (k := .skip) (c := _) rfl)
        fun hco => frag_conseq (over_frag o hco he) (fun s h => h.1) fun _ h => h
      rw [hor s h] at hc'
      have := SessionCheck.bw_ne0 hc'
      rcases hc with rfl | rfl | rfl | rfl <;> simp [cmdCode] at this ⊢
    · refine frag_pure (c = .hdr ∨ c = .xhdr) (fun s ⟨h, hc'⟩ => ?_) lowKK_hdr
        fun hch => frag_conseq (hdr_frag o hch he) (fun s h => h.1) fun _ h => h
      rw [hor s h] at hc'
      have := SessionCheck.bw_eq0 hc'
      rcases hc with rfl | rfl | rfl | rfl <;> simp [cmdCode] at this ⊢
  have fs : Frag o [vset ownVSel (Syntax.v "sel")] (VEnd b e R) (VEnd b e R) :=
    frag_one (vset_lower (X := ownVSel) (e := Syntax.v "sel") rfl) rfl rfl (vend_clock _ _ _)
      (Safe.store fun u ⟨hm, hr, ⟨sv, hs⟩, hd, hba, hbe, hco⟩ => by
        obtain ⟨T, hT⟩ := SessionAppend.lay
        obtain ⟨h1, h2⟩ := vOffs_facts ownVSel (by decide)
        have := hT.above; have := SessionAppend.nums.own64
        have ha : u.memaddrs (b + BitVec.ofNat 64 (ownOff + ownVSel)) = true := by
          rw [hd]; exact SessionAppend.own_addr he.hcov h1 (by omega) (by rw [hT.eq]; omega)
        refine ⟨b + BitVec.ofNat 64 (ownOff + ownVSel), sv,
          fun k => if k = b + BitVec.ofNat 64 (ownOff + ownVSel) then sv else u.memory k,
          by simp only [eval, hba, he.base], by simp only [eval]; exact hs, by simp only [memStoreWord, ha, if_true],
          fun a ha' => ?_, hr, ⟨sv, hs⟩, hd, hba, hbe, hco⟩
        have : a ≠ b + BitVec.ofNat 64 (ownOff + ownVSel) := fun h => ha' (by
          rw [h]; simp only [vWords, List.mem_map]; exact ⟨ownVSel, by decide, rfl⟩)
        simp only [if_neg this]; exact hm a ha')
  exact frag_append (frag_append (frag_append (frag_append (vhead_frag o he) (vscan_frag o he))
    (vkept_frag o he)) (vdecs_frag o hw1 hsh)) (frag_append (xs := [_]) fi fs)

/-- The reply's code given back in the return word. -/
theorem give_run (o : Oracle σ) {b : Word} {e : PancakeState σ} {R : Nat}
    (hcov : Analyzer.Covers SessionLayout.size e.memaddrs b)
    (hb : e.baseAddr = b) :
    SafeR o (VEnd b e R) (.seq (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet)))) (.var "r"))
      (.ret (.const (BitVec.ofNat 64 0)))) (CallRet b R e.memory) (fun _ => False) := by
  let M : Assn σ := fun u => u.memory (SessionCheck.retW b) = BitVec.ofNat 64 R ∧
    ∀ a, a ∉ clsWords b → u.memory a = e.memory a
  refine WpRet.seq (M := M) (WpRet.store fun u ⟨hm, hr, _, hd, hba, _⟩ => ?_)
    (WpRet.ret fun u h => ⟨0, rfl, rfl, h.1, h.2⟩) (fun _ _ h => h)
  have ha : u.memaddrs (SessionCheck.retW b) = true := by rw [hd]; exact SessionAppend.retW_addr hcov
  refine ⟨SessionCheck.retW b, BitVec.ofNat 64 R,
    fun k => if k = SessionCheck.retW b then BitVec.ofNat 64 R else u.memory k,
    by simp only [eval, hba, hb, SessionCheck.retW], by simp only [eval]; exact hr,
    by simp only [memStoreWord, ha, if_true], by simp, fun a ha' => ?_⟩
  have h1 : a ≠ SessionCheck.retW b := fun h => ha' (h ▸ retW_mem b)
  have h2 : a ∉ vWords b := fun h => ha' (vWords_cls b a h)
  simp only [if_neg h1]; exact hm a h2

/-- `viewClassify`'s body lowers before anything. -/
theorem lowKK_view : LowKK viewBody := by
  have hhead : LowKK viewHead :=
    lowKK_append (xs := [_]) (lowKK_one rfl (SessionRun.keptIn_lower rfl _))
      (lowKK_append (xs := [_]) (lowKK_dec SessionCheck.blk_lower)
        (lowKK_append (xs := [_]) (lowKK_dec rfl) (lowKK_one rfl (SessionRun.keptIn_lower rfl _))))
  exact lowKK_append (lowKK_append (lowKK_append (lowKK_append hhead (lowK_any _ (k := .skip) (c := _) rfl))
    (lowK_any _ (k := .skip) (c := _) rfl)) (lowK_any _ (k := .skip) (c := _) rfl))
    (lowKK_append (xs := [_]) (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) lowKK_hdr)
      (lowKK_one rfl (vset_lower rfl)))

/-- How its last words lower. -/
theorem give_lower : Lower.lowerStmtsFold (SessionStore.give (Syntax.v "r")) =
    some (.seq (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet)))) (.var "r"))
      (.ret (.const (BitVec.ofNat 64 0)))) := by
  simp [SessionStore.give, Lower.lowerStmtsFold, Lower.lowerStmt1,
    SessionAppend.at_lower SessionAppend.ret_facts.2.2.2, Syntax.v, Syntax.n, Lower.lowerExp]

/-- `viewClassify` lowers. -/
theorem view_lowers : ∃ body, Lower.lower Session.viewClassify = some body := by
  obtain ⟨c, hc⟩ := lowKK_view _
  refine ⟨c, ?_⟩
  rw [Lower.lower, view_eq, Block.fold_split viewBody _ (by simp [SessionStore.give]) give_lower]
  exact hc

/-- **`viewClassify` gives the code of `CommandSpec.answerIn`'s reply to OVER, HDR, XOVER and XHDR**: from its entry
on a line of words, if it returns, it gives back zero, that code in the return word, every word but `clsWords` as it
was. -/
theorem viewClassify_ok (o : Oracle σ) (b : Word) {code : String → Option (List String × PancakeProg)}
    {body : PancakeProg} (hcode : code "viewClassify" = some (["c", "cmd"], body))
    (hbody : Lower.lower Session.viewClassify = some body) : FnOk o "viewClassify" b IsView code := by
  refine ⟨body, hcode, fun ci c L s1 hc hw1 he _ => ?_⟩
  have hsplit := Block.fold_split viewBody (SessionStore.give (Syntax.v "r")) (by simp [SessionStore.give]) give_lower
  rw [Lower.lower, view_eq, hsplit] at hbody
  obtain ⟨c', hc', hs⟩ := view_frag o hc hw1 he _ (CallRet b (Session.replyCode (CommandSpec.answerIn c (argsOf L)))
    s1.memory) (fun _ => False) (fun _ _ _ h _ => h) (give_run o he.hcov he.base)
  rw [hbody] at hc'; cases hc'
  exact WpRet.conseq hs (fun u (hu : u = s1) => hu ▸ like_refl s1) (fun _ _ h => h) fun _ h => h

/-! ## `classify` with `viewClassify` proven -/

/-- **`classify` gives the code of `CommandSpec.replyIn`'s reply**, `viewClassify` as the code holds it and
`listClassify` by its contract: from its entry, if it goes on, `r` holds that code, every local but its own and every
word but `clsWords` as they were. What the reply carries past its code is not shown. -/
theorem classify_run (o : Oracle σ) {b : Word} {ci : Nat} {offered : Bool} {k : FrameSpec.Kind} {L : List Byte}
    {s0 : PancakeState σ} (hs : ClsIn b ci offered k L s0) (hgn : GnCode s0.code) {vbody : PancakeProg}
    (hvc : s0.code "viewClassify" = some (["c", "cmd"], vbody)) (hvl : Lower.lower Session.viewClassify = some vbody)
    (hlc : FnOk o "listClassify" b IsList s0.code) :
    Frag o Session.classify (Like s0) (Out b s0 (Session.replyCode (CommandSpec.replyIn offered ⟨k, L⟩))) :=
  classify_frag o hs hgn (viewClassify_ok o b hvc hvl) hlc

/-! ### The premises can hold -/

theorem kept_witness : Kept zeroState zeroState := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨0, rfl⟩⟩

theorem treeAt_witness : TreeAt [] zeroState zeroState :=
  ⟨kept_witness, rfl, rfl, rfl, rfl, rfl, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

theorem after_witness : After 0 zeroState zeroState := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, ⟨0, rfl⟩⟩

theorem out_witness : Out 0 zeroState 0 zeroState := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pickAt_witness : PickAt zeroState 0 zeroState := ⟨SessionCheck.but_refl _ _, rfl, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

theorem isView_witness : IsView .over := Or.inl rfl

theorem isList_witness : IsList .mode := Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- `viewClassify`'s locals declared, of an empty line in block zero past base zero. -/
def vState : PancakeState Unit :=
  { bareState () with
    locals := fun x => if x = "blk" then some (SessionFrame.blockAt 0 0)
      else if x = "r" then some (BitVec.ofNat 64 (Session.replyCode .syntax)) else some 0 }

theorem vat_witness : VAt 0 0 [] vState vState :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨0, rfl⟩,
    ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

theorem vend_witness : VEnd 0 vState (Session.replyCode .syntax) vState :=
  ⟨fun _ _ => rfl, rfl, ⟨0, rfl⟩, rfl, rfl, rfl, rfl⟩

/-- A code with `groupName` as it lowers. -/
def gnCode : String → Option (List String × PancakeProg) := fun f =>
  if f = "groupName" then some (["c", "s1", "l1"], (SessionCheck.gnA (σ := Unit) 0 [] (bareState ())).erase) else none

theorem gnCode_witness : GnCode gnCode := ⟨_, rfl, SessionCheck.groupName_lower (σ := Unit) 0 [] (bareState ())⟩

/-- A code whose `listClassify` never returns: so it keeps any contract on what it gives back. -/
def loopCode : String → Option (List String × PancakeProg) := fun f =>
  if f = "listClassify" then some (["c", "cmd"], .while_ (.const 1) .skip) else none

theorem fnOk_loop {b : Word} {code : String → Option (List String × PancakeProg)}
    (h : code "listClassify" = some (["c", "cmd"], .while_ (.const 1) .skip)) :
    FnOk (σ := Unit) Oracle.idle "listClassify" b IsList code :=
  ⟨_, h, fun _ _ _ _ _ _ _ _ => conseq (WpRet.while_ (I := fun _ => True) (fun _ _ => ⟨1, rfl⟩)
    (conseq (WpRet.skip _ (fun _ => True) _) (fun _ _ => trivial) (fun _ _ h => h) (fun _ h => h))
    (fun _ _ _ => trivial)) (fun _ _ => trivial) (fun _ _ h => h) fun s ⟨_, h⟩ => absurd h (by simp [eval])⟩

theorem fnOk_witness : FnOk (σ := Unit) Oracle.idle "listClassify" 0 IsList loopCode := fnOk_loop rfl

/-- `groupName` as it lowers, `viewClassify` as `vb`, and a `listClassify` that never returns. -/
def jointCode (vb : PancakeProg) : String → Option (List String × PancakeProg) := fun f =>
  if f = "groupName" then gnCode f else if f = "viewClassify" then some (["c", "cmd"], vb) else loopCode f

/-- The kept word of block zero's line. -/
def jKept : Word := SessionFrame.blockAt SessionAppend.wb 0 + BitVec.ofNat 64 32

/-- The witnesses' words at connection zero's `classify`, the line of the one octet zero, no store. -/
def jState (vb : PancakeProg) : PancakeState Unit :=
  { SessionText.wState with
    memory := fun a => if a = jKept then 1 else SessionText.wState.memory a
    code := jointCode vb
    locals := fun x => if x = "blk" then some (SessionFrame.blockAt SessionAppend.wb 0)
      else if x = "kind" ∨ x = "kept" then some 1 else some 0 }

theorem jKept_eq : jKept = SessionAppend.wb + BitVec.ofNat 64 (SessionAppend.tOff + cFramer + 32) := by
  rw [jKept, SessionAppend.blockAt_off, Nat.zero_mul,
    show SessionAppend.tOff + 0 = SessionAppend.tOff from Nat.add_zero _]

theorem j_ne {x : Nat} (hx : x < SessionAppend.tOff + cFramer + 32 ∨ SessionAppend.tOff + cFramer + 32 < x)
    (h64 : x < 2 ^ 64) : SessionAppend.wb + BitVec.ofNat 64 x ≠ jKept := by
  rw [jKept_eq]
  obtain ⟨T, hT⟩ := SessionAppend.lay
  rw [hT.eq] at hx ⊢
  have := hT.room
  have hc : cFramer < 2712 := by
    have := SessionAppend.block_facts.fits; have := SessionAppend.block_facts.slot
    have := SessionAppend.block_facts.head; omega
  exact region_addr_inj _ _ _ h64 (by omega) (by omega)

theorem j_far {x : Nat} (hx : x < SessionAppend.tOff) :
    byteAlign (SessionAppend.wb + BitVec.ofNat 64 x) ≠ jKept := by
  rw [byteAlign_base (by decide)]
  obtain ⟨T, hT⟩ := SessionAppend.lay
  have := hT.room
  rw [hT.eq] at hx
  exact j_ne (by rw [hT.eq]; omega) (by omega)

/-- Block zero's first octet, zero. -/
theorem j_line (vb : PancakeProg) : memLoadByte (jState vb).memory (jState vb).memaddrs (jState vb).be
    (SessionFrame.blockAt SessionAppend.wb 0 + BitVec.ofNat 64 40 + BitVec.ofNat 64 0) = some 0 := by
  rw [add_ofNat, SessionAppend.blockAt_off]
  obtain ⟨T, G, S, E, hw, hT, hG, hS, -⟩ := SessionText.w_far
  obtain ⟨hc1, hc2, hc3⟩ : cFramer + 40 ≠ SessionLayout.cGroup ∧ cFramer % 8 = 0 ∧ cFramer + 48 ≤ 173568 := by
    decide +kernel
  have hal : T % 8 = 0 := hT ▸ SessionText.w_ends.tAl
  have g1 := hw.group
  have g2 := hw.groupIn
  have g3 := hw.sizeLe
  have g4 := hw.textsEnd
  have hX : SessionAppend.tOff + 0 * connSlot + cFramer + (40 + 0) = T + cFramer + 40 := by rw [hT]; omega
  rw [hX]
  have hm : (T + cFramer + 40) % 8 = 0 := by omega
  have h8 : (T + cFramer + 40) / 8 * 8 = T + cFramer + 40 := by omega
  have ha : byteAlign (SessionAppend.wb + BitVec.ofNat 64 (T + cFramer + 40)) =
      SessionAppend.wb + BitVec.ofNat 64 (T + cFramer + 40) := by
    rw [byteAlign_base (by decide), h8]
  have hd : (jState vb).memaddrs (SessionAppend.wb + BitVec.ofNat 64 (T + cFramer + 40)) = true := by
    rw [show (jState vb).memaddrs = SessionText.wState.memaddrs from rfl]
    exact SessionText.w_cov.2 _ (by simp only [Analyzer.floor]; omega) (by rw [hS]; omega) hm
  have hY := SessionText.w_high (Y := T + cFramer + 40) (by omega) (by rw [hT]; omega) (by rw [hS]; omega)
    (by rw [hG]; omega)
  have hne := j_ne (x := T + cFramer + 40) (by rw [hT]; omega) (by omega)
  simp only [memLoadByte, ha, hd, if_true]
  rw [show (jState vb).memory = fun a => if a = jKept then 1 else SessionText.wState.memory a from rfl]
  dsimp only
  rw [if_neg hne, SessionText.w_mem, hY, if_neg (by rw [hT, hG]; omega)]
  generalize SessionAppend.wb + _ = a
  simp [getByte]

theorem j_texts (vb : PancakeProg) :
    SessionAppend.TextsIn SessionAppend.wb (jState vb).memory (jState vb).memaddrs (jState vb).be := by
  intro k hk i hi
  have hb := SessionText.w_texts k hk i hi
  have ht := SessionAppend.text_below hk
  rw [add_ofNat] at hb ⊢
  have hl : (texts.getD k []).length = Session.textLen k := rfl
  rw [show (jState vb).memaddrs = SessionText.wState.memaddrs from rfl,
    show (jState vb).be = SessionText.wState.be from rfl,
    load_of_word (m := SessionText.wState.memory) (by
      show (if _ = jKept then _ else _) = _
      rw [if_neg (j_far (by omega))])]
  exact hb

theorem clsIn_joint (vb : PancakeProg) : ClsIn SessionAppend.wb 0 false .command [0] (jState vb) where
  line := ⟨rfl, rfl, fun j hj => by
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      exact j_line vb, by decide⟩
  c := rfl
  hci := by decide
  kind := rfl
  r := ⟨0, rfl⟩
  base := rfl
  hb := by decide
  hcov := SessionText.w_cov
  texts := j_texts vb
  store := by
    rw [show (jState vb).memory = fun a => if a = jKept then 1 else SessionText.wState.memory a from rfl]
    dsimp only
    obtain ⟨T, hT⟩ := SessionAppend.lay
    have := hT.above
    have := hT.room
    have h : ownStore + 8 ≤ ownTexts := by decide +kernel
    rw [if_neg (j_ne (by rw [hT.eq]; omega) (by omega))]
    exact SessionText.w_own_val (by decide +kernel)
  short := by decide
  keptW := by
    rw [show (jState vb).memory = fun a => if a = jKept then 1 else SessionText.wState.memory a from rfl]
    exact if_pos rfl

theorem clsIn_witness : ClsIn SessionAppend.wb 0 false .command [0] (jState .skip) := clsIn_joint .skip

theorem gnCode_joint (vb : PancakeProg) : GnCode (jState vb).code :=
  ⟨_, rfl, SessionCheck.groupName_lower (σ := Unit) 0 [] (bareState ())⟩

theorem view_joint (vb : PancakeProg) : (jState vb).code "viewClassify" = some (["c", "cmd"], vb) := by
  show jointCode vb "viewClassify" = _
  unfold jointCode
  rw [if_neg (by decide), if_pos rfl]

theorem fnOk_joint (vb : PancakeProg) :
    FnOk (σ := Unit) Oracle.idle "listClassify" SessionAppend.wb IsList (jState vb).code :=
  fnOk_loop (by
    show jointCode vb "listClassify" = _
    unfold jointCode; rw [if_neg (by decide), if_neg (by decide)]; rfl)

/-- **`classify_run`'s premises hold together**, on a line of one word. -/
theorem classify_premises : ∃ (s0 : PancakeState Unit) (vb : PancakeProg),
    ClsIn SessionAppend.wb 0 false .command [0] s0 ∧ GnCode s0.code ∧
    s0.code "viewClassify" = some (["c", "cmd"], vb) ∧ Lower.lower Session.viewClassify = some vb ∧
    FnOk (σ := Unit) Oracle.idle "listClassify" SessionAppend.wb IsList s0.code ∧ 1 ≤ (spans [0]).length := by
  obtain ⟨vb, hvb⟩ := view_lowers
  exact ⟨jState vb, vb, clsIn_joint vb, gnCode_joint vb, view_joint vb, hvb, fnOk_joint vb, by decide⟩

/-- The same words with `cmd` OVER's code, the state `viewClassify` would enter on. -/
def veState : PancakeState Unit := { jState .skip with locals := fun x => if x = "cmd" then some 17 else some 0 }

theorem vEntry_witness : VEntry SessionAppend.wb 0 (cmdCode (some .over)) [0] veState where
  base := rfl
  hb := by decide
  hcov := SessionText.w_cov
  c := rfl
  hci := by decide
  cmd := rfl
  kept := by
    rw [show veState.memory = fun a => if a = jKept then 1 else SessionText.wState.memory a from rfl]
    exact if_pos rfl
  bytes := fun j hj => by
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    rw [show veState.memory = (jState .skip).memory from rfl, show veState.memaddrs = (jState .skip).memaddrs from rfl,
      show veState.be = (jState .skip).be from rfl]
    exact j_line .skip
  short := by decide
  texts := by
    rw [show veState.memory = (jState .skip).memory from rfl, show veState.memaddrs = (jState .skip).memaddrs from rfl,
      show veState.be = (jState .skip).be from rfl]
    exact j_texts .skip

end DN.Server.SessionClassify
