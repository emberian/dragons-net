-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionAppend

/-!
# DN.Server.SessionState

The session's connections in the heap as `SessionSpec` has them: a record (`ConnAt`), the table (`TableAt`). A record
names the store's groups and commits by place, read through the store's `Posting`.
-/

namespace DN.Server.SessionState

open DN.Compiler DN.Server.SessionLayout DN.News.SessionSpec
open DN.News.FramerCode (Holds Fits Chunk bw)
open DN.News.FrameSpec (Byte)
open DN.Server.SessionFrame (recordAt blockAt heldAt)
open DN.News.CommandSpec (Cmd Wildmat wildmatch)

variable {σ : Type}

/-- Word `k` of connection `ci`'s record. -/
def recW (b : Word) (ci k : Nat) : Word := recordAt b ci + BitVec.ofNat 64 k

/-- A word holding the number `x`, below `2 ^ 63`. -/
def NumW (s : PancakeState σ) (a : Word) (x : Nat) : Prop := s.memory a = BitVec.ofNat 64 x ∧ x < 2 ^ 63

/-- The read an ARTICLE, HEAD, BODY, OVER or HDR waits for, as the record codes it. -/
def wantCode : Cmd → Nat
  | .article => 1 | .head => 2 | .body => 3 | .over => 4 | .hdr => 5 | _ => 0

/-- Where a connection stands with AUTHINFO, as the record codes it. -/
def authCode : Auth → Nat
  | .none => authNone | .named _ => authNamed | .verify .. => authVerify | .checking => authChecking
  | .done => authDone

/-- The largest article number the program takes. -/
def numMax : Nat := 2147483647

/-- A place kept as one more, none as zero. -/
def placeCode : Option Nat → Nat
  | none => 0
  | some k => k + 1

/-- `bs` in the record's bytes from word `k`, its length in word `kl`, at most `most`. -/
def BytesW (b : Word) (ci kl k most : Nat) (bs : List Byte) (s : PancakeState σ) : Prop :=
  NumW s (recW b ci kl) bs.length ∧ bs.length ≤ most ∧ Chunk s (recW b ci k) bs

/-- The name and the password AUTHINFO keeps. -/
def AuthIn (b : Word) (ci : Nat) (s : PancakeState σ) : Auth → Prop
  | .named nm => BytesW b ci cNameLen cName News.CommandSpec.nameMax nm s
  | .verify nm pw =>
    BytesW b ci cNameLen cName News.CommandSpec.nameMax nm s ∧
      BytesW b ci cPassLen cPass News.CommandSpec.passwordMax pw s
  | _ => True

/-- The selected group: none as zero, else one more than its place among the store's groups. -/
def GroupIn (p : Posting) (w : Word) : Option (List Byte) → Prop
  | none => w = 0
  | some g => ∃ k, w = BitVec.ofNat 64 (k + 1) ∧ p.groups[k]? = some g

/-- The read a connection waits for: its code, its first line's number, its commit's place among the store's. -/
def WantIn (p : Posting) (wc wci wno : Word) : Option (Cmd × Nat × List Byte) → Prop
  | none => wc = 0
  | some (k, no, id) => wc = BitVec.ofNat 64 (wantCode k) ∧ 0 < wantCode k ∧ wno = BitVec.ofNat 64 no ∧
    no ≤ numMax ∧ ∃ j cm, wci = BitVec.ofNat 64 j ∧ p.held[j]? = some cm ∧ cm.messageId = id

/-- The group's articles after number `n` up to `upto`, by number, each with its commit. -/
def restOf (held : List News.Journal.Commit) (g : List Byte) (n upto : Nat) : List (Nat × News.Journal.Commit) :=
  (((numbered held g).filter fun x => n < x.1 && x.1 ≤ upto).mergeSort fun a c => a.1 ≤ c.1).filterMap fun x =>
    (held.find? (·.messageId == x.2)).map fun cm => (x.1, cm)

/-- What is left of a reply that goes out a part at a time. A group's numbers: its place, the lowest left, the
highest, and a commit's place before which none lies. The groups: the next one's place, a bit for each the wildmat
takes. -/
def ListIn (p : Posting) (lk la lb lc ld : Word) : Option Listing → Prop
  | none => lk = 0
  | some (.numbers g from_ upto) => lk = 1 ∧ (∃ k, la = BitVec.ofNat 64 k ∧ p.groups[k]? = some g) ∧
    lb = BitVec.ofNat 64 from_ ∧ from_ < 2 ^ 63 ∧ lc = BitVec.ofNat 64 upto ∧ upto < 2 ^ 63 ∧
    ∃ d, ld = BitVec.ofNat 64 d ∧ d ≤ p.held.length ∧
      ((numbered (p.held.take d) g).map (·.1)).all fun x => x < from_ || upto < x
  | some (.groups w next) => lk = 2 ∧ la = BitVec.ofNat 64 next ∧ next ≤ groupsMax ∧
    ∀ k (h : k < p.groups.length), lc.toNat.testBit k = w.all (wildmatch · p.groups[k])

/-- A flag as a number. -/
def bnat (x : Bool) : Nat := if x then 1 else 0

/-- The view of an OVER or HDR, kept until its read ends: its flags and HDR's field. Its group, lowest and highest
numbers give its rest; no group is `groupsMax`, by message-id or of the current article. -/
def ViewIn (p : Posting) (b : Word) (ci : Nat) (s : PancakeState σ) (want : Option (Cmd × Nat × List Byte)) :
    Option News.PostSpec.View → Prop
  | none => ∀ k n id, want = some (k, n, id) → k ≠ .over ∧ k ≠ .hdr
  | some v => v.first = true ∧ s.memory (recW b ci cViewF) = BitVec.ofNat 64 (bnat v.legacy + 2 * bnat v.byId) ∧
    ∃ k n id, want = some (k, n, id) ∧
      (match v.field with
        | none => k = .over
        | some f => k = .hdr ∧ BytesW b ci cFieldLen cField fieldMax f s) ∧
      ∃ gi lo upto, s.memory (recW b ci cViewGi) = BitVec.ofNat 64 gi ∧
        s.memory (recW b ci cViewLo) = BitVec.ofNat 64 lo ∧ s.memory (recW b ci cViewUpto) = BitVec.ofNat 64 upto ∧
        upto ≤ numMax ∧ lo ≤ n ∧ (v.byId = true → groupsMax ≤ gi) ∧
        v.rest = if gi < groupsMax then restOf p.held (p.groups.getD gi []) n upto else []

/-- **Connection `ci`'s record holds `c`**, the store's places read through `p`. -/
structure ConnAt (b : Word) (p : Posting) (ci : Nat) (c : Conn) (s : PancakeState σ) : Prop where
  live : s.memory (recW b ci cLive) = 1
  gen : NumW s (recW b ci cGen) c.gen
  phase : s.memory (recW b ci cPhase) = BitVec.ofNat 64 (Session.phaseCode c.phase)
  line : Holds s (blockAt b ci) c.line ∧ Fits lineLimit c.line
  held : ∃ pre : List Byte, NumW s (recW b ci cHeldPos) pre.length ∧
    NumW s (recW b ci cHeldLen) (pre.length + c.held.length) ∧ pre.length + c.held.length ≤ data ∧
    Chunk s (heldAt b ci) (pre ++ c.held)
  out : NumW s (recW b ci cOutLen) c.out.length ∧ c.out.length ≤ data ∧
    DN.Compiler.Bytes.memBytesAt s.memory s.memaddrs s.be (SessionAppend.outAt b ci) c.out
  reading : s.memory (recW b ci cReading) = bw c.reading
  blocked : s.memory (recW b ci cBlocked) = bw c.blocked
  first : NumW s (recW b ci cFirst) c.first
  idle : NumW s (recW b ci cIdle) c.idle
  lineDue : NumW s (recW b ci cLineDue) c.lineDue
  number : NumW s (recW b ci cNumber) c.number
  greeted : s.memory (recW b ci cGreeted) = bw c.greeted
  logins : s.memory (recW b ci cLogins) = bw c.logins
  tls : s.memory (recW b ci cTls) = bw c.tls
  auth : s.memory (recW b ci cAuth) = BitVec.ofNat 64 (authCode c.auth) ∧ AuthIn b ci s c.auth
  waiting : s.memory (recW b ci cWaiting) = bw c.waiting
  post : s.memory (recW b ci cPost) = BitVec.ofNat 64 (placeCode c.post) ∧ ∀ k, c.post = some k → k < posts
  articleDue : NumW s (recW b ci cArticleDue) c.articleDue
  want : WantIn p (s.memory (recW b ci cWant)) (s.memory (recW b ci cWantCi)) (s.memory (recW b ci cWantNo)) c.want
  read : s.memory (recW b ci cRead) = BitVec.ofNat 64 (placeCode c.read) ∧ ∀ k, c.read = some k → k < reads
  view : ViewIn p b ci s c.want c.view
  group : GroupIn p (s.memory (recW b ci cGroup)) c.group
  current : NumW s (recW b ci cCurrent) c.current ∧ c.current ≤ numMax
  listing : ListIn p (s.memory (recW b ci cList)) (s.memory (recW b ci cListA)) (s.memory (recW b ci cListB))
    (s.memory (recW b ci cListC)) (s.memory (recW b ci cListD)) c.listing

/-- Record `ci` holds the table's entry `e`, `g` the last generation opened there, no action of the turn. -/
def SlotAt (b : Word) (p : Posting) (ci g : Nat) (e : Option Conn) (s : PancakeState σ) : Prop :=
  NumW s (recW b ci cGen) g ∧ s.memory (recW b ci cActed) = 0 ∧
    match e with
    | none => s.memory (recW b ci cLive) = 0
    | some c => ConnAt b p ci c s ∧ c.gen = g

/-- **The table holds `t`**, the last generation opened at each index in its record, the records addressable. -/
structure TableAt (b : Word) (p : Posting) (t : Table) (gens : List Nat) (s : PancakeState σ) : Prop where
  len : t.length = SessionLayout.conns
  gensLen : gens.length = SessionLayout.conns
  slot : ∀ ci, ci < SessionLayout.conns → SlotAt b p ci (gens.getD ci 0) (t.getD ci none) s
  dom : ∀ ci k, ci < SessionLayout.conns → k < connSlot → k % 8 = 0 → s.memaddrs (recW b ci k) = true

/-! ## A record depends only on its words -/

theorem rec_al {b : Word} (hb : b.toNat % 8 = 0) (ci : Nat) : (recordAt b ci).toNat % 8 = 0 := by
  have hT := SessionAppend.table_aligned; have hs := SessionAppend.nums.slot
  simp only [recordAt]; rw [← SessionAppend.tOff_eq]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [hs]
  generalize SessionAppend.tOff = T at *
  omega

theorem recW_add (b : Word) (ci k j : Nat) : recW b ci k + BitVec.ofNat 64 j = recW b ci (k + j) :=
  DN.Compiler.Bytes.add_ofNat _ _ _

theorem byte_rec {b : Word} (hb : b.toNat % 8 = 0) (ci k : Nat) : byteAlign (recW b ci k) = recW b ci (k / 8 * 8) :=
  DN.Compiler.Bytes.byteAlign_base (rec_al hb ci) k

/-- The words of a record `ConnAt` does not read: the framer's verdict, and whether it acted in the turn. -/
def Unread (k : Nat) : Prop := k = cFramer + 24 ∨ k = cFramer + 32 ∨ k = cActed

/-- Two states alike on record `ci`'s words but those it does not read. -/
def SameRec (b : Word) (ci : Nat) (s s' : PancakeState σ) : Prop :=
  s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧
    ∀ k, k < connSlot → ¬Unread k → s'.memory (recW b ci k) = s.memory (recW b ci k)

/-- The record's fixed offsets these proofs read. -/
theorem offs : cFramer = 1136 ∧ cHeld = 1688 ∧ cOut = 2200 ∧ connSlot = 2712 ∧ cName = 808 ∧ cPass = 880 ∧
    cField = 264 ∧ cNameLen = 800 ∧ cPassLen = 872 ∧ cFieldLen = 256 ∧ data = 512 ∧ lineLimit = 512 ∧
    News.CommandSpec.nameMax = 64 ∧ News.CommandSpec.passwordMax = 256 ∧ fieldMax = 512 ∧ cActed = 88 ∧
    cLogins = 776 ∧ cTls = 784 ∧ cAuth = 792 := by decide

theorem unread_iff {k : Nat} : Unread k ↔ k = 1160 ∨ k = 1168 ∨ k = 88 := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, -⟩ := offs
  simp only [Unread, h1, h16]

section Same
variable {b : Word} {ci : Nat} {s s' : PancakeState σ}

theorem word_same (hS : SameRec b ci s s') {k : Nat} (hk : k < connSlot) (hu : k ≠ 1160 ∧ k ≠ 1168 ∧ k ≠ 88) :
    s'.memory (recW b ci k) = s.memory (recW b ci k) :=
  hS.2.2 k hk fun h => by rw [unread_iff] at h; omega

theorem byte_same (hb : b.toNat % 8 = 0) (hS : SameRec b ci s s') {x : Nat} (hx : x < connSlot)
    (hu : x < 88 ∨ 96 ≤ x ∧ x < 1160 ∨ 1176 ≤ x) :
    memLoadByte s'.memory s'.memaddrs s'.be (recW b ci x) = memLoadByte s.memory s.memaddrs s.be (recW b ci x) := by
  unfold memLoadByte; rw [byte_rec hb, hS.1, hS.2.1, word_same hS (by omega) (by omega)]

theorem chunk_same (hb : b.toNat % 8 = 0) (hS : SameRec b ci s s') {k : Nat} {bs : List Byte}
    (hk : k + bs.length ≤ connSlot) (hu : k + bs.length ≤ 1160 ∧ 96 ≤ k ∨ 1176 ≤ k)
    (h : Chunk s (recW b ci k) bs) : Chunk s' (recW b ci k) bs := fun j hj => by
  rw [recW_add, byte_same hb hS (by omega) (by omega), ← recW_add]; exact h j hj

theorem numW_same (hS : SameRec b ci s s') {k x : Nat} (hk : k < connSlot) (hu : k ≠ 1160 ∧ k ≠ 1168 ∧ k ≠ 88)
    (h : NumW s (recW b ci k) x) : NumW s' (recW b ci k) x := ⟨(word_same hS hk hu).trans h.1, h.2⟩

theorem bytesW_same (hb : b.toNat % 8 = 0) (hS : SameRec b ci s s') {kl k most : Nat} {bs : List Byte}
    (hkl : kl < connSlot) (hul : kl ≠ 1160 ∧ kl ≠ 1168 ∧ kl ≠ 88) (hk : k + most ≤ connSlot)
    (hu : k + most ≤ 1160 ∧ 96 ≤ k ∨ 1176 ≤ k) (h : BytesW b ci kl k most bs s) : BytesW b ci kl k most bs s' :=
  ⟨numW_same hS hkl hul h.1, h.2.1, chunk_same hb hS (by have := h.2.1; omega) (by have := h.2.1; omega) h.2.2⟩

end Same

/-- **A record holds what it held** where the words it reads are alike. -/
theorem connAt_congr {b : Word} (hb : b.toNat % 8 = 0) {p : Posting} {ci : Nat} {c : Conn} {s s' : PancakeState σ}
    (h : ConnAt b p ci c s) (hS : SameRec b ci s s') : ConnAt b p ci c s' := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, -, o17, o18, o19⟩ := offs
  have hw : ∀ k, k < connSlot → k ≠ 1160 ∧ k ≠ 1168 ∧ k ≠ 88 → s'.memory (recW b ci k) = s.memory (recW b ci k) :=
    fun k hk hu => word_same hS hk hu
  have hW : ∀ k, k < connSlot → k ≠ 1160 ∧ k ≠ 1168 ∧ k ≠ 88 → ∀ x, NumW s (recW b ci k) x →
      NumW s' (recW b ci k) x := fun k hk hu x => numW_same hS hk hu
  refine ⟨(hw _ (by decide) (by decide)).trans h.live, hW _ (by decide) (by decide) _ h.gen,
    (hw _ (by decide) (by decide)).trans h.phase, ⟨?_, h.line.2⟩, ?_, ?_,
    (hw _ (by decide) (by decide)).trans h.reading, (hw _ (by decide) (by decide)).trans h.blocked,
    hW _ (by decide) (by decide) _ h.first, hW _ (by decide) (by decide) _ h.idle,
    hW _ (by decide) (by decide) _ h.lineDue, hW _ (by decide) (by decide) _ h.number,
    (hw _ (by decide) (by decide)).trans h.greeted, (hw _ (by omega) (by omega)).trans h.logins,
    (hw _ (by omega) (by omega)).trans h.tls, ⟨(hw _ (by omega) (by omega)).trans h.auth.1, ?_⟩,
    (hw _ (by decide) (by decide)).trans h.waiting, ⟨(hw _ (by decide) (by decide)).trans h.post.1, h.post.2⟩,
    hW _ (by decide) (by decide) _ h.articleDue, ?_, ⟨(hw _ (by decide) (by decide)).trans h.read.1, h.read.2⟩, ?_,
    by rw [hw _ (by decide) (by decide)]; exact h.group, ⟨hW _ (by decide) (by decide) _ h.current.1, h.current.2⟩,
    by rw [hw _ (by decide) (by decide), hw _ (by decide) (by decide), hw _ (by decide) (by decide),
      hw _ (by decide) (by decide), hw _ (by decide) (by decide)]; exact h.listing⟩
  · obtain ⟨h0, h8, h16, hk⟩ := h.line.1
    have hfit := h.line.2
    refine ⟨(hw cFramer (by omega) (by omega)).trans h0, ?_, ?_, fun j hj => ?_⟩
    · show s'.memory (recW b ci cFramer + BitVec.ofNat 64 8) = _
      rw [recW_add, hw _ (by omega) (by omega), ← recW_add]; exact h8
    · show s'.memory (recW b ci cFramer + BitVec.ofNat 64 16) = _
      rw [recW_add, hw _ (by omega) (by omega), ← recW_add]; exact h16
    · have hl : j < lineLimit := by have := hfit.1; have := hfit.2.1; omega
      show memLoadByte _ _ _ (recW b ci cFramer + BitVec.ofNat 64 40 + BitVec.ofNat 64 j) = _
      rw [recW_add, recW_add, byte_same hb hS (by omega) (by omega), ← recW_add, ← recW_add]; exact hk j hj
  · obtain ⟨pre, hq1, hq2, hq3, hq4⟩ := h.held
    refine ⟨pre, hW _ (by decide) (by decide) _ hq1, hW _ (by decide) (by decide) _ hq2, hq3, ?_⟩
    change Chunk s (recW b ci cHeld) (pre ++ c.held) at hq4
    exact chunk_same hb hS (by simp only [List.length_append]; omega) (by omega) hq4
  · refine ⟨hW _ (by decide) (by decide) _ h.out.1, h.out.2.1, fun i hi => ?_⟩
    have hl := h.out.2.1
    have hc := h.out.2.2 i hi
    change memLoadByte _ _ _ (recW b ci cOut + BitVec.ofNat 64 i) = _ at hc ⊢
    rw [recW_add] at hc ⊢; rw [byte_same hb hS (by omega) (by omega)]; exact hc
  · have ha := h.auth.2
    cases hc : c.auth <;> rw [hc] at ha
    · exact trivial
    · exact bytesW_same hb hS (by omega) (by omega) (by omega) (by omega) ha
    · exact ⟨bytesW_same hb hS (by omega) (by omega) (by omega) (by omega) ha.1,
        bytesW_same hb hS (by omega) (by omega) (by omega) (by omega) ha.2⟩
    · exact trivial
    · exact trivial
  · rw [hw _ (by decide) (by decide), hw _ (by decide) (by decide), hw _ (by decide) (by decide)]; exact h.want
  · have hv := h.view
    cases hc : c.view with
    | none => rw [hc] at hv; exact hv
    | some v =>
      rw [hc] at hv
      obtain ⟨h1, h2, k, n, id, h3, h4, gi, lo, upto, e1, e2, e3, h5⟩ := hv
      refine ⟨h1, (hw _ (by decide) (by decide)).trans h2, k, n, id, h3, ?_, gi, lo, upto,
        (hw _ (by decide) (by decide)).trans e1, (hw _ (by decide) (by decide)).trans e2,
        (hw _ (by decide) (by decide)).trans e3, h5⟩
      cases hf : v.field <;> rw [hf] at h4
      · exact h4
      · exact ⟨h4.1, bytesW_same hb hS (by omega) (by omega) (by omega) (by omega) h4.2⟩

/-- **Two records' words are apart.** -/
theorem recW_ne (b : Word) {ci cj k j : Nat} (hci : ci < SessionLayout.conns) (hcj : cj < SessionLayout.conns)
    (hk : k < connSlot) (hj : j < connSlot) (hne : ci ≠ cj) : recW b ci k ≠ recW b cj j := by
  obtain ⟨T, hT⟩ := SessionAppend.lay
  have hs := SessionAppend.nums.slot; have hc := SessionAppend.nums.count
  intro e
  simp only [recW, recordAt, DN.Compiler.Bytes.add_ofNat] at e
  have he := congrArg BitVec.toNat ((BitVec.add_right_inj b).1 e)
  simp only [BitVec.toNat_ofNat] at he
  rw [← SessionAppend.tOff_eq, hT.eq, hs] at he
  have := hT.room
  rw [hs] at hk hj; rw [hc] at hci hcj
  rw [Nat.mod_eq_of_lt (a := T + ci * 2712 + k) (by omega), Nat.mod_eq_of_lt (a := T + cj * 2712 + j) (by omega)]
    at he
  omega

/-- **A word stored outside record `ci`** keeps it. -/
theorem sameRec_store {b : Word} {ci : Nat} (s : PancakeState σ) {a : Word}
    (ha : ∀ k, k < connSlot → a ≠ recW b ci k) (v : Word) :
    SameRec b ci s { s with memory := fun x => if x = a then v else s.memory x } :=
  ⟨rfl, rfl, fun k hk _ => if_neg (Ne.symm (ha k hk))⟩

/-! ## The premises can hold -/

/-- A state of zeros, every word addressable. -/
def zeroState : PancakeState Unit := { bareState () with memory := fun _ => 0, memaddrs := fun _ => true }

theorem tableAt_witness : TableAt 0 (Posting.of 0 none) Table.empty (List.replicate SessionLayout.conns 0)
    zeroState where
  len := by simp [Table.empty, SessionLayout.conns, News.SessionSpec.conns]
  gensLen := by simp
  slot := fun ci hci => by
    have h1 : (List.replicate SessionLayout.conns 0).getD ci 0 = 0 := by simp [List.getD, hci]
    have h2 : Table.empty.getD ci none = none := by
      simp [Table.empty, List.getD, show ci < News.SessionSpec.conns from hci]
    rw [h1, h2]; exact ⟨⟨rfl, by decide⟩, rfl, rfl⟩
  dom := fun _ _ _ _ _ => rfl

theorem recW_inj {b : Word} {ci k j : Nat} (hk : k < 2 ^ 64) (hj : j < 2 ^ 64) (h : recW b ci k = recW b ci j) :
    k = j := by
  have := congrArg BitVec.toNat h
  simp only [recW, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := (recordAt b ci).isLt
  omega

/-- Memory whose only word set is record 0's flag of use, at base 0. -/
def oneMem (a : Word) : Word := if a = recW 0 0 cLive then 1 else 0

def oneState : PancakeState Unit := { zeroState with memory := oneMem }

theorem one_live : oneState.memory (recW 0 0 cLive) = 1 := by
  simp only [oneState, oneMem, if_true]

theorem one_at {k : Nat} (hk : k ≠ 0) (hk2 : k < 2 ^ 64) : oneState.memory (recW 0 0 k) = 0 := by
  simp only [oneState, oneMem]; exact if_neg fun e => hk (recW_inj hk2 (by decide) e)

/-- A connection of generation 0, all of its words zero. -/
def zeroConn : Conn :=
  { gen := 0, phase := .open_, line := .fresh, held := [], out := [], reading := false, blocked := false, first := 0,
    idle := 0, lineDue := 0 }

theorem connAt_witness : ConnAt 0 (Posting.of 0 none) 0 zeroConn oneState := by
  have z : ∀ k, k ≠ 0 → k < 2 ^ 64 → NumW oneState (recW 0 0 k) 0 := fun k hk hk2 => ⟨one_at hk hk2, by decide⟩
  have o : ∀ k, k ≠ 0 → k < 2 ^ 64 → oneState.memory (recW 0 0 k) = 0 := fun k hk hk2 => one_at hk hk2
  have h8 : oneState.memory (recW 0 0 cFramer + BitVec.ofNat 64 8) = 0 := by
    rw [recW_add]; exact o _ (by decide) (by decide)
  have h16 : oneState.memory (recW 0 0 cFramer + BitVec.ofNat 64 16) = 0 := by
    rw [recW_add]; exact o _ (by decide) (by decide)
  exact
    { live := one_live, gen := z _ (by decide) (by decide), phase := o _ (by decide) (by decide)
      line := ⟨⟨o _ (by decide) (by decide), h8, h16,
        fun j h => absurd h (by simp [zeroConn, News.Framer.LineState.fresh])⟩,
        by simp [Fits, zeroConn, News.Framer.LineState.fresh]⟩
      held := ⟨[], z _ (by decide) (by decide), z _ (by decide) (by decide), by decide,
        fun j h => absurd h (by simp [zeroConn])⟩
      out := ⟨z _ (by decide) (by decide), by decide, fun j h => absurd h (by simp [zeroConn])⟩
      reading := o _ (by decide) (by decide), blocked := o _ (by decide) (by decide)
      first := z _ (by decide) (by decide), idle := z _ (by decide) (by decide)
      lineDue := z _ (by decide) (by decide), number := z _ (by decide) (by decide)
      greeted := o _ (by decide) (by decide), logins := o _ (by decide) (by decide), tls := o _ (by decide) (by decide)
      auth := ⟨o _ (by decide) (by decide), trivial⟩, waiting := o _ (by decide) (by decide)
      post := ⟨o _ (by decide) (by decide), fun _ h => nomatch h⟩, articleDue := z _ (by decide) (by decide)
      want := o _ (by decide) (by decide), read := ⟨o _ (by decide) (by decide), fun _ h => nomatch h⟩
      view := (fun _ _ _ h => nomatch h), group := o _ (by decide) (by decide)
      current := ⟨z _ (by decide) (by decide), by decide⟩, listing := o _ (by decide) (by decide) }

theorem sameRec_witness : SameRec 0 0 zeroState zeroState := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem slotAt_witness : SlotAt 0 (Posting.of 0 none) 0 0 none zeroState := ⟨⟨rfl, by decide⟩, rfl, rfl⟩

/-- A store's view: one group, named empty, and the sample commit. -/
def onePosting : Posting := ⟨true, true, [[]], [News.Journal.sample], 0⟩

theorem groupIn_witness : GroupIn onePosting (BitVec.ofNat 64 1) (some []) := ⟨0, rfl, rfl⟩

theorem wantIn_witness : WantIn onePosting (BitVec.ofNat 64 4) 0 0 (some (.over, 0, News.Journal.sample.messageId)) :=
  ⟨rfl, by decide, rfl, by decide, 0, _, rfl, rfl, rfl⟩

theorem listIn_witness : ListIn onePosting 1 0 0 0 0 (some (.numbers [] 0 0)) :=
  ⟨rfl, ⟨0, rfl, rfl⟩, rfl, by decide, rfl, by decide, 0, rfl, by decide, rfl⟩

theorem authIn_witness : AuthIn 0 0 zeroState (.verify [] []) :=
  ⟨⟨⟨rfl, by decide⟩, Nat.zero_le _, fun _ h => absurd h (by simp)⟩,
    ⟨⟨rfl, by decide⟩, Nat.zero_le _, fun _ h => absurd h (by simp)⟩⟩

theorem viewIn_witness : ViewIn onePosting 0 0 zeroState (some (.over, 0, []))
    (some { legacy := false, field := none, byId := false, rest := [] }) :=
  ⟨rfl, rfl, .over, 0, [], rfl, rfl, 0, 0, 0, rfl, rfl, rfl, by decide, Nat.le_refl _, fun h => absurd h (by decide),
    by simp [restOf, numbered, onePosting, News.Journal.sample]⟩

theorem numW_witness : NumW zeroState 0 0 := ⟨rfl, by decide⟩

theorem bytesW_witness : BytesW 0 0 0 0 0 [] zeroState :=
  ⟨⟨rfl, by decide⟩, Nat.le_refl _, fun _ h => absurd h (by simp)⟩

end DN.Server.SessionState
