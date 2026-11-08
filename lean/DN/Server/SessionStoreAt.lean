-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionState
import DN.News.CrcCode
import DN.Server.SessionHash

/-!
# DN.Server.SessionStoreAt

The session's own words and store in the heap as `SessionSpec` and `PostSpec` have them: `StoreAt`, `ServerAt`. A
slot's article keeps the octets not written and the CRC-32C of those written. A read keeps its octets' count and
CRC-32C; `StoreOk` names the store's facts places rest on.
-/

namespace DN.Server.SessionStoreAt

open DN.Compiler DN.Server.SessionLayout DN.News.SessionSpec DN.Server.SessionState
open DN.News.PostSpec (Store Slot Read Article Task File ReadFile ReadTask)
open DN.News.FramerCode (Chunk bw)
open DN.News.FrameSpec (Byte)
open DN.News.Journal (Commit crcByte)

variable {σ : Type}

/-- Word `k` of the session's own words; of POST slot `k`, read `k`, recovery's area, the jobs' driver. -/
def ownW (b : Word) (k : Nat) : Word := b + BitVec.ofNat 64 (ownOff + k)
def slotW (b : Word) (k f : Nat) : Word := b + BitVec.ofNat 64 (slotsOff + k * slotLen + f)
def readW (b : Word) (k f : Nat) : Word := b + BitVec.ofNat 64 (readsOff + k * readLen + f)
def recA (b : Word) (x : Nat) : Word := b + BitVec.ofNat 64 (recOff + x)
def drvW (b : Word) (x : Nat) : Word := b + BitVec.ofNat 64 (drvOff + x)

/-- A word holding the number `x`, below `2 ^ 64`. -/
def WordN (s : PancakeState σ) (a : Word) (x : Nat) : Prop := s.memory a = BitVec.ofNat 64 x ∧ x < 2 ^ 64

/-- Word `x` of the article's area and cell `i` of the Message-ID index. -/
def artW (b : Word) (x : Nat) : Word := b + BitVec.ofNat 64 (artOff + x)
def cellW (b : Word) (i : Nat) : Word := b + BitVec.ofNat 64 (indexOff + 8 * i)

/-- A queue of connections by index and generation: its count, then two words each. -/
def QueueAt (b : Word) (kn kq : Nat) (q : List (Nat × Nat)) (s : PancakeState σ) : Prop :=
  NumW s (ownW b kn) q.length ∧ q.length ≤ SessionLayout.conns ∧
    ∀ i (h : i < q.length), NumW s (ownW b (kq + 16 * i)) q[i].1 ∧ NumW s (ownW b (kq + 16 * i + 8)) q[i].2

/-- An owner: none as zero, else one, with its index and generation. -/
def OwnerIn (wo wi wg : Word) : Option (Nat × Nat) → Prop
  | none => wo = 0
  | some (i, g) => wo = 1 ∧ wi = BitVec.ofNat 64 i ∧ wg = BitVec.ofNat 64 g ∧ i < SessionLayout.conns ∧ g < 2 ^ 63

/-- A POST's task and its two numbers, as the slot codes them. -/
def TaskIn (wt wa wb : Word) : Task → Prop
  | .create => wt = BitVec.ofNat 64 SessionStore.taskCreate
  | .write len => wt = BitVec.ofNat 64 SessionStore.taskWrite ∧ wa = BitVec.ofNat 64 len
  | .finish w len => wt = BitVec.ofNat 64 SessionStore.taskFinish ∧ wa = BitVec.ofNat 64 w ∧ wb = BitVec.ofNat 64 len
  | .place => wt = BitVec.ofNat 64 SessionStore.taskPlace
  | .commit _ len => wt = BitVec.ofNat 64 SessionStore.taskCommit ∧ wa = BitVec.ofNat 64 len
  | .clean closes => wt = BitVec.ofNat 64 SessionStore.taskClean ∧ wa = bw closes

/-- A job in flight: none as zero, else one, its job slot, generation, operations and task. -/
def BusyIn {α : Type} (task : α → Prop) (wb wj wg wo : Word) : Option (Nat × Nat × Nat × α) → Prop
  | none => wb = 0
  | some (j, g, ops, t) => wb = 1 ∧ wj = BitVec.ofNat 64 j ∧ j < jobs ∧ wg = BitVec.ofNat 64 g ∧ g < 2 ^ 63 ∧
    wo = BitVec.ofNat 64 ops ∧ ops ≤ jobOps ∧ task t

/-- An article's file, as the slot codes it, with its place and generation while open. -/
def FileIn (wf wp wg : Word) : File → Prop
  | .none => wf = BitVec.ofNat 64 SessionStore.fileNone
  | .open_ p g => wf = BitVec.ofNat 64 SessionStore.fileOpen ∧ wp = BitVec.ofNat 64 p ∧ wg = BitVec.ofNat 64 g ∧
    p < handles ∧ g < 2 ^ 64
  | .closed => wf = BitVec.ofNat 64 SessionStore.fileClosed
  | .final => wf = BitVec.ofNat 64 SessionStore.fileFinal
  | .placed => wf = BitVec.ofNat 64 SessionStore.filePlaced

/-- A POST's outcome: none as zero. -/
def outcomeCode : Option News.PostSpec.Outcome → Nat
  | none => 0
  | some .posted => SessionStore.outPosted
  | some .failed => SessionStore.outFailed
  | some .lost => SessionStore.outLost

/-- The CRC-32C so far of octets, before its last flip, as the program carries it. -/
def crcSoFar (bs : List Byte) : Word := News.CrcCode.w32 (bs.foldl crcByte 0xFFFFFFFF)

/-- The octets a write or finish in flight takes past those written. -/
def inFlight : Option (Nat × Nat × Nat × Task) → Nat
  | some (_, _, _, .write len) => len
  | some (_, _, _, .finish _ len) => len
  | _ => 0

/-- An accepted article in slot `k`: its numbers, sizes, the CRC-32C of the octets written and its file. Also the
Message-ID, each group's place among `gs`, and the octets not yet written. -/
def ArticleIn (b : Word) (k : Nat) (gs : List (List Byte)) (s : PancakeState σ) (a : Article) : Prop :=
  WordN s (slotW b k zSeq) a.seq ∧ NumW s (slotW b k zHeadSize) a.headerSize ∧
    NumW s (slotW b k zSize) a.octets.size ∧ NumW s (slotW b k zWritten) a.written ∧
    NumW s (slotW b k zPend) a.pending ∧ a.written ≤ a.octets.size ∧ a.pending ≤ bufMax ∧
    FileIn (s.memory (slotW b k zFile)) (s.memory (slotW b k zPlace)) (s.memory (slotW b k zPGen)) a.file ∧
    NumW s (slotW b k zMsgLen) a.messageId.length ∧ a.messageId.length ≤ 250 ∧
    Chunk s (slotW b k zMsg) a.messageId ∧ NumW s (slotW b k zGroupN) a.groups.length ∧ a.groups.length ≤ 16 ∧
    (∀ i (h : i < a.groups.length), ∃ x, s.memory (slotW b k (zGroups + 8 * i)) = BitVec.ofNat 64 x ∧
      gs[x]? = some a.groups[i]) ∧
    Chunk s (slotW b k zBuf) (a.octets.toList.drop a.written)

/-- The commit a commit job in flight makes of slot `k`'s article `a`: its fields, its groups' numbers in `zNums`. -/
def CommitIn (b : Word) (k : Nat) (a : Article) (c : Commit) (s : PancakeState σ) : Prop :=
  c.seq = a.seq ∧ c.messageId = a.messageId ∧ c.headerSize = a.headerSize ∧ c.fileSize = a.octets.size ∧
    c.fileCrc = (News.Journal.crc32c a.octets.toList).toNat ∧ c.groups.map (·.name) = a.groups ∧
    ∀ i (h : i < c.groups.length), NumW s (slotW b k (zNums + 8 * i)) c.groups[i].number

/-- **POST slot `k` holds a slot**: owner and its number, framer's phase and verdict, octets arrived, flags, outcome.
Also its job, the header section until the article is accepted or refused, and the article. -/
def SlotIn (b : Word) (k : Nat) (gs : List (List Byte)) (s : PancakeState σ) : Option Slot → Prop
  | none => s.memory (slotW b k zLive) = 0
  | some z => s.memory (slotW b k zLive) = 1 ∧
    OwnerIn (s.memory (slotW b k zOwner)) (s.memory (slotW b k zOwnIdx)) (s.memory (slotW b k zOwnGen)) z.owner ∧
    NumW s (slotW b k zConn) z.conn ∧
    s.memory (slotW b k zPh) = BitVec.ofNat 64 (News.FramerProg.phaseCode z.frame.phase) ∧
    s.memory (slotW b k zBad) = bw z.frame.bad ∧ NumW s (slotW b k zArrived) z.arrived ∧
    s.memory (slotW b k zEnded) = bw z.ended ∧ s.memory (slotW b k zBody) = bw z.body ∧
    s.memory (slotW b k zBol) = bw z.bol ∧ s.memory (slotW b k zRefused) = bw z.refused ∧
    s.memory (slotW b k zOutcome) = BitVec.ofNat 64 (outcomeCode z.outcome) ∧
    BusyIn (fun t => TaskIn (s.memory (slotW b k zTask)) (s.memory (slotW b k zTaskA)) (s.memory (slotW b k zTaskB)) t)
      (s.memory (slotW b k zBusy)) (s.memory (slotW b k zJob)) (s.memory (slotW b k zJGen))
      (s.memory (slotW b k zJOps)) z.busy ∧
    s.memory (slotW b k zHas) = bw z.article.isSome ∧
    (z.body = false → z.refused = false → NumW s (slotW b k zPend) z.header.size ∧
      z.header.size ≤ SessionStore.headerMax + 2 ∧ Chunk s (slotW b k zBuf) z.header.toList) ∧
    ∀ a, z.article = some a → ArticleIn b k gs s a ∧
      (z.refused = false → s.memory (slotW b k zCrc) = crcSoFar (a.octets.toList.take (a.written + inFlight z.busy))) ∧
      ∀ j g ops c len, z.busy = some (j, g, ops, .commit c len) → CommitIn b k a c s

/-- A read's file, as the read codes it, with its place and generation while open. -/
def ReadFileIn (wf wp wg : Word) : ReadFile → Prop
  | .none => wf = BitVec.ofNat 64 SessionStore.readNone
  | .open_ p g => wf = BitVec.ofNat 64 SessionStore.readOpen ∧ wp = BitVec.ofNat 64 p ∧ wg = BitVec.ofNat 64 g ∧
    p < handles ∧ g < 2 ^ 64
  | .gone => wf = BitVec.ofNat 64 SessionStore.readGone

/-- A read's task and the octets it asks, as the read codes them. -/
def ReadTaskIn (wt wa : Word) : ReadTask → Prop
  | .open_ => wt = BitVec.ofNat 64 SessionStore.taskOpen
  | .read len last => wt = BitVec.ofNat 64 (if last then SessionStore.taskReadLast else SessionStore.taskRead) ∧
    wa = BitVec.ofNat 64 len
  | .close => wt = BitVec.ofNat 64 SessionStore.taskClose

/-- One octet of a file's check as a read carries it. The state: at a line's start, after a CR, after a leading dot.
None when the octet is refused. -/
def checkStep : Bool × Bool × Bool → Byte → Option (Bool × Bool × Bool)
  | (bol, cr, dt), x =>
    if cr then (if x = News.FrameSpec.LF then some (true, false, dt) else none)
    else if x = 0 ∨ x = News.FrameSpec.LF then none
    else if dt then (if x = News.FrameSpec.DOT then some (false, false, false) else none)
    else if x = News.FrameSpec.CR then some (bol, true, dt)
    else if bol ∧ x = News.FrameSpec.DOT then some (false, cr, true)
    else some (false, cr, dt)

/-- **Read `k` holds a read**: owner, command, commit's place among `held` and its copies, first line's number, file.
Also the octets read, those given, the failure, its job, the view's flags; unfailed, the check so far. -/
def ReadIn (b : Word) (k : Nat) (held : List Commit) (s : PancakeState σ) : Option Read → Prop
  | none => s.memory (readW b k rLive) = 0
  | some r => s.memory (readW b k rLive) = 1 ∧
    OwnerIn (s.memory (readW b k rOwner)) (s.memory (readW b k rOwnIdx)) (s.memory (readW b k rOwnGen)) r.owner ∧
    s.memory (readW b k rCmd) = BitVec.ofNat 64 (wantCode r.cmd) ∧ 0 < wantCode r.cmd ∧
    (∃ j, s.memory (readW b k rCi) = BitVec.ofNat 64 j ∧ held[j]? = some r.commit) ∧
    NumW s (readW b k rNumber) r.number ∧ r.number ≤ News.CommandSpec.numberMax ∧
    ReadFileIn (s.memory (readW b k rFile)) (s.memory (readW b k rPlace)) (s.memory (readW b k rPGen)) r.file ∧
    NumW s (readW b k rHead) r.commit.headerSize ∧ NumW s (readW b k rSize) r.commit.fileSize ∧
    NumW s (readW b k rCrcWant) r.commit.fileCrc ∧
    NumW s (readW b k rGot) r.got.size ∧ r.got.size ≤ r.commit.fileSize ∧
    NumW s (readW b k rGiven) r.given ∧ r.given ≤ r.out.size ∧ s.memory (readW b k rBad) = bw r.bad ∧
    (r.bad = false → s.memory (readW b k rAcc) = crcSoFar r.got.toList ∧
      ∃ bol cr dt, r.got.toList.foldlM checkStep (true, false, false) = some (bol, cr, dt) ∧
        s.memory (readW b k rBol) = bw bol ∧ s.memory (readW b k rCr) = bw cr ∧ s.memory (readW b k rDot) = bw dt) ∧
    BusyIn (fun t => ReadTaskIn (s.memory (readW b k rTask)) (s.memory (readW b k rAsked)) t)
      (s.memory (readW b k rBusy)) (s.memory (readW b k rJob)) (s.memory (readW b k rJGen))
      (s.memory (readW b k rJOps)) r.busy ∧
    match r.view with
    | none => s.memory (readW b k rView) = 0
    | some v => s.memory (readW b k rView) = BitVec.ofNat 64 (if v.field.isSome then 2 else 1) ∧
      s.memory (readW b k rLegacy) = bw v.legacy ∧ s.memory (readW b k rById) = bw v.byId ∧
      s.memory (readW b k rViewFirst) = bw v.first

/-- Commit `c` at place `i` of recovery's area: number, sizes, CRC-32C and Message-ID. Each group's word has its
place among `gs` in the high half, its article number in the low. Recovery's tag word is left out: commits the session
adds have none. -/
def CommitAt (b : Word) (gs : List (List Byte)) (i : Nat) (c : Commit) (s : PancakeState σ) : Prop :=
  let at' (x : Nat) : Word := recA b (News.RecoverProg.rSlots + i * News.RecoverProg.slotSize + x)
  s.memory (at' News.RecoverProg.slotSeq) = BitVec.ofNat 64 c.seq ∧
    s.memory (at' News.RecoverProg.slotSizes) =
      (BitVec.ofNat 64 c.headerSize <<< 32) ||| BitVec.ofNat 64 c.fileSize ∧
    s.memory (at' News.RecoverProg.slotMisc) = ((BitVec.ofNat 64 c.fileCrc <<< 16) |||
      (BitVec.ofNat 64 c.messageId.length <<< 8)) ||| BitVec.ofNat 64 c.groups.length ∧
    c.messageId.length ≤ 250 ∧ Chunk s (at' News.RecoverProg.slotId) c.messageId ∧
    c.groups.length ≤ News.ScanProg.groupsMax ∧
    ∀ g (h : g < c.groups.length), ∃ x, gs[x]? = some c.groups[g].name ∧
      s.memory (at' (News.RecoverProg.slotGroups + g * 8)) =
        (BitVec.ofNat 64 x <<< 32) ||| BitVec.ofNat 64 c.groups[g].number

/-- The Message-ID index: each cell zero or one more than a commit's place. Each commit lies on the probe from the
cell its Message-ID hashes to under the index's key. -/
def IndexAt (b : Word) (held : List Commit) (s : PancakeState σ) : Prop :=
  ∃ key : List Byte, key.length = indexKeyLen ∧ Chunk s (ownW b ownIndexKey) key ∧
    (∀ i, i < indexCells → ∃ j, j ≤ held.length ∧ s.memory (cellW b i) = BitVec.ofNat 64 j) ∧
    ∀ j (h : j < held.length), ∃ d, d < indexCells ∧
      s.memory (cellW b (((SessionHash.cellOf key held[j].messageId).toNat + d) % indexCells)) =
        BitVec.ofNat 64 (j + 1) ∧
      ∀ e, e < d → s.memory (cellW b (((SessionHash.cellOf key held[j].messageId).toNat + e) % indexCells)) ≠ 0

/-- The configuration's part of the article's context in its area: the identity, the random value, the run and the
groups. The sequence number, wall clock and connection are each request's. -/
def ContextAt (b : Word) (cfg : News.PostSpec.Config) (s : PancakeState σ) : Prop :=
  NumW s (artW b News.ArticleProg.xIdLen) cfg.identity.length ∧ cfg.identity.length ≤ identityMax ∧
    Chunk s (artW b News.ArticleProg.xId) cfg.identity ∧
    NumW s (artW b News.ArticleProg.xRandLen) cfg.random.length ∧ Chunk s (artW b News.ArticleProg.xRand) cfg.random ∧
    NumW s (artW b News.ArticleProg.xRun) cfg.run ∧ NumW s (artW b News.ArticleProg.xGroupsN) cfg.groups.length ∧
    ∀ g (h : g < cfg.groups.length),
      NumW s (artW b (News.ArticleProg.xGroups + g * News.ArticleProg.groupSize)) cfg.groups[g].length ∧
      Chunk s (artW b (News.ArticleProg.xGroups + g * News.ArticleProg.groupSize + 8)) cfg.groups[g]

/-- **The store holds `st`**: its words, the journal's key and place, groups, commits and high numbers in recovery's
area. Also the index, the context, the CRC-32C table, the queues, the slots and the reads. -/
structure StoreAt (b : Word) (st : Store) (s : PancakeState σ) : Prop where
  has : s.memory (ownW b ownStore) = 1
  accepting : s.memory (ownW b ownAccepting) = bw st.accepting
  next : WordN s (ownW b ownNext) st.next
  journalEnd : NumW s (ownW b ownJournalEnd) st.journalEnd
  aside : NumW s (ownW b ownAside) st.setAside.length
  journal : NumW s (drvW b dJnl) st.journal.1 ∧ WordN s (drvW b dJnlGen) st.journal.2
  jobGen : NumW s (drvW b dGen) st.jobGen
  key : st.key.length = News.Journal.keyLength ∧ Chunk s (ownW b ownKey) st.key
  groups : NumW s (recA b News.RecoverProg.rGroupCount) st.cfg.groups.length ∧
    st.cfg.groups.length ≤ News.RecoverProg.groupsMax ∧
    ∀ g (h : g < st.cfg.groups.length),
      NumW s (recA b (News.RecoverProg.rGroups + g * News.RecoverProg.rGroupSlot)) st.cfg.groups[g].length ∧
      st.cfg.groups[g].length ≤ News.RecoverProg.groupNameMax ∧
      Chunk s (recA b (News.RecoverProg.rGroups + g * News.RecoverProg.rGroupSlot + 8)) st.cfg.groups[g]
  commits : NumW s (recA b News.RecoverProg.rCommits) st.articles.length ∧ st.articles.length ≤ News.Recovery.capacity ∧
    ∀ i (h : i < st.articles.length), CommitAt b st.cfg.groups i st.articles[i] s
  high : ∀ x (h : x < st.cfg.groups.length),
    NumW s (recA b (News.RecoverProg.rHigh + x * 8)) (News.Recovery.highIn st.articles st.cfg.groups[x])
  index : IndexAt b st.articles s
  context : ContextAt b st.cfg s
  crc : News.CrcCode.TableAt s.memory s.memaddrs (ownW b ownCrc)
  waiters : QueueAt b ownWaitN ownWaits st.waiters s
  readers : QueueAt b ownReadN ownReaders st.readers s
  slots : st.slots.length = posts ∧ ∀ k, k < posts → SlotIn b k st.cfg.groups s (st.slots.getD k none)
  reads : st.reads.length = reads ∧ ∀ k, k < reads → ReadIn b k st.articles s (st.reads.getD k none)
  rules : st.rules = {}

/-- **The server holds `srv`** at the wall clock `wall`: table, clock, wall's seconds, connections opened. Also no
stop, the article's failed flag clear, every word addressable, and the store or none. -/
structure ServerAt (b : Word) (wall : Nat) (srv : Server) (s : PancakeState σ) : Prop where
  table : TableAt b (Posting.of wall srv.store) srv.table srv.gens s
  clock : NumW s (ownW b ownClock) srv.clock
  wallW : NumW s (ownW b ownWall) (wall / 1000)
  opened : NumW s (ownW b ownOpened) srv.opened
  stop : s.memory (ownW b ownStop) = 0
  broken : s.memory (artW b News.AbnfProg.aBroken) = 0
  dom : ∀ x, x < SessionLayout.size → x % 8 = 0 → s.memaddrs (b + BitVec.ofNat 64 x) = true
  store : match srv.store with
    | none => s.memory (ownW b ownStore) = 0
    | some st => StoreAt b st s

/-- **The store's facts places rest on**: commits well formed, rising in each group, their Message-IDs and the
groups' names apart. Slots' articles are well formed; those not refused have Message-IDs apart, held by no commit. -/
structure StoreOk (st : Store) : Prop where
  ok : ∀ c ∈ st.articles, c.ok = true
  rising : News.Recovery.Rising st.articles
  ids : (st.articles.map (·.messageId)).Nodup
  names : st.cfg.groups.Nodup
  pending : ∀ k1 k2 z1 z2 a1 a2, st.slots.getD k1 none = some z1 → st.slots.getD k2 none = some z2 →
    z1.article = some a1 → z2.article = some a2 → z1.refused = false → z2.refused = false →
    (k1 ≠ k2 → a1.messageId ≠ a2.messageId) ∧ a1.messageId ∉ st.articles.map (·.messageId)
  formed : ∀ k z a, st.slots.getD k none = some z → z.article = some a → 1 ≤ a.seq ∧ 1 ≤ a.messageId.length ∧
    a.messageId.length ≤ 250 ∧ 1 ≤ a.groups.length ∧ a.groups.length ≤ 16 ∧
    (∀ g ∈ a.groups, 1 ≤ g.length ∧ g.length ≤ 64) ∧ a.headerSize ≤ a.octets.size ∧ a.octets.size < 2 ^ 32

/-! ## The premises can hold -/

/-- The server `main` starts: no connection, no store. -/
theorem serverAt_witness : ServerAt 0 0 { gens := List.replicate SessionLayout.conns 0 } zeroState where
  table := tableAt_witness
  clock := ⟨rfl, by decide⟩
  wallW := ⟨rfl, by decide⟩
  opened := ⟨rfl, by decide⟩
  stop := rfl
  broken := rfl
  dom := fun _ _ _ => rfl
  store := rfl

/-! ## A store can hold -/

theorem z_add (x : Word) : (0 : Word) + x = x := by simp

theorem own_nums : ownOff = 1032568 ∧ ownStore = 304 ∧ ownCrc = 4128 ∧ ownTexts = 6408 := by decide

/-- The store's regions past the records, as numbers from `tOff`. -/
theorem regions : recOff = SessionAppend.tOff + 173568 ∧ drvOff = recOff + 1730792 ∧ slotsOff = drvOff + 16728 ∧
    indexOff = slotsOff + 560160 ∧ readsOff = indexOff + 65536 ∧ SessionLayout.size = readsOff + 584704 := by
  have h1 : News.RecoverProg.size = 1730792 := by decide +kernel
  have h2 : dPage + jobData + 256 = 16728 := by decide
  have h3 : posts * slotLen = 560160 := by decide
  have h4 : indexCells * 8 = 65536 := by decide
  have h5 : reads * readLen = 584704 := by decide
  refine ⟨by rw [SessionAppend.rec_off]; rfl, by simp only [drvOff, h1], ?_, ?_, ?_, ?_⟩
  · unfold slotsOff; generalize drvOff = D; omega
  · unfold indexOff; generalize slotsOff = S; omega
  · unfold readsOff; generalize indexOff = I; omega
  · unfold SessionLayout.size; generalize readsOff = R; omega

/-- The witness's memory: the store's flag, the CRC-32C table, zeros. -/
def wMem (a : Word) : Word :=
  if a = BitVec.ofNat 64 1032872 then 1
  else if (a - BitVec.ofNat 64 1036696).toNat < 2048 then News.CrcCode.tableMem (BitVec.ofNat 64 1036696) a
  else 0

def wState : PancakeState Unit := { zeroState with memory := wMem }

theorem w_zero {x : Nat} (hx : x < 2 ^ 40) (h1 : x ≠ 1032872) (h2 : x < 1036696 ∨ 1036696 + 2048 ≤ x) :
    wState.memory (BitVec.ofNat 64 x) = 0 := by
  show wMem _ = 0
  unfold wMem
  rw [if_neg fun e => h1 (by have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega), if_neg]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- A word past the records, within the heap, is zero. -/
theorem hi_zero {x : Nat} (h1 : SessionAppend.tOff ≤ x) (h2 : x < SessionLayout.size) :
    wState.memory (BitVec.ofNat 64 x) = 0 := by
  obtain ⟨T, hT⟩ := SessionAppend.lay
  have := hT.above; have := hT.room; have hn := own_nums
  have hs := SessionLayout.size_fits; have hh : heapBytes = 4194304 := by decide
  rw [hT.eq] at h1
  exact w_zero (by omega) (by omega) (.inr (by omega))

/-- One of the session's own words below the CRC-32C table, not the store's flag, is zero. -/
theorem own_zero {k : Nat} (hk : k ≠ ownStore) (hk2 : k < ownCrc) : wState.memory (ownW 0 k) = 0 := by
  have hn := own_nums
  rw [ownW, z_add]; exact w_zero (by omega) (by omega) (.inl (by omega))

theorem zero_bytes {a : Word} (h : wState.memory (byteAlign a) = 0) :
    memLoadByte wState.memory wState.memaddrs wState.be a = some 0 := by
  unfold memLoadByte; rw [h]; simp [wState, zeroState, getByte]

theorem own_chunk {k n : Nat} (hk : ownStore + 8 ≤ k) (hk2 : k + n ≤ ownCrc) :
    Chunk wState (ownW 0 k) (List.replicate n 0) := fun j hj => by
  have hn := own_nums
  rw [List.getElem_replicate]
  refine zero_bytes ?_
  rw [ownW, z_add, ← BitVec.ofNat_add, ← z_add (BitVec.ofNat 64 (ownOff + k + j)),
    DN.Compiler.Bytes.byteAlign_base (by decide), z_add]
  simp only [List.length_replicate] at hj
  exact w_zero (by omega) (by omega) (.inl (by omega))

/-- A store with no group and no article, accepting nothing. -/
def wStore : Store :=
  { cfg := ⟨[], [], [], 0⟩, key := List.replicate 16 0, articles := [], setAside := [], next := 0, journalEnd := 0,
    journal := (0, 0), accepting := false, jobGen := 0, slots := List.replicate posts none,
    reads := List.replicate reads none }

theorem storeAt_witness : StoreAt 0 wStore wState := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := regions
  have hn := own_nums
  have hd : dJnl = 24 ∧ dJnlGen = 32 ∧ dGen = 72 ∧ News.RecoverProg.rGroupCount = 632 ∧
    News.RecoverProg.rCommits = 384 ∧ zLive = 0 ∧ rLive = 0 ∧ indexCells = 8192 ∧ slotLen = 140040 ∧
    readLen = 73088 ∧ artOff = 64 := by decide
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := hd
  have hz : ∀ x, SessionAppend.tOff ≤ x → x < SessionLayout.size → wState.memory (0 + BitVec.ofNat 64 x) = 0 :=
    fun x h1 h2 => by rw [z_add]; exact hi_zero h1 h2
  have ha : ∀ x, x < 578000 → wState.memory (artW 0 x) = 0 := fun x hx => by
    rw [artW, z_add]; exact w_zero (by omega) (by omega) (.inl (by omega))
  have nz : ∀ k, k ≠ ownStore → k < ownCrc → NumW wState (ownW 0 k) 0 := fun k h1 h2 => ⟨own_zero h1 h2, by decide⟩
  refine
    { has := ?_, accepting := own_zero (by decide) (by decide), next := ⟨own_zero (by decide) (by decide), by decide⟩
      journalEnd := nz _ (by decide) (by decide), aside := nz _ (by decide) (by decide)
      journal := ⟨⟨hz _ (by omega) (by omega), by decide⟩, ⟨hz _ (by omega) (by omega), by decide⟩⟩
      jobGen := ⟨hz _ (by omega) (by omega), by decide⟩
      key := ⟨rfl, own_chunk (by decide) (by decide)⟩
      groups := ⟨⟨hz _ (by omega) (by omega), by decide⟩, by decide, fun _ h => absurd h (by simp [wStore])⟩
      commits := ⟨⟨hz _ (by omega) (by omega), by decide⟩, by decide, fun _ h => absurd h (by simp [wStore])⟩
      high := fun _ h => absurd h (by simp [wStore])
      index := ⟨List.replicate 16 0, rfl, own_chunk (by decide) (by decide), fun i hi => ⟨0, Nat.le_refl _, by
        rw [cellW]; exact hz _ (by omega) (by omega)⟩, fun _ h => absurd h (by simp [wStore])⟩
      context := ⟨⟨ha _ (by decide), by decide⟩, by decide, fun _ h => absurd h (by simp [wStore]),
        ⟨ha _ (by decide), by decide⟩, fun _ h => absurd h (by simp [wStore]), ⟨ha _ (by decide), by decide⟩,
        ⟨ha _ (by decide), by decide⟩, fun _ h => absurd h (by simp [wStore])⟩
      crc := fun j hj => ⟨rfl, ?_⟩
      waiters := ⟨nz _ (by decide) (by decide), by decide, fun _ h => absurd h (by simp [wStore])⟩
      readers := ⟨nz _ (by decide) (by decide), by decide, fun _ h => absurd h (by simp [wStore])⟩
      slots := ⟨by simp [wStore], fun k hk => by
        have : wStore.slots.getD k none = none := by simp [wStore, List.getD, hk]
        rw [this]; exact hz _ (by rw [d9]; omega) (by have : posts = 4 := rfl; rw [d9]; omega)⟩
      reads := ⟨by simp [wStore], fun k hk => by
        have : wStore.reads.getD k none = none := by simp [wStore, List.getD, hk]
        rw [this]; exact hz _ (by rw [d10]; omega) (by have : reads = 8 := rfl; rw [d10]; omega)⟩
      rules := rfl }
  · show wMem (0 + BitVec.ofNat 64 (ownOff + ownStore)) = 1
    rw [z_add, hn.1, hn.2.1]; unfold wMem; exact if_pos rfl
  · show wMem (0 + BitVec.ofNat 64 (ownOff + ownCrc) + BitVec.ofNat 64 (j * 8)) = _
    rw [z_add, hn.1, hn.2.2.1]
    unfold wMem
    have e : BitVec.ofNat 64 (1032568 + 4128) + BitVec.ofNat 64 (j * 8) - BitVec.ofNat 64 1036696 =
        BitVec.ofNat 64 (j * 8) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [if_neg fun e => by
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this; omega,
      if_pos (by rw [e, BitVec.toNat_ofNat]; omega)]
    simp only [News.CrcCode.tableMem, e, BitVec.toNat_ofNat]
    congr 3; omega

theorem wStore_slot (k : Nat) : wStore.slots.getD k none = none := by
  simp only [wStore, List.getD, List.getElem?_replicate]; split <;> rfl

theorem storeOk_witness : StoreOk wStore :=
  ⟨fun _ h => absurd h (by simp [wStore]), fun _ _ h => by simp [wStore] at h, List.nodup_nil, List.nodup_nil,
    fun k1 _ _ _ _ _ h => (by rw [wStore_slot] at h; cases h), fun k _ _ h => (by rw [wStore_slot] at h; cases h)⟩

end DN.Server.SessionStoreAt
