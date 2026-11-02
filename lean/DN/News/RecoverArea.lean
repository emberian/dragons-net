-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverDrive
import DN.News.RecoverProg
import DN.News.ScanStop

/-!
# DN.News.RecoverArea

What recovery's area holds as a state of `DN.News.RecoverSpec` (`RAt`), what a step leaves in it for its caller
(`OutR`), and what a phase of `RecoverProg.stepWith` is shown to do (`PIn`, `POut`): from a state whose area holds
`r`, it leaves the area holding what `RecoverSpec.phase` gives and, when that asks or gives, the status for it.
-/

namespace DN.News.RecoverArea

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News.Journal DN.News.Recovery DN.News.RecoverProg
open DN.News.RecoverSpec (RSt ROut Act)
open DN.News.ScanRun (St AreaAt Kept at_ at_ne at_add align_at kept_has kept_set kept_word areaAt_keep kept_widen
  without vals_set kept_false_eq)
open DN.News.FramerCode (bw)

variable {σ : Type}

/-- The area's numbers. -/
theorem nums : rStatus = 0 ∧ rPhase = 8 ∧ rI = 16 ∧ rWait = 24 ∧ rFirst = 32 ∧ rEnd = 40 ∧ rNameLen = 48 ∧
    rName = 56 ∧ nameMax = 256 ∧ rSeq = 312 ∧ rFound = 320 ∧ rFileSize = 328 ∧ rJournalSize = 336 ∧
    rNames = 344 ∧ rJournal = 352 ∧ rMaxSeq = 360 ∧ rTails = 368 ∧ rMaxTail = 376 ∧ rCommits = 384 ∧
    rRecords = 392 ∧ rUnknown = 400 ∧ rUnknownLen = 408 ∧ rUnknownName = 416 ∧ rTorn = 480 ∧ rCut = 488 ∧
    rFresh = 496 ∧ rNext0 = 504 ∧ rNext = 512 ∧ rJournalEnd = 520 ∧ rTidied = 528 ∧ rAct = 536 ∧ rActA = 544 ∧
    rActB = 552 ∧ rActAt = 560 ∧ rActLen = 568 ∧ rFault = 576 ∧ rFaultA = 584 ∧ rFaultB = 592 ∧
    rFaultAt = 600 ∧ rFaultLen = 608 ∧ rKey = 616 ∧ rGroupCount = 632 ∧ rGroups = 640 ∧ groupsMax = 64 ∧
    groupNameMax = 64 ∧ rGroupSlot = 72 ∧ rHigh = 5248 ∧ rScan = 5760 ∧ rSlots = 26856 ∧ slotSize = 416 ∧
    slotSeq = 0 ∧ slotSizes = 8 ∧ slotMisc = 16 ∧ slotGroups = 24 ∧ slotTag = 152 ∧ slotId = 160 ∧
    RecoverProg.size = 1730792 ∧ capacity = 4096 ∧ ScanProg.size = 21096 ∧ keyLength = 16 ∧ ScanProg.groupsMax = 16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The area as a state -/

/-- The area's words. -/
def RAreaW (A : Word) (a : Word) : Prop := ∃ x, x < RecoverProg.size ∧ a = at_ A x

/-- The area addressable. -/
def RDom (A : Word) (dm : Word → Bool) : Prop := ∀ x, x < RecoverProg.size → dm (byteAlign (at_ A x)) = true

/-- The state's numbers and flags a word each, and the configuration's count of groups. -/
def scalarList (cfg : Config) (r : RSt) : List (Nat × Word) :=
  [(rPhase, .ofNat 64 r.phase), (rI, .ofNat 64 r.i), (rWait, bw r.wait), (rFirst, bw r.first),
   (rEnd, bw r.ended), (rNameLen, .ofNat 64 r.name.length), (rFound, bw r.found),
   (rFileSize, .ofNat 64 r.fileSize), (rJournalSize, .ofNat 64 r.jsize), (rNames, .ofNat 64 r.names),
   (rJournal, bw r.journal), (rMaxSeq, .ofNat 64 r.maxSeq), (rTails, bw r.tails), (rMaxTail, .ofNat 64 r.maxTail),
   (rCommits, .ofNat 64 r.commits.length), (rRecords, .ofNat 64 r.records), (rUnknown, bw r.unknown.isSome),
   (rTorn, bw r.torn), (rCut, .ofNat 64 r.cut), (rFresh, bw r.fresh), (rNext0, .ofNat 64 r.next0),
   (rNext, .ofNat 64 r.next), (rJournalEnd, .ofNat 64 r.journalEnd), (rTidied, .ofNat 64 r.tidied),
   (rGroupCount, .ofNat 64 cfg.groups.length)]

/-- The offsets of `scalars`. -/
def scalarOffs : List Nat :=
  [rPhase, rI, rWait, rFirst, rEnd, rNameLen, rFound, rFileSize, rJournalSize, rNames, rJournal, rMaxSeq, rTails,
   rMaxTail, rCommits, rRecords, rUnknown, rTorn, rCut, rFresh, rNext0, rNext, rJournalEnd, rTidied, rGroupCount]

/-- The offsets of the words a step gives its caller in. -/
def outOffs : List Nat :=
  [rStatus, rAct, rActA, rActB, rActAt, rActLen, rFault, rFaultA, rFaultB, rFaultAt, rFaultLen]

/-- The word of `scalarList` at `x`. -/
def scalars (cfg : Config) (r : RSt) (x : Nat) : Word := ((scalarList cfg r).lookup x).getD 0

/-- The words at `scalarOffs` of the area as `f` gives them. -/
def Words (A : Word) (f : Nat → Word) (u : PancakeState σ) : Prop := ∀ x ∈ scalarOffs, u.memory (at_ A x) = f x

/-- `f` with the word at `x` now `v`. -/
def upd (f : Nat → Word) (x : Nat) (v : Word) : Nat → Word := fun y => if y = x then v else f y

/-- Words at offsets of the area, listed. -/
def Outs (A : Word) (os : List (Nat × Word)) (u : PancakeState σ) : Prop := ∀ q ∈ os, u.memory (at_ A q.1) = q.2

/-- What holds at each of `scalarOffs`, from what holds at each, shown by `and_intros`. -/
theorem offs_all {p : Nat → Prop} (h : p rPhase ∧ p rI ∧ p rWait ∧ p rFirst ∧ p rEnd ∧ p rNameLen ∧ p rFound ∧
    p rFileSize ∧ p rJournalSize ∧ p rNames ∧ p rJournal ∧ p rMaxSeq ∧ p rTails ∧ p rMaxTail ∧ p rCommits ∧
    p rRecords ∧ p rUnknown ∧ p rTorn ∧ p rCut ∧ p rFresh ∧ p rNext0 ∧ p rNext ∧ p rJournalEnd ∧ p rTidied ∧
    p rGroupCount) : ∀ x ∈ scalarOffs, p x := by
  intro x hx
  simp only [scalarOffs, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25⟩ := h
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Octets `bs` at offset `x` of the area. -/
def BytesAt (A : Word) (x : Nat) (bs : Bytes) (u : PancakeState σ) : Prop :=
  ∀ i (h : i < bs.length), memLoadByte u.memory u.memaddrs u.be (at_ A (x + i)) = some bs[i]

/-- The configuration: its key, and each group's length and name in its slot, at most `groupsMax` groups of at
most `groupNameMax` octets. -/
structure CfgAt (A : Word) (cfg : Config) (u : PancakeState σ) : Prop where
  key : BytesAt A rKey cfg.key u
  keyLen : cfg.key.length = keyLength
  count : cfg.groups.length ≤ groupsMax
  len : ∀ g (h : g < cfg.groups.length), u.memory (at_ A (rGroups + g * rGroupSlot)) = .ofNat 64 cfg.groups[g].length
  short : ∀ g (h : g < cfg.groups.length), cfg.groups[g].length ≤ groupNameMax
  name : ∀ g (h : g < cfg.groups.length), BytesAt A (rGroups + g * rGroupSlot + 8) cfg.groups[g] u

/-- Where the configuration has the group `name`: the last of its first `groupsMax` with it, else `groupsMax`. -/
def groupIx (cfg : Config) (name : Bytes) : Nat :=
  (List.range (min cfg.groups.length groupsMax)).foldl (fun x c => if cfg.groups.getD c [] = name then c else x)
    groupsMax

/-- Where slot `i` starts. -/
def slotAt (i : Nat) : Nat := rSlots + i * slotSize

theorem slotAt_le {i : Nat} (h : i < capacity) : rSlots ≤ slotAt i ∧ slotAt i + slotSize ≤ RecoverProg.size := by
  have hn := nums
  simp only [slotAt, show slotSize = 416 from rfl]
  omega

/-- Commit `c` in slot `i`: its number, its sizes, its CRC, its Message-ID's length and its count of groups, the
Message-ID's tag under the configuration's key, the Message-ID, and each group's place in the configuration and its
article number. -/
structure SlotR (A : Word) (cfg : Config) (i : Nat) (c : Commit) (u : PancakeState σ) : Prop where
  seq : u.memory (at_ A (slotAt i + slotSeq)) = .ofNat 64 c.seq
  sizes : u.memory (at_ A (slotAt i + slotSizes)) = (BitVec.ofNat 64 c.headerSize <<< 32) ||| .ofNat 64 c.fileSize
  misc : u.memory (at_ A (slotAt i + slotMisc)) = ((BitVec.ofNat 64 c.fileCrc <<< 16) |||
    (BitVec.ofNat 64 c.messageId.length <<< 8)) ||| .ofNat 64 c.groups.length
  tag : u.memory (at_ A (slotAt i + slotTag)) = (SipHash.tag cfg.key c.messageId).toBitVec
  idLen : c.messageId.length ≤ 250
  id : BytesAt A (slotAt i + slotId) c.messageId u
  count : c.groups.length ≤ ScanProg.groupsMax
  groups : ∀ g (h : g < c.groups.length), u.memory (at_ A (slotAt i + slotGroups + g * 8)) =
    (BitVec.ofNat 64 (groupIx cfg c.groups[g].name) <<< 32) ||| .ofNat 64 c.groups[g].number

/-- The highest article number commits `cs` gave the group at `x` in the configuration: the last's. -/
def highOf (cfg : Config) (cs : List Commit) (x : Nat) : Nat :=
  cs.foldl (fun h c => match c.groups.find? (fun g => groupIx cfg g.name = x) with
    | some g => g.number
    | none => h) 0

/-- Each group's highest article number. -/
def HighAt (A : Word) (cfg : Config) (cs : List Commit) (u : PancakeState σ) : Prop :=
  ∀ x, x < groupsMax → u.memory (at_ A (rHigh + x * 8)) = .ofNat 64 (highOf cfg cs x)

/-- What the area holds besides `scalars`: the number asked about while it is read, the name, the first group the
configuration lacks, the configuration, the scanner's state, kept in its window, once it reads the journal, the
commits in their slots, and once the rules hold, each group's highest article number. -/
structure Rest (A : Word) (cfg : Config) (J : Bytes) (r : RSt) (u : PancakeState σ) : Prop where
  seq : r.phase = 9 ∨ r.phase = 12 → u.memory (at_ A rSeq) = .ofNat 64 r.seq
  nameLen : r.name.length ≤ nameMax
  name : BytesAt A rName r.name u
  unknown : ∀ g, r.unknown = some g → u.memory (at_ A rUnknownLen) = .ofNat 64 g.length ∧
    g.length ≤ groupNameMax ∧ BytesAt A rUnknownName g u
  config : CfgAt A cfg u
  scan : 3 ≤ r.phase → r.fresh = false → AreaAt (at_ A rScan) J r.scan u ∧ ScanRun.Valid J r.scan
  slots : ∀ i (h : i < r.commits.length), i < capacity → SlotR A cfg i r.commits[i] u
  high : 5 ≤ r.phase → HighAt A cfg (if r.fresh then [] else r.commits) u

/-- **The area at `A` holds `r`**, for the configuration `cfg` and the journal `J`. -/
structure RAt (A : Word) (cfg : Config) (J : Bytes) (r : RSt) (u : PancakeState σ) : Prop where
  words : Words A (scalars cfg r) u
  rest : Rest A cfg J r u

/-! ## What a step gives its caller -/

/-- Octets `bs` somewhere in the area, the words at `at` and `len` saying where. -/
def OctetsAt (A : Word) (at' len : Nat) (bs : Bytes) (u : PancakeState σ) : Prop :=
  ∃ x, u.memory (at_ A at') = .ofNat 64 x ∧ u.memory (at_ A len) = .ofNat 64 bs.length ∧
    x + bs.length ≤ RecoverProg.size ∧ BytesAt A x bs u

/-- What the step gives with why the store does not start. -/
def FaultData (A : Word) (r : RSt) : Fault → PancakeState σ → Prop
  | .badName n, _ => n = r.name
  | .journal p w, u => u.memory (at_ A rFaultA) = .ofNat 64 p ∧ u.memory (at_ A rFaultB) = .ofNat 64
      (ScanProg.whyCode w)
  | .seqTwice s, u | .missingFile s, u | .wrongSize s, u | .tooMany s, u => u.memory (at_ A rFaultA) = .ofNat 64 s
  | .numberNotAbove g n, u => u.memory (at_ A rFaultA) = .ofNat 64 n ∧ OctetsAt A rFaultAt rFaultLen g u
  | .unknownGroup g, u | .idTwice g, u => OctetsAt A rFaultAt rFaultLen g u
  | .noJournal, _ | .exhausted, _ | .badKey, _ => True

/-- Why the store does not start, as the step gives it. -/
def FaultR (A : Word) (r : RSt) (f : Fault) (u : PancakeState σ) : Prop :=
  u.memory (at_ A rFault) = .ofNat 64 (faultCode f) ∧ FaultData A r f u

/-- An action, as the step gives it. -/
def ActR (A : Word) (J : Bytes) : Act → PancakeState σ → Prop
  | .keep s x, u => u.memory (at_ A rAct) = .ofNat 64 actKeep ∧ u.memory (at_ A rActA) = .ofNat 64 s ∧
      u.memory (at_ A rActB) = .ofNat 64 x ∧ OctetsAt A rActAt rActLen (J.drop x) u
  | .rename s, u => u.memory (at_ A rAct) = .ofNat 64 actRename ∧ u.memory (at_ A rActA) = .ofNat 64 s
  | .remove s t, u => u.memory (at_ A rAct) = .ofNat 64 actRemove ∧ u.memory (at_ A rActA) = .ofNat 64 s ∧
      u.memory (at_ A rActB) = .ofNat 64 (if t then nameTemp else nameFinal)
  | .syncDir, u => u.memory (at_ A rAct) = .ofNat 64 actSyncDir
  | .cut x, u => u.memory (at_ A rAct) = .ofNat 64 actCut ∧ u.memory (at_ A rActA) = .ofNat 64 x
  | .create, u => u.memory (at_ A rAct) = .ofNat 64 actCreate

/-- **What a step asks or gives**, the area holding `r`: the status, and with it what the caller needs. -/
def OutR (A : Word) (J : Bytes) (r : RSt) : ROut → PancakeState σ → Prop
  | .askName, u => u.memory (at_ A rStatus) = .ofNat 64 asksName
  | .askJournal, u => u.memory (at_ A rStatus) = .ofNat 64 asksJournal
  | .askOctets n, u => u.memory (at_ A rStatus) = .ofNat 64 asksOctets ∧
      u.memory (at_ A (rScan + ScanProg.sWant)) = .ofNat 64 n
  | .askFile s, u => u.memory (at_ A rStatus) = .ofNat 64 asksFile ∧ u.memory (at_ A rSeq) = .ofNat 64 s
  | .askAside s, u => u.memory (at_ A rStatus) = .ofNat 64 asksAside ∧ u.memory (at_ A rSeq) = .ofNat 64 s
  | .gives a, u => u.memory (at_ A rStatus) = .ofNat 64 gives ∧ ActR A J a u
  | .givesAside n, u => u.memory (at_ A rStatus) = .ofNat 64 givesAside ∧ u.memory (at_ A rActA) = .ofNat 64 n
  | .done, u => u.memory (at_ A rStatus) = .ofNat 64 done
  | .refused f, u => u.memory (at_ A rStatus) = .ofNat 64 refused ∧ FaultR A r f u

/-! ## Words stored -/

/-- The memory with the word `x` octets into the area now `v`. -/
def stW (u : PancakeState σ) (A : Word) (x : Nat) (v : Word) : PancakeState σ :=
  { u with memory := fun k => if k = at_ A x then v else u.memory k }

theorem at_at (A : Word) (x y : Nat) : at_ (at_ A x) y = at_ A (x + y) := at_add A x y

theorem at_aligned {A : Word} (hA : A.toNat % 8 = 0) {x : Nat} (hx : x % 8 = 0) : (at_ A x).toNat % 8 = 0 := by
  rw [at_, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := A.isLt
  omega

theorem stW_word {u : PancakeState σ} {A : Word} {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : y ≠ x)
    (v : Word) : (stW u A x v).memory (at_ A y) = u.memory (at_ A y) := by
  simp only [stW, if_neg (at_ne hy hx h)]

theorem stW_load {u : PancakeState σ} {A : Word} (hA : A.toNat % 8 = 0) {x z : Nat} (hx : x < 2 ^ 64)
    (hz : z < 2 ^ 63) (h : z / 8 * 8 ≠ x) (v : Word) :
    memLoadByte (stW u A x v).memory (stW u A x v).memaddrs (stW u A x v).be (at_ A z) =
      memLoadByte u.memory u.memaddrs u.be (at_ A z) :=
  load_word_ne (by rw [align_at hA]; exact at_ne (by omega) hx h)

theorem offs_lt : ∀ x ∈ scalarOffs, x < 2 ^ 64 := by decide

theorem words_store {A : Word} {f : Nat → Word} {u : PancakeState σ} (h : Words A f u) {x : Nat} (hx : x < 2 ^ 64)
    (v : Word) : Words A (upd f x v) (stW u A x v) := by
  intro y hy
  by_cases e : y = x
  · subst e; simp [stW, upd]
  · simp only [upd, if_neg e]
    rw [stW_word hx (offs_lt y hy) e]
    exact h y hy

theorem words_ext {A : Word} {f g : Nat → Word} {u : PancakeState σ} (h : Words A f u)
    (hfg : ∀ x ∈ scalarOffs, f x = g x) : Words A g u := fun x hx => by rw [← hfg x hx]; exact h x hx

/-- The word of `os` listed first for `x`, found by `List.lookup` (shown by `rfl`). -/
theorem outs_lookup {A : Word} {u : PancakeState σ} : ∀ {os : List (Nat × Word)}, Outs A os u → ∀ {x : Nat}
    {v : Word}, os.lookup x = some v → u.memory (at_ A x) = v
  | [], _, _, _, hx => by cases hx
  | (y, w) :: os, h, x, v, hx => by
    rw [List.lookup_cons] at hx
    by_cases e : x = y
    · subst e
      rw [beq_self_eq_true] at hx
      cases hx; exact h _ (List.mem_cons_self ..)
    · rw [beq_eq_false_iff_ne.mpr e] at hx
      exact outs_lookup (fun q hq => h q (List.mem_cons_of_mem _ hq)) hx

theorem bytesAt_stW {A : Word} (hA : A.toNat % 8 = 0) {z : Nat} {bs : Bytes} {u : PancakeState σ}
    (h : BytesAt A z bs u) {x : Nat} (hx : x < 2 ^ 64) (hz : z + bs.length < 2 ^ 63)
    (hout : ∀ i, i < bs.length → (z + i) / 8 * 8 ≠ x) (v : Word) : BytesAt A z bs (stW u A x v) := fun i hi => by
  rw [stW_load hA hx (by omega) (hout i hi)]; exact h i hi

/-- Offsets of words a store at which keeps `Rest`. -/
def Free (x : Nat) : Prop := x < rName ∨ (rSeq < x ∧ x < rUnknownLen) ∨ (rTorn ≤ x ∧ x < rKey) ∨ x = rGroupCount

theorem free_scalar : ∀ x ∈ scalarOffs, Free x ∧ x % 8 = 0 := by
  simp only [scalarOffs, List.mem_cons, List.not_mem_nil, or_false, Free]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Offsets of words a phase's state between stores lists: of what a step gives, and of the scanner's. -/
def Known (x : Nat) : Prop := x ∈ outOffs ∨ (rScan ≤ x ∧ x < rSlots)

theorem out_range : ∀ x ∈ outOffs, x = rStatus ∨ (rAct ≤ x ∧ x ≤ rFaultLen) := by decide

theorem known_range {x : Nat} (h : Known x) : (x = rStatus ∨ (rAct ≤ x ∧ x ≤ rFaultLen)) ∨ (rScan ≤ x ∧ x < rSlots) :=
  h.elim (fun h => .inl (out_range x h)) .inr

theorem free_out : ∀ x ∈ outOffs, Free x ∧ x % 8 = 0 := by
  simp only [outOffs, List.mem_cons, List.not_mem_nil, or_false, Free]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem areaAt_stW {A : Word} (hA : A.toNat % 8 = 0) {J : Bytes} {st : St} {u : PancakeState σ}
    (h : AreaAt (at_ A rScan) J st u) (hl : st.len ≤ ScanProg.windowMax) {x : Nat}
    (hx : x < rScan ∨ rScan + ScanProg.size ≤ x) (hx64 : x < 2 ^ 64) (v : Word) :
    AreaAt (at_ A rScan) J st (stW u A x v) := by
  have hn := nums
  refine areaAt_keep (at_aligned hA (by omega)) h hl rfl rfl fun y hy _ _ => ?_
  rw [at_, at_add]
  exact stW_word hx64 (by omega) (by omega) v

/-- Offsets of words `Rest` of `r` reads outside the scanner's area: the number asked about, the name, the first
group the configuration lacks, the configuration's key and groups, the highest article numbers once the rules hold,
and the commits' slots. -/
def Reads (r : RSt) (y : Nat) : Prop :=
  ((r.phase = 9 ∨ r.phase = 12) ∧ y = rSeq) ∨ (rName ≤ y ∧ y < rSeq) ∨
    (r.unknown.isSome ∧ rUnknownLen ≤ y ∧ y < rTorn) ∨ (rKey ≤ y ∧ y < rKey + 16) ∨ (rGroups ≤ y ∧ y < rHigh) ∨
    (5 ≤ r.phase ∧ rHigh ≤ y ∧ y < rScan) ∨ (rSlots ≤ y ∧ y < rSlots + min r.commits.length capacity * slotSize)

/-- Octets read alike where the words holding them are alike. -/
theorem bytesAt_frame {A : Word} (hA : A.toNat % 8 = 0) {x : Nat} {bs : Bytes} {u u' : PancakeState σ}
    (h : BytesAt A x bs u)
    (hm : ∀ i, i < bs.length → u'.memory (at_ A ((x + i) / 8 * 8)) = u.memory (at_ A ((x + i) / 8 * 8)))
    (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) : BytesAt A x bs u' := fun i hi => by
  have e : memLoadByte u'.memory u'.memaddrs u'.be (at_ A (x + i)) =
      memLoadByte u.memory u.memaddrs u.be (at_ A (x + i)) := by
    simp only [memLoadByte, align_at hA, hd, hb]; rw [hm i hi]
  rw [e]; exact h i hi

/-- **`Rest` framed**: what holds of `r` holds with the scanner at `st'` where the memory is alike at each word
`Rest` reads outside the scanner's area, and the scanner's area holds `st'` once it must. -/
theorem rest_frame {A : Word} (hA : A.toNat % 8 = 0) {cfg : Config} {J : Bytes} {r : RSt} {u u' : PancakeState σ}
    (h : Rest A cfg J r u) (hm : ∀ y, Reads r y → u'.memory (at_ A y) = u.memory (at_ A y))
    (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) {st' : St}
    (hscan : 3 ≤ r.phase → r.fresh = false → AreaAt (at_ A rScan) J st' u' ∧ ScanRun.Valid J st') :
    Rest A cfg J { r with scan := st' } u' := by
  have e1 : rName = 56 := rfl
  have e2 : rSeq = 312 := rfl
  have e3 : rUnknownLen = 408 := rfl
  have e4 : rUnknownName = 416 := rfl
  have e5 : rTorn = 480 := rfl
  have e6 : rKey = 616 := rfl
  have e7 : rGroups = 640 := rfl
  have e8 : rHigh = 5248 := rfl
  have e9 : rScan = 5760 := rfl
  have e10 : rSlots = 26856 := rfl
  have e12 : rGroupSlot = 72 := rfl
  have e13 : capacity = 4096 := rfl
  have hR : ∀ y, ((r.phase = 9 ∨ r.phase = 12) ∧ y = rSeq) ∨ (rName ≤ y ∧ y < rSeq) ∨
      (r.unknown.isSome ∧ rUnknownLen ≤ y ∧ y < rTorn) ∨ (rKey ≤ y ∧ y < rKey + 16) ∨ (rGroups ≤ y ∧ y < rHigh) ∨
      (5 ≤ r.phase ∧ rHigh ≤ y ∧ y < rScan) ∨ (rSlots ≤ y ∧ y < rSlots + min r.commits.length capacity * 416) →
      u'.memory (at_ A y) = u.memory (at_ A y) := hm
  refine ⟨fun hp => by rw [hR _ (.inl ⟨hp, rfl⟩)]; exact h.seq hp, h.nameLen, bytesAt_frame hA h.name
    (fun i hi => hR _ (.inr (.inl ⟨by omega, by
      dsimp only at hi; have := h.nameLen; simp only [nameMax] at this; omega⟩))) hd hb,
    fun g hg => ?_, ⟨bytesAt_frame hA h.config.key (fun i hi => hR _ (.inr (.inr (.inr (.inl ⟨by omega,
      by have := h.config.keyLen; simp only [keyLength] at this; omega⟩))))) hd hb, h.config.keyLen,
      h.config.count, fun g hg => ?_, h.config.short, fun g hg => ?_⟩, hscan, fun i hi hc => ?_,
    fun h5 y hy => ?_⟩
  · dsimp only at hg
    obtain ⟨f1, f2, f3⟩ := h.unknown g hg
    have hs : r.unknown.isSome := by rw [hg]; rfl
    refine ⟨by rw [hR _ (.inr (.inr (.inl ⟨hs, by omega, by omega⟩)))]; exact f1, f2, bytesAt_frame hA f3
      (fun i hi => hR _ (.inr (.inr (.inl ⟨hs, by omega, by simp only [groupNameMax] at f2; omega⟩)))) hd hb⟩
  · have := h.config.count
    have : g * rGroupSlot ≤ 63 * 72 := by
      rw [e12]; exact Nat.mul_le_mul (by simp only [groupsMax] at this; omega) (by omega)
    rw [hR _ (.inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))]; exact h.config.len g hg
  · have := h.config.count
    have h64 := h.config.short g hg
    simp only [groupNameMax] at h64
    have : g * rGroupSlot ≤ 63 * 72 := by
      rw [e12]; exact Nat.mul_le_mul (by simp only [groupsMax] at this; omega) (by omega)
    exact bytesAt_frame hA (h.config.name g hg) (fun i hi => hR _ (.inr (.inr (.inr (.inr (.inl
      ⟨by omega, by omega⟩)))))) hd hb
  · dsimp only at hi hc ⊢
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := h.slots i hi hc
    have hm' : i + 1 ≤ min r.commits.length capacity := by omega
    have hsl : slotAt i = 26856 + i * 416 := rfl
    have hs : ∀ off, off < 416 → u'.memory (at_ A (slotAt i + off)) = u.memory (at_ A (slotAt i + off)) :=
      fun off ho => hR _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩))))))
    refine ⟨by rw [hs _ (by decide)]; exact f1, by rw [hs _ (by decide)]; exact f2,
      by rw [hs _ (by decide)]; exact f3, by rw [hs _ (by decide)]; exact f4, f5,
      bytesAt_frame hA f6 (fun j hj => ?_) hd hb, f7, fun g hg => ?_⟩
    · have hid : slotId = 160 := rfl
      have := f5
      rw [show (slotAt i + slotId + j) / 8 * 8 = slotAt i + (160 + j) / 8 * 8 by omega]
      exact hs _ (by omega)
    · have := f7; simp only [ScanProg.groupsMax] at this
      have hgr : slotGroups = 24 := rfl
      rw [show slotAt i + slotGroups + g * 8 = slotAt i + (24 + g * 8) by omega, hs _ (by omega)]
      rw [show slotAt i + (24 + g * 8) = slotAt i + slotGroups + g * 8 by omega]; exact f8 g hg
  · dsimp only at h5 ⊢
    rw [hR _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨h5, by omega, by simp only [groupsMax] at hy; omega⟩))))))]
    exact h.high h5 y hy

/-- Offsets of words `Rest` of `r` does not read: of `Free`, of the highest article numbers before the rules hold, of
the scanner's before it reads, of the first group the configuration lacks while there is none, and of the slot after
the commits'. -/
def Away (r : RSt) (x : Nat) : Prop :=
  Free x ∨ (rHigh ≤ x ∧ x < rScan ∧ r.phase < 5) ∨ (rScan ≤ x ∧ x < rSlots ∧ r.phase < 3) ∨
    (rUnknownLen ≤ x ∧ x < rTorn ∧ r.unknown = none) ∨
    (slotAt r.commits.length ≤ x ∧ x < slotAt r.commits.length + slotSize ∧ r.commits.length < capacity)

/-- A word `Rest` does not read is none it reads, and below the area's end. -/
theorem away_reads {r : RSt} {x y : Nat} (hx : Away r x) (hy : Reads r y) : y ≠ x ∧ x < RecoverProg.size := by
  have e1 : rName = 56 := rfl
  have e2 : rSeq = 312 := rfl
  have e3 : rUnknownLen = 408 := rfl
  have e5 : rTorn = 480 := rfl
  have e6 : rKey = 616 := rfl
  have e7 : rGroups = 640 := rfl
  have e8 : rHigh = 5248 := rfl
  have e9 : rScan = 5760 := rfl
  have e10 : rSlots = 26856 := rfl
  have e11 : slotSize = 416 := rfl
  have e13 : capacity = 4096 := rfl
  have e14 : rGroupCount = 632 := rfl
  have e15 : RecoverProg.size = 1730792 := rfl
  simp only [Away, Free, slotAt, e11] at hx
  simp only [Reads, e11] at hy
  rcases hx with hx | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rcases hy with ⟨_, rfl⟩ | hy | ⟨_, hy⟩ | hy | hy | ⟨_, hy⟩ | hy <;> omega
  · rcases hy with ⟨_, rfl⟩ | hy | ⟨_, hy⟩ | hy | hy | ⟨_, _⟩ | hy <;> omega
  · rcases hy with ⟨_, rfl⟩ | hy | ⟨_, hy⟩ | hy | hy | ⟨_, _⟩ | hy <;> omega
  · rcases hy with ⟨_, rfl⟩ | hy | ⟨hs, hy⟩ | hy | hy | ⟨_, hy⟩ | hy
    all_goals first | omega | (rw [h3] at hs; cases hs)
  · have : r.commits.length * 416 ≤ 4095 * 416 := Nat.mul_le_mul_right _ (by omega)
    have hml : min r.commits.length capacity = r.commits.length := Nat.min_eq_left (by omega)
    rw [hml] at hy
    rcases hy with ⟨_, rfl⟩ | hy | ⟨_, hy⟩ | hy | hy | ⟨_, hy⟩ | hy <;> omega

/-- A word `Rest` reads lies in the area, outside the scanner's. -/
theorem reads_lt {r : RSt} {y : Nat} (hy : Reads r y) : y < RecoverProg.size ∧ (y < rScan ∨ rSlots ≤ y) := by
  have e2 : rSeq = 312 := rfl
  have e5 : rTorn = 480 := rfl
  have e6 : rKey = 616 := rfl
  have e8 : rHigh = 5248 := rfl
  have e9 : rScan = 5760 := rfl
  have e10 : rSlots = 26856 := rfl
  have e11 : slotSize = 416 := rfl
  have e13 : capacity = 4096 := rfl
  have e15 : RecoverProg.size = 1730792 := rfl
  have hmin := Nat.min_le_right r.commits.length capacity
  have : min r.commits.length capacity * 416 ≤ 4096 * 416 := Nat.mul_le_mul_right _ (by omega)
  simp only [Reads, e11] at hy
  omega

/-- A word `Rest` does not read lies outside the scanner's area once it reads the journal. -/
theorem away_scan {r : RSt} {x : Nat} (hx : Away r x) (h3 : 3 ≤ r.phase) : x < rScan ∨ rScan + ScanProg.size ≤ x := by
  have e1 : rName = 56 := rfl
  have e3 : rUnknownLen = 408 := rfl
  have e5 : rTorn = 480 := rfl
  have e6 : rKey = 616 := rfl
  have e9 : rScan = 5760 := rfl
  have e10 : rSlots = 26856 := rfl
  have e11 : slotSize = 416 := rfl
  have e13 : capacity = 4096 := rfl
  have e14 : rGroupCount = 632 := rfl
  have e15 : ScanProg.size = 21096 := rfl
  simp only [Away, Free, slotAt, e11] at hx
  omega

/-- **`Rest` kept** where a word it does not read is stored. -/
theorem rest_stW {A : Word} (hA : A.toNat % 8 = 0) {cfg : Config} {J : Bytes} {r : RSt} {u : PancakeState σ}
    (h : Rest A cfg J r u) {x : Nat} (hf : Away r x) (hx8 : x % 8 = 0) (v : Word) : Rest A cfg J r (stW u A x v) := by
  have e15 : RecoverProg.size = 1730792 := rfl
  have hx : x < 2 ^ 64 := by
    have := (away_reads hf (y := rName) (.inr (.inl ⟨Nat.le_refl _, by decide⟩))).2
    omega
  exact rest_frame (st' := r.scan) hA h (fun y hy => stW_word hx (by have := (reads_lt hy).1; omega)
    (away_reads hf hy).1 v) rfl rfl fun h3 hfr => ⟨areaAt_stW hA (h.scan h3 hfr).1 (h.scan h3 hfr).2.len
      (away_scan hf h3) hx v, (h.scan h3 hfr).2⟩

/-! ## A phase -/

/-- The step's locals but the scanner's address. -/
def stepLocals : List String := RecoverProg.locals.filter (· != "jsc")

/-- What every phase has: the area at `A`, addressable, its address in `rsc` and the scanner's in `jsc`, and each
local bound. -/
structure PBase (A : Word) (s : PancakeState σ) : Prop where
  hA : A.toNat % 8 = 0
  dom : RDom A s.memaddrs
  rsc : s.locals "rsc" = some A
  jsc : s.locals "jsc" = some (at_ A rScan)
  jz : s.locals "jz" = some 0
  bound : ∀ y ∈ RecoverProg.locals, ∃ v, s.locals y = some v

/-- **What a phase starts from**: the base, the step going on, the area holding `r`, and a journal shorter than
`2 ^ 62` octets. -/
structure PIn (A : Word) (cfg : Config) (J : Bytes) (r : RSt) (s : PancakeState σ) : Prop extends PBase A s where
  rgo : s.locals "rgo" = some 1
  area : RAt A cfg J r s
  short : J.length < 2 ^ 62

/-- **What a phase leaves**: the locals but the step's and the memory but the area as they were,
the area holding the state `p.1`, and the step going on, or stopped with what `p.2` asks or gives. -/
def POut (A : Word) (cfg : Config) (J : Bytes) (s0 : PancakeState σ) (p : RSt × Option ROut)
    (u : PancakeState σ) : Prop :=
  Kept stepLocals (RAreaW A) s0 u ∧ RAt A cfg J p.1 u ∧
    match p.2 with
    | none => u.locals "rgo" = some 1
    | some o => u.locals "rgo" = some 0 ∧ OutR A J p.1 o u

/-! ## Alike in memory -/

theorem bytesAt_congr {A : Word} {x : Nat} {bs : Bytes} {u u' : PancakeState σ} (h : BytesAt A x bs u)
    (hm : u'.memory = u.memory) (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) : BytesAt A x bs u' :=
  fun i hi => by rw [hm, hd, hb]; exact h i hi

theorem areaAt_congr {A : Word} {J : Bytes} {st : St} {u u' : PancakeState σ} (h : AreaAt A J st u)
    (hm : u'.memory = u.memory) (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) : AreaAt A J st u' :=
  ⟨by rw [hm]; exact h.size, by rw [hm]; exact h.base, by rw [hm]; exact h.len, by rw [hm]; exact h.pos,
    by rw [hm]; exact h.keyed, by rw [hm]; exact h.count, fun i hi => by rw [hm, hd, hb]; exact h.window i hi,
    fun k hk => by rw [hm, hd, hb]; exact h.key k hk⟩

theorem cfgAt_congr {A : Word} {cfg : Config} {u u' : PancakeState σ} (h : CfgAt A cfg u)
    (hm : u'.memory = u.memory) (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) : CfgAt A cfg u' :=
  ⟨bytesAt_congr h.key hm hd hb, h.keyLen, h.count, fun g hg => by rw [hm]; exact h.len g hg, h.short,
    fun g hg => bytesAt_congr (h.name g hg) hm hd hb⟩

theorem slotR_congr {A : Word} {cfg : Config} {i : Nat} {c : Commit} {u u' : PancakeState σ} (h : SlotR A cfg i c u)
    (hm : u'.memory = u.memory) (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) : SlotR A cfg i c u' :=
  ⟨by rw [hm]; exact h.seq, by rw [hm]; exact h.sizes, by rw [hm]; exact h.misc, by rw [hm]; exact h.tag, h.idLen,
    bytesAt_congr h.id hm hd hb, h.count, fun g hg => by rw [hm]; exact h.groups g hg⟩

theorem rest_congr {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {u u' : PancakeState σ} (h : Rest A cfg J r u)
    (hm : u'.memory = u.memory) (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) : Rest A cfg J r u' :=
  ⟨fun hp => by rw [hm]; exact h.seq hp, h.nameLen, bytesAt_congr h.name hm hd hb,
    fun g hg => by
      obtain ⟨e1, e2, e3⟩ := h.unknown g hg
      exact ⟨by rw [hm]; exact e1, e2, bytesAt_congr e3 hm hd hb⟩,
    ⟨bytesAt_congr h.config.key hm hd hb, h.config.keyLen, h.config.count,
      fun g hg => by rw [hm]; exact h.config.len g hg, h.config.short,
      fun g hg => bytesAt_congr (h.config.name g hg) hm hd hb⟩,
    fun h3 hf => ⟨areaAt_congr (h.scan h3 hf).1 hm hd hb, (h.scan h3 hf).2⟩,
    fun i hi hc => slotR_congr (h.slots i hi hc) hm hd hb, fun h5 x hx => by rw [hm]; exact h.high h5 x hx⟩

theorem rat_congr {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {u u' : PancakeState σ} (h : RAt A cfg J r u)
    (hm : u'.memory = u.memory) (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) : RAt A cfg J r u' :=
  ⟨fun q hq => by rw [hm]; exact h.words q hq, rest_congr h.rest hm hd hb⟩

theorem octetsAt_congr {A : Word} {at' len : Nat} {bs : Bytes} {u u' : PancakeState σ} (h : OctetsAt A at' len bs u)
    (hm : u'.memory = u.memory) (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) : OctetsAt A at' len bs u' :=
  let ⟨x, h1, h2, h3, h4⟩ := h
  ⟨x, by rw [hm]; exact h1, by rw [hm]; exact h2, h3, bytesAt_congr h4 hm hd hb⟩

theorem outR_congr {A : Word} {J : Bytes} {r : RSt} {o : ROut} {u u' : PancakeState σ} (h : OutR A J r o u)
    (hm : u'.memory = u.memory) (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) : OutR A J r o u' := by
  cases o with
  | askName | askJournal | done => simp only [OutR, hm] at h ⊢; exact h
  | askOctets n | askFile n | askAside n | givesAside n =>
    simp only [OutR, hm] at h ⊢; exact h
  | gives a =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨by rw [hm]; exact h1, ?_⟩
    cases a with
    | keep s x =>
      obtain ⟨e1, e2, e3, e4⟩ := h2
      exact ⟨by rw [hm]; exact e1, by rw [hm]; exact e2, by rw [hm]; exact e3, octetsAt_congr e4 hm hd hb⟩
    | rename s | cut s =>
      obtain ⟨e1, e2⟩ := h2; exact ⟨by rw [hm]; exact e1, by rw [hm]; exact e2⟩
    | remove s tmp =>
      obtain ⟨e1, e2, e3⟩ := h2; exact ⟨by rw [hm]; exact e1, by rw [hm]; exact e2, by rw [hm]; exact e3⟩
    | syncDir | create => simp only [ActR, hm] at h2 ⊢; exact h2
  | refused f =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by rw [hm]; exact h1, by rw [hm]; exact h2, ?_⟩
    cases f with
    | badName n => exact h3
    | journal p w => obtain ⟨e1, e2⟩ := h3; exact ⟨by rw [hm]; exact e1, by rw [hm]; exact e2⟩
    | seqTwice s | missingFile s | wrongSize s | tooMany s => simp only [FaultData, hm] at h3 ⊢; exact h3
    | numberNotAbove g n => obtain ⟨e1, e2⟩ := h3; exact ⟨by rw [hm]; exact e1, octetsAt_congr e2 hm hd hb⟩
    | unknownGroup g | idTwice g => exact octetsAt_congr h3 hm hd hb
    | noJournal | exhausted | badKey => trivial

theorem pout_clock {A : Word} {cfg : Config} {J : Bytes} {s0 : PancakeState σ} {p : RSt × Option ROut} :
    Safe.ClockFree (POut A cfg J s0 p) := fun s k ⟨h1, h2, h3⟩ => by
  refine ⟨{ h1 with }, rat_congr h2 rfl rfl rfl, ?_⟩
  revert h3
  cases p.2 with
  | none => exact id
  | some o => exact fun ⟨e1, e2⟩ => ⟨e1, outR_congr e2 rfl rfl rfl⟩

/-! ## A phase's stores -/

/-- **A phase's state between stores**: the locals but the step's and the memory but the area as in `s0`, the
words `ws` in place of `scalars` and `os` of what a step gives, `Rest` of `r`, and the locals `l`. -/
structure Mid (A : Word) (cfg : Config) (J : Bytes) (r : RSt) (s0 : PancakeState σ) (ws : Nat → Word)
    (os : List (Nat × Word)) (l : List (String × Value)) (u : PancakeState σ) : Prop where
  kept : Kept stepLocals (RAreaW A) s0 u
  words : Words A ws u
  outs : Outs A os u
  outIn : ∀ q ∈ os, Known q.1
  rest : Rest A cfg J r u
  vals : ScanRun.Vals u l

theorem mid_clock {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} : Safe.ClockFree (Mid A cfg J r s0 ws os l) := fun _ _ h =>
  ⟨{ h.kept with }, h.words, h.outs, h.outIn, rest_congr h.rest rfl rfl rfl, h.vals⟩

theorem apart : ∀ x ∈ scalarOffs, x ∉ outOffs := by decide

theorem rsc_kept {A : Word} {s0 u : PancakeState σ} (h : PBase A s0)
    {w : Word → Prop} (hk : Kept stepLocals w s0 u) : u.locals "rsc" = some A := by
  rw [hk.locals _ (by decide)]; exact h.rsc

theorem jz_kept {A : Word} {s0 u : PancakeState σ} (h : PBase A s0)
    {w : Word → Prop} (hk : Kept stepLocals w s0 u) : u.locals "jz" = some 0 := by
  rw [hk.locals _ (by decide)]; exact h.jz

theorem jsc_kept {A : Word} {s0 u : PancakeState σ} (h : PBase A s0)
    {w : Word → Prop} (hk : Kept stepLocals w s0 u) : u.locals "jsc" = some (at_ A rScan) := by
  rw [hk.locals _ (by decide)]; exact h.jsc

/-- **A word of the area stored**. -/
theorem rset_frag (o : Oracle σ) {A : Word} (hA : A.toNat % 8 = 0) {x : Nat} (hx : x % 8 = 0)
    (hxs : x < RecoverProg.size) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {P P' : Assn σ}
    (hP' : Safe.ClockFree P')
    (h : ∀ u, P u → u.locals "rsc" = some A ∧ RDom A u.memaddrs ∧ ∃ val, eval u E = some val ∧ P' (stW u A x val)) :
    Frag o [rset x e] P P' :=
  ScanRun.store_at_frag o hA hx hxs he hP' h

/-- A word of `scalars` stored, what else holds kept. -/
theorem mid_set_and (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {x : Nat}
    (hx : x ∈ scalarOffs) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {val : Word}
    {F : Assn σ} (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u → eval u E = some val) (hFc : Safe.ClockFree F)
    (hF : ∀ u v, F u → F (stW u A x v)) :
    Frag o [rset x e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u)
      (fun u => Mid A cfg J r s0 (upd ws x val) os l u ∧ F u) := by
  have hn := nums
  have hf := free_scalar x hx
  have hx64 : x < RecoverProg.size := by have := hf.1; simp only [Free] at this; omega
  refine rset_frag o h.hA hf.2 hx64 he (fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, hFc s k h2⟩) fun u ⟨hu, hfu⟩ =>
    ⟨rsc_kept h hu.kept, by rw [hu.kept.memaddrs]; exact h.dom, val, hv u hu hfu, ⟨kept_word hu.kept ⟨x, hx64, rfl⟩ val,
      words_store hu.words (by omega) val, fun q hq => ?_, hu.outIn, rest_stW h.hA hu.rest (.inl hf.1) hf.2 val,
      hu.vals⟩, hF u val hfu⟩
  have hxs := (free_scalar x hx).1
  simp only [Free] at hxs
  have hne : q.1 ≠ x := by
    rcases hu.outIn q hq with hq' | hq'
    · exact fun e => apart x hx (by rw [← e]; exact hq')
    · omega
  have := known_range (hu.outIn q hq)
  rw [stW_word (x := x) (y := q.1) (by omega) (by omega) hne]
  exact hu.outs q hq

/-- A word of `scalars` stored. -/
theorem mid_set (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {x : Nat}
    (hx : x ∈ scalarOffs) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {val : Word}
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → eval u E = some val) :
    Frag o [rset x e] (Mid A cfg J r s0 ws os l) (Mid A cfg J r s0 (upd ws x val) os l) :=
  frag_conseq (mid_set_and o h hx he (F := fun _ => True) (fun u hu _ => hv u hu) (fun _ _ h => h) fun _ _ h => h)
    (fun _ hu => ⟨hu, trivial⟩) fun _ hu => hu.1

/-- A word of what a step gives stored. -/
theorem mid_out (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {x : Nat} (hx : x ∈ outOffs)
    (hos : ∀ q ∈ os, q.1 ≠ x) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {val : Word}
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → eval u E = some val) :
    Frag o [rset x e] (Mid A cfg J r s0 ws os l) (Mid A cfg J r s0 ws ((x, val) :: os) l) := by
  have hn := nums
  have hf := free_out x hx
  have hx64 : x < RecoverProg.size := by have := hf.1; simp only [Free] at this; omega
  refine rset_frag o h.hA hf.2 hx64 he mid_clock fun u hu => ⟨rsc_kept h hu.kept, by rw [hu.kept.memaddrs]; exact h.dom,
    val, hv u hu, kept_word hu.kept ⟨x, hx64, rfl⟩ val, fun y hy => ?_, fun q hq => ?_, fun q hq => ?_,
    rest_stW h.hA hu.rest (.inl hf.1) hf.2 val, hu.vals⟩
  · have hq2 := (free_scalar _ hy).1
    simp only [Free] at hq2
    rw [stW_word (x := x) (y := y) (by omega) (by omega) fun e => apart _ hy (by rw [e]; exact hx)]
    exact hu.words y hy
  · simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp [stW]
    · have := known_range (hu.outIn q hq)
      rw [stW_word (by omega) (by omega) (hos q hq)]; exact hu.outs q hq
  · simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact .inl hx
    · exact hu.outIn q hq

/-- A local of the step's set. -/
theorem mid_assign (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {y : String}
    (hy : y ∈ stepLocals) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {val : Word}
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → eval u E = some val) :
    Frag o [.assign y e] (Mid A cfg J r s0 ws os l) (Mid A cfg J r s0 ws os ((y, val) :: without y l)) :=
  set_frag o he mid_clock fun u hu => ⟨val, hv u hu, kept_has hu.kept (h.bound y (by
      simp only [stepLocals, List.mem_filter] at hy; exact hy.1)),
    ⟨kept_set hu.kept hy val, hu.words, hu.outs, hu.outIn, rest_congr hu.rest rfl rfl rfl,
      vals_set hu.vals y val⟩⟩

/-- The step stops, asking or giving `code`. -/
theorem stop_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} (code : Nat)
    (hos : ∀ q ∈ os, q.1 ≠ rStatus) :
    Frag o (stop code) (Mid A cfg J r s0 ws os l)
      (Mid A cfg J r s0 ws ((rStatus, .ofNat 64 code) :: os) (("rgo", 0) :: without "rgo" l)) :=
  frag_append (xs := [_]) (mid_out o h (x := rStatus) (by decide) hos (E := .const (.ofNat 64 code)) rfl
    fun _ _ => rfl) (mid_assign o h (y := "rgo") (by decide) (E := .op .add (.var "jz") (.const (.ofNat 64 0))) rfl
      (val := 0) fun u hu => by simp [eval, jz_kept h hu.kept])

/-- A local not in `l` set. -/
theorem mid_setL {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ} (hu : Mid A cfg J r s0 ws os l u)
    {y : String} (hy : y ∈ stepLocals) (hyl : ScanRun.Fresh y l = true) (v : Value) :
    Mid A cfg J r s0 ws os l (setL u y v) :=
  ⟨kept_set hu.kept hy v, hu.words, hu.outs, hu.outIn, rest_congr hu.rest rfl rfl rfl, fun q hq => by
    simp only [setL, setLocal, if_neg (ScanRun.fresh_ne hyl q hq)]; exact hu.vals q hq⟩

/-- A word of the area read. -/
theorem rw_eval {A : Word} (hA : A.toNat % 8 = 0) {u : PancakeState σ} (hd : RDom A u.memaddrs)
    (hsp : u.locals "rsc" = some A) {x : Nat} (hx : x % 8 = 0) (hxs : x < RecoverProg.size) {E : PancakeExp}
    (hE : Lower.lowerExp (rw x) = some E) : eval u E = some (u.memory (at_ A x)) := by
  obtain ⟨E', hE', hv⟩ := ScanRun.e_loadw (p := "rsc") hA hd hsp hx hxs
  have e : some E = some E' := hE.symm.trans hE'
  cases e; exact hv

/-- A word of `scalars` read. -/
theorem mid_rw {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0)
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ}
    (hu : Mid A cfg J r s0 ws os l u) {x : Nat} (hx : x ∈ scalarOffs) {E : PancakeExp}
    (hE : Lower.lowerExp (rw x) = some E) : eval u E = some (ws x) := by
  have hn := nums
  have hf := free_scalar x hx
  have : x < RecoverProg.size := by have := hf.1; simp only [Free] at this; omega
  rw [rw_eval h.hA (by rw [hu.kept.memaddrs]; exact h.dom) (rsc_kept h hu.kept) hf.2 this hE, hu.words x hx]

/-- Locals listed fewer. -/
theorem mid_vals {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l l' : List (String × Value)} {u : PancakeState σ} (hu : Mid A cfg J r s0 ws os l u)
    (hs : ∀ q ∈ l', q ∈ l) : Mid A cfg J r s0 ws os l' u :=
  { hu with vals := ScanRun.vals_sub hu.vals hs }

/-- A highest article number stored before the rules hold. -/
theorem mid_high {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0)
    (hp : r.phase < 5) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ}
    (hu : Mid A cfg J r s0 ws os l u) {x : Nat} (hx : x < groupsMax) (v : Word) :
    Mid A cfg J r s0 ws os l (stW u A (rHigh + x * 8) v) := by
  have hn := nums
  have hy : rHigh + x * 8 < RecoverProg.size := by omega
  refine ⟨kept_word hu.kept ⟨_, hy, rfl⟩ v, fun y hy' => ?_, fun q hq => ?_, hu.outIn,
    rest_stW h.hA hu.rest (.inr (.inl ⟨by omega, by omega, hp⟩)) (by omega) v, hu.vals⟩
  · have := (free_scalar y hy').1
    simp only [Free] at this
    rw [stW_word (by omega) (by omega) (by omega)]; exact hu.words y hy'
  · have := known_range (hu.outIn q hq)
    rw [stW_word (by omega) (by omega) (by omega)]; exact hu.outs q hq

/-- A word of the scanner's stored before it reads. -/
theorem mid_scanW {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0)
    (hp : r.phase < 3) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ}
    (hu : Mid A cfg J r s0 ws os l u) {x : Nat} (hx : x < ScanProg.size) (hx8 : x % 8 = 0)
    (hos : ∀ q ∈ os, q.1 ≠ rScan + x) (v : Word) : Mid A cfg J r s0 ws os l (stW u A (rScan + x) v) := by
  have hn := nums
  have hy : rScan + x < RecoverProg.size := by omega
  refine ⟨kept_word hu.kept ⟨_, hy, rfl⟩ v, fun y hy' => ?_, fun q hq => ?_, hu.outIn,
    rest_stW h.hA hu.rest (.inr (.inr (.inl ⟨by omega, by omega, hp⟩))) (by omega) v, hu.vals⟩
  · have := (free_scalar y hy').1
    simp only [Free] at this
    rw [stW_word (by omega) (by omega) (by omega)]; exact hu.words y hy'
  · have := known_range (hu.outIn q hq)
    rw [stW_word (by omega) (by omega) (hos q hq)]; exact hu.outs q hq

theorem outs_stW {A : Word} {qs : List (Nat × Word)} {u : PancakeState σ} (h : Outs A qs u) {y : Nat}
    (hy : y < 2 ^ 64) (hq : ∀ k ∈ qs.map Prod.fst, k ≠ y ∧ k < 2 ^ 64) (v : Word) :
    Outs A ((y, v) :: qs) (stW u A y v) := by
  intro q hq'
  simp only [List.mem_cons] at hq'
  rcases hq' with rfl | hq'
  · simp [stW]
  · have := hq q.1 (List.mem_map_of_mem hq')
    rw [stW_word hy this.2 this.1]; exact h q hq'

theorem outs_keep {A : Word} {qs : List (Nat × Word)} {u : PancakeState σ} (h : Outs A qs u) {y : Nat}
    (hy : y < 2 ^ 64) (hq : ∀ k ∈ qs.map Prod.fst, k ≠ y ∧ k < 2 ^ 64) (v : Word) : Outs A qs (stW u A y v) :=
  fun q hq' => by
    have := hq q.1 (List.mem_map_of_mem hq')
    rw [stW_word hy this.2 this.1]; exact h q hq'

/-- **A word of the scanner's stored** before it reads, what else holds kept. -/
theorem mid_sset (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hp : r.phase < 3) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)}
    {x : Nat} (hx : x % 8 = 0) (hxs : x < ScanProg.size) (hos : ∀ q ∈ os, q.1 ≠ rScan + x) {e : Syntax.PExpr}
    {E : PancakeExp}
    (he : Lower.lowerExp e = some E) {val : Word} {F F' : Assn σ} (hF'c : Safe.ClockFree F')
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u → eval u E = some val)
    (hF : ∀ u, Mid A cfg J r s0 ws os l u → F u → F' (stW u A (rScan + x) val)) :
    Frag o [RecoverProg.sset x e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u)
      (fun u => Mid A cfg J r s0 ws os l u ∧ F' u) := by
  have hn := nums
  have hA' := at_aligned h.hA (x := rScan) (by decide)
  refine ScanRun.store_at_frag o hA' (p := "jsc") (n := ScanProg.size) hx hxs he
    (fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, hF'c s k h2⟩) fun u ⟨hu, hf⟩ => ⟨jsc_kept h hu.kept, fun y hy => ?_, val,
      hv u hu hf, ?_⟩
  · have := h.dom (rScan + y) (by omega)
    rw [hu.kept.memaddrs]; rwa [← at_add A rScan y] at this
  · rw [show at_ (at_ A rScan) x = at_ A (rScan + x) from at_add A rScan x]
    exact ⟨mid_scanW h hp hu hxs hx hos val, hF u hu hf⟩

/-! ## Stores away from what a phase keeps -/

/-- Offsets of words a phase writes away from what it keeps: of the first group the configuration lacks while there
is none, and of the slot after the commits'. -/
def Far (r : RSt) (x : Nat) : Prop :=
  (rUnknownLen ≤ x ∧ x < rTorn ∧ r.unknown = none) ∨
    (slotAt r.commits.length ≤ x ∧ x < slotAt r.commits.length + slotSize ∧ r.commits.length < capacity)

theorem far_bounds {r : RSt} {x : Nat} (h : Far r x) : (rUnknownLen ≤ x ∧ x < rTorn) ∨
    (rSlots ≤ x ∧ x < RecoverProg.size) := by
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, h3⟩
  · exact .inl ⟨h1, h2⟩
  · obtain ⟨s1, s2⟩ := slotAt_le h3
    exact .inr ⟨by omega, by omega⟩

/-- **A word stored away from what a phase keeps**. -/
theorem mid_far {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0)
    {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {u : PancakeState σ}
    (hu : Mid A cfg J r s0 ws os l u) {x : Nat} (hx : Far r x) (hx8 : x % 8 = 0) (hos : ∀ q ∈ os, q.1 ≠ x)
    (v : Word) : Mid A cfg J r s0 ws os l (stW u A x v) := by
  have hn := nums
  have hb := far_bounds hx
  have hxs : x < RecoverProg.size := by omega
  refine ⟨kept_word hu.kept ⟨x, hxs, rfl⟩ v, fun y hy => ?_, fun q hq => ?_, hu.outIn,
    rest_stW h.hA hu.rest (.inr (.inr (.inr hx))) hx8 v, hu.vals⟩
  · have := (free_scalar y hy).1
    simp only [Free] at this
    rw [stW_word (by omega) (by omega) (by omega)]; exact hu.words y hy
  · have := known_range (hu.outIn q hq)
    rw [stW_word (by omega) (by omega) (hos q hq)]; exact hu.outs q hq

/-- A byte stored is the word holding it stored. -/
theorem putByte_stW {A : Word} (hA : A.toNat % 8 = 0) (u : PancakeState σ) (z : Nat) (b : BitVec 8) :
    { u with memory := putByte u.memory u.be (at_ A z) b } =
      stW u A (z / 8 * 8) (setByte (at_ A z) b (u.memory (at_ A (z / 8 * 8))) u.be) := by
  simp only [stW]
  congr 1
  funext k
  show (if k = byteAlign (at_ A z) then _ else _) = _
  rw [align_at hA]

/-- Octets `bs` at `z`, one more stored after them. -/
theorem bytesAt_snoc {A : Word} {z : Nat} {bs : Bytes} {u : PancakeState σ}
    (h : BytesAt A z bs u) (hz : z + bs.length < 2 ^ 63) (hd : u.memaddrs (byteAlign (at_ A (z + bs.length))) = true)
    (b : BitVec 8) : BytesAt A z (bs ++ [b]) { u with memory := putByte u.memory u.be (at_ A (z + bs.length)) b } := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases e : i = bs.length
  · subst e
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem_singleton]
    exact load_putByte_same _ _ _ _ _ hd
  · have hi' : i < bs.length := by omega
    rw [List.getElem_append_left hi']
    show memLoadByte (putByte u.memory u.be (at_ A (z + bs.length)) b) u.memaddrs u.be (at_ A (z + i)) = _
    rw [load_putByte_diff _ _ _ _ _ _ (at_ne (by omega) (by omega) (by omega))]
    exact h i hi'

/-! ## Locals alone changed -/

/-- **A phase's state between stores kept** where only locals it does not list changed. -/
theorem mid_locals {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} {u u' : PancakeState σ} (hu : Mid A cfg J r s0 ws os l u)
    {xs : List String} (hxs : ∀ y ∈ xs, y ∈ stepLocals) (hl : ScanRun.Outside xs l = true)
    (hk : Kept xs (fun _ => False) u u') : Mid A cfg J r s0 ws os l u' := by
  have hk' := ScanRun.kept_trans hu.kept (kept_widen hk hxs fun _ h => h.elim)
  have hv := ScanRun.vals_kept hu.vals hk hl
  rw [kept_false_eq hk] at hk' hv ⊢
  exact ⟨hk', hu.words, hu.outs, hu.outIn, rest_congr hu.rest rfl rfl rfl, hv⟩

/-- The word of `scalars` at `x` read, as the program lowers it. -/
def rwE (x : Nat) : PancakeExp := .loadWord (.op .add (.var "rsc") (.const (.ofNat 64 x)))

theorem offs_ne0 : ∀ x ∈ scalarOffs, x ≠ 0 := by decide

theorem rw_lower {x : Nat} (hx : x ∈ scalarOffs) : Lower.lowerExp (rw x) = some (rwE x) := by
  have : x ≠ 0 := offs_ne0 x hx
  simp [rw, rp, Syntax.atOff, rwE, Lower.lowerExp, Syntax.eAdd, Syntax.v, Syntax.n, this]

/-- A local of the step's not listed set, with what else holds. -/
theorem mid_put (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {y : String}
    (hy : y ∈ stepLocals) (hyl : ScanRun.Fresh y l = true) {e : Syntax.PExpr} {E : PancakeExp}
    (he : Lower.lowerExp e = some E) {F F' : Assn σ} (hF' : Safe.ClockFree F')
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → F u → ∃ val, eval u E = some val ∧ F' (setL u y val)) :
    Frag o [.assign y e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u) (fun u => Mid A cfg J r s0 ws os l u ∧ F' u) :=
  set_frag o he (fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, hF' s k h2⟩) fun u ⟨hm, hf⟩ => by
    obtain ⟨val, hev, hf'⟩ := hv u hm hf
    exact ⟨val, hev, kept_has hm.kept (h.bound y (by simp only [stepLocals, List.mem_filter] at hy; exact hy.1)),
      mid_setL hm hy hyl val, hf'⟩

/-- A local of the step's set, what else holds kept. -/
theorem mid_assign_and (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {ws : Nat → Word} {os : List (Nat × Word)} {l : List (String × Value)} {y : String}
    (hy : y ∈ stepLocals) {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E) {val : Word}
    (hv : ∀ u, Mid A cfg J r s0 ws os l u → eval u E = some val) {F : Assn σ} (hFc : Safe.ClockFree F)
    (hF : ∀ u, F u → F (setL u y val)) :
    Frag o [.assign y e] (fun u => Mid A cfg J r s0 ws os l u ∧ F u)
      (fun u => Mid A cfg J r s0 ws os ((y, val) :: without y l) u ∧ F u) :=
  set_frag o he (fun s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, hFc s k h2⟩) fun u ⟨hu, hfu⟩ => ⟨val, hv u hu,
    kept_has hu.kept (h.bound y (by simp only [stepLocals, List.mem_filter] at hy; exact hy.1)),
    ⟨kept_set hu.kept hy val, hu.words, hu.outs, hu.outIn, rest_congr hu.rest rfl rfl rfl, vals_set hu.vals y val⟩,
    hF u hfu⟩

/-- Words of `scalars` stored, each a number. -/
theorem mid_consts (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) {os : List (Nat × Word)} {l : List (String × Value)} :
    ∀ (ps : List (Nat × Nat)) (ws : Nat → Word), (∀ p ∈ ps, p.1 ∈ scalarOffs) →
      Frag o (ps.map fun p => rset p.1 (Syntax.n p.2)) (Mid A cfg J r s0 ws os l)
        (Mid A cfg J r s0 (ps.foldl (fun ws p => upd ws p.1 (.ofNat 64 p.2)) ws) os l)
  | [], _, _ => frag_nil o fun _ h => h
  | p :: ps, _, hp => frag_append (xs := [_])
      (mid_set o h (hp p (List.mem_cons_self ..)) (E := .const (.ofNat 64 p.2)) rfl fun _ _ => rfl)
      (mid_consts o h ps _ fun q hq => hp q (List.mem_cons_of_mem _ hq))

/-- A phase's start as a state between stores. -/
theorem mid_start {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PIn A cfg J r s0)
    {u : PancakeState σ} (hu : Like s0 u) : Mid A cfg J r s0 (scalars cfg r) [] [("rgo", 1)] u :=
  ⟨ScanRun.kept_of_like hu, by intro q hq; rw [hu.memory]; exact h.area.words q hq, (fun _ h => nomatch h),
    (fun _ h => nomatch h), rest_congr h.area.rest hu.memory hu.memaddrs hu.be,
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; rw [hu.locals]; exact h.rgo⟩

/-- **A phase's end**, from a state between stores: the words those of `r'`, what is left of `r'`, and with an
output, the step stopped. -/
theorem mid_end {A : Word} {cfg : Config} {J : Bytes} {r r' : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} {oo : Option ROut} {u : PancakeState σ}
    (h : Mid A cfg J r s0 ws os l u)
    (hw : ∀ x ∈ scalarOffs, ws x = scalars cfg r' x) (hr : Rest A cfg J r u → Rest A cfg J r' u)
    (ho : match oo with
      | none => u.locals "rgo" = some 1
      | some o => u.locals "rgo" = some 0 ∧ OutR A J r' o u) :
    POut A cfg J s0 (r', oo) u :=
  ⟨h.kept, ⟨words_ext h.words hw, hr h.rest⟩, ho⟩

end DN.News.RecoverArea
