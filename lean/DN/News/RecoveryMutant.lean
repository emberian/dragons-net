-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Recovery

/-!
# DN.News.RecoveryMutant

Recovery (`DN.News.Recovery`) with one of its rules changed, for the lane that holds recovery
against an independent reference to show that it sees each (`scripts/store_check.py`). With no rule
changed it is recovery (`recoverM_none`); with any, a directory written for it recovers otherwise
(`mutants_differ`), or for the bound on articles, its commits (`capacity_differs`).
-/

namespace DN.News.RecoveryMutant

open DN.News.Journal
open DN.News.Recovery
open DN.News.CommandSpec (ascii)

/-- A version of recovery with one of its rules changed. -/
inductive Mutant
  | none
  /-- a sequence number in two records let be -/
  | seqUnchecked
  /-- article numbers that do not rise let be -/
  | numbersUnchecked
  /-- an article number equal to the group's last let be -/
  | numbersEqual
  /-- a group the configuration lacks let be -/
  | groupsUnchecked
  /-- a file of another size than its record's let be -/
  | sizeUnchecked
  /-- a record whose file is missing let be -/
  | missingUnchecked
  /-- a name of no shape the store gives passed over -/
  | namesIgnored
  /-- a journal created among other files -/
  | journalAmongFiles
  /-- a journal with no format made again among other files -/
  | remadeAmongFiles
  /-- the next number above the records' alone, not the names' -/
  | nextRecordsOnly
  /-- no number skipped for a torn tail -/
  | tornNoBump
  /-- a torn tail cut with no file kept for it -/
  | tailDropped
  /-- a torn tail kept without its offset in front -/
  | tailUnprefixed
  /-- names tidied before the torn tail is cut -/
  | tidyFirst
  /-- a final file no record names never set aside -/
  | asideNever
  /-- a final file no record names set aside whatever the journal's end and the tails, unless set
  aside already -/
  | asideAlways
  /-- a final file no record names renamed over a file set aside under its number -/
  | asideOverQuarantine
  /-- a final file set aside also when a tail kept has its number, not only one above it -/
  | asideAtTail
  /-- a temporary file kept -/
  | tempKept
  /-- the directory not synced after names are tidied -/
  | tidyUnsynced
  /-- sequence numbers taken to run out one later -/
  | exhaustedLate
  /-- a key for a new journal of any length -/
  | keyUnchecked
  /-- the store's key taken from the configuration, not from the journal -/
  | keyFromConfig
  /-- one article more than `capacity` let through -/
  | capacityLate
  deriving DecidableEq

def names : List (String × Mutant) :=
  [("seq-unchecked", .seqUnchecked), ("numbers-unchecked", .numbersUnchecked),
   ("numbers-equal", .numbersEqual), ("groups-unchecked", .groupsUnchecked),
   ("size-unchecked", .sizeUnchecked), ("missing-unchecked", .missingUnchecked),
   ("names-ignored", .namesIgnored), ("journal-among-files", .journalAmongFiles),
   ("remade-among-files", .remadeAmongFiles), ("next-records-only", .nextRecordsOnly),
   ("torn-no-bump", .tornNoBump), ("tail-dropped", .tailDropped), ("tidy-first", .tidyFirst),
   ("aside-never", .asideNever), ("aside-always", .asideAlways), ("aside-at-tail", .asideAtTail),
   ("temp-kept", .tempKept), ("tidy-unsynced", .tidyUnsynced), ("exhausted-late", .exhaustedLate),
   ("key-unchecked", .keyUnchecked), ("tail-unprefixed", .tailUnprefixed),
   ("aside-over-quarantine", .asideOverQuarantine), ("key-from-config", .keyFromConfig),
   ("capacity-late", .capacityLate)]

/-! ## Recovery, its rules changed -/

def notAboveM (m : Mutant) (before : List Commit) : List Commit → Option (Bytes × Nat)
  | [] => none
  | c :: cs =>
    match c.groups.find? (fun g =>
        if m = .numbersEqual then decide (g.number < highIn before g.name)
        else decide (g.number ≤ highIn before g.name)) with
    | some g => some (g.name, g.number)
    | none => notAboveM m (before ++ [c]) cs

def fileFaultM (m : Mutant) (img : Image) : List Commit → Option Fault
  | [] => none
  | c :: cs =>
    match img.lookup (finalName c.seq) with
    | none => if m = .missingUnchecked then fileFaultM m img cs else some (.missingFile c.seq)
    | some f =>
      if f.length = c.fileSize || m = .sizeUnchecked then fileFaultM m img cs
      else some (.wrongSize c.seq)

def nextSeqM (m : Mutant) (cs : List Commit) (names : List Name) : Nat :=
  (cs.map (·.seq) ++ (if m = .nextRecordsOnly then [] else names.filterMap seqOf)).foldl max 0 + 1

def setsAsideM (m : Mutant) (names : List Name) (torn : Bool) (s : Nat) : Bool :=
  if m = .asideNever then false
  else if m = .asideAlways then true
  else torn || names.any fun n => match n with
    | .tail t => if m = .asideAtTail then decide (s ≤ t) else decide (s < t)
    | _ => false

def tidyNameM (m : Mutant) (recorded : List Bytes) (names : List Name) (torn : Bool) :
    Name → Option Action
  | .temp s => if m = .tempKept then none else some (.remove (tempName s))
  | .final s =>
    if recorded.contains (finalName s) then none
    else if (names.contains (.quarantine s) && m ≠ .asideOverQuarantine) ||
        !setsAsideM m names torn s then
      some (.remove (finalName s))
    else some (.rename (finalName s) (quarantineName s))
  | _ => none

def asideOfM (m : Mutant) (recorded : List Bytes) (names : List Name) (torn : Bool) :
    Name → Option Nat
  | .final s =>
    if !recorded.contains (finalName s) && !names.contains (.quarantine s) &&
        setsAsideM m names torn s then some s
    else none
  | .quarantine s | .tail s => some s
  | _ => none

def recoverRecordsM (m : Mutant) (cfg : Config) (img : Image) (names : List Name)
    (content key : Bytes) (cs : List Commit) (cut : Option Nat) :
    Except Fault (Store × List Action) :=
  if (if m = .capacityLate then decide (capacity + 1 < cs.length)
      else decide (capacity < cs.length)) then .error (.tooMany cs.length) else
  match (if m = .seqUnchecked then none else seqTwice? cs),
      (if m = .numbersUnchecked then none else notAboveM m [] cs),
      (if m = .groupsUnchecked then none else unknownGroup? cfg cs), fileFaultM m img cs with
  | some s, _, _, _ => .error (.seqTwice s)
  | none, some (g, n), _, _ => .error (.numberNotAbove g n)
  | none, none, some g, _ => .error (.unknownGroup g)
  | none, none, none, some f => .error f
  | none, none, none, none =>
    let next0 := nextSeqM m cs names
    let next := if cut.isSome && m ≠ .tornNoBump then next0 + 1 else next0
    if (if m = .exhaustedLate then decide (2 ^ 64 < next) else decide (2 ^ 64 ≤ next)) then
      .error .exhausted
    else
      let recorded := cs.map (finalName ·.seq)
      let tidy := names.filterMap (tidyNameM m recorded names cut.isSome)
      let tail :=
        match cut with
        | some x =>
          if m = .tailDropped then [Action.cut x]
          else
            let kept := if m = .tailUnprefixed then content.drop x else le 8 x ++ content.drop x
            [Action.keep (tailName next0) kept, .syncDir, .cut x]
        | none => []
      let synced := if tidy.isEmpty || m = .tidyUnsynced then [] else [Action.syncDir]
      let ops := if m = .tidyFirst then tidy ++ synced ++ tail else tail ++ tidy ++ synced
      let setAside := names.filterMap (asideOfM m recorded names cut.isSome) ++
        (if cut.isSome then [next0] else [])
      .ok (⟨if m = .keyFromConfig then cfg.key else key, cs, setAside, next,
        cut.getD content.length⟩, ops)

/-- The names of a directory: every one when names are read strictly, else those of a shape the
store gives. -/
def namesM (m : Mutant) (img : Image) : Except Fault (List Name) :=
  if m = .namesIgnored then .ok (img.filterMap (parseName ·.1)) else img.mapM nameOf

def recoverWithM (m : Mutant) (cfg : Config) (img : Image) : Except Fault (Store × List Action) :=
  match namesM m img with
  | .error f => .error f
  | .ok names =>
    match img.lookup journalName with
    | none =>
      if img.isEmpty || m = .journalAmongFiles then .ok (fresh cfg, [.create cfg.key, .syncDir])
      else .error .noJournal
    | some content =>
      let sc := scan content
      match sc.ending, sc.records with
      | .corrupt at_ w, _ => .error (.journal at_ w)
      | _, [] =>
        if img.length = 1 || m = .remadeAmongFiles then .ok (fresh cfg, [.create cfg.key])
        else .error .noJournal
      | ending, .format key :: rest =>
        recoverRecordsM m cfg img names content key (commitsOf rest) (cutOf ending)
      | _, _ => .error (.journal 0 .notARecord)

def recoverM (m : Mutant) (cfg : Config) (img : Image) : Except Fault (Store × List Action) :=
  if cfg.key.length = keyLength || m = .keyUnchecked then recoverWithM m cfg img
  else .error .badKey

/-! ## With no rule changed it is recovery -/

theorem notAboveM_none (before cs : List Commit) :
    notAboveM .none before cs = notAbove? before cs := by
  induction cs generalizing before with
  | nil => rfl
  | cons c cs ih =>
    simp only [notAboveM, notAbove?, reduceCtorEq, ↓reduceIte, ih]
    rfl

theorem fileFaultM_none (img : Image) (cs : List Commit) :
    fileFaultM .none img cs = fileFault? img cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [fileFaultM, fileFault?, reduceCtorEq, ↓reduceIte, decide_false, Bool.or_false,
      decide_eq_true_eq, ih]
    rfl

theorem setsAsideM_none : setsAsideM .none = setsAside := by
  funext names torn s
  simp only [setsAsideM, setsAside, reduceCtorEq, ↓reduceIte]
  rfl

theorem tidyNameM_none : tidyNameM .none = tidyName := by
  funext recorded names torn n
  cases n <;> simp [tidyNameM, tidyName, setsAsideM_none]

theorem asideOfM_none : asideOfM .none = asideOf := by
  funext recorded names torn n
  cases n <;> simp [asideOfM, asideOf, setsAsideM_none]

theorem recoverRecordsM_none : recoverRecordsM .none = recoverRecords := by
  funext cfg img names content key cs cut
  simp only [recoverRecordsM, recoverRecords, notAboveM_none, fileFaultM_none, tidyNameM_none,
    asideOfM_none, nextSeqM, reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, Bool.and_true,
    decide_true, decide_false, Bool.or_false, decide_eq_true_eq]
  rfl

theorem recoverM_none : recoverM .none = recover := by
  funext cfg img
  simp only [recoverM, recover, reduceCtorEq, decide_false, Bool.or_false, decide_eq_true_eq,
    recoverWithM, recoverWith, namesM, ↓reduceIte, recoverRecordsM_none]
  rfl

/-! ## Every rule of recovery matters -/

/-- Whether two outcomes of recovery are the same, decided. -/
instance : DecidableEq (Except Fault (Store × List Action)) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | .error x, .error y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | .ok _, .error _ => isFalse fun e => by cases e
  | .error _, .ok _ => isFalse fun e => by cases e

/-- The configuration of the witnesses: the sample group, the sample key. -/
def sampleConfig : Config := ⟨[ascii "local.test"], sampleKey⟩

/-- The sample group and a key other than the sample key. -/
def otherConfig : Config := ⟨[ascii "local.test"], List.replicate keyLength 1⟩

/-- A commit of the witnesses: sequence number `seq`, the sample group's number `n`, a file of one
octet. -/
def commitOf (seq n : Nat) : Commit := ⟨seq, ascii "<a@b>", [⟨ascii "local.test", n⟩], 1, 1, 0⟩

/-- A journal of the sample key holding these commits. -/
def journalOf (cs : List Commit) : Bytes := journal sampleKey (cs.map .commit)

/-- A journal of the format alone, its append after it torn after one octet. -/
def tornJournal : Bytes := journal sampleKey [] ++ [0]

/-- A configuration and a directory that tell recovery with one rule changed from recovery. None
makes the kernel compute a tag over more than two small commits; the bound's would, so its witness
is its commits alone (`capacity_differs`). -/
def witness : Mutant → Config × Image
  | .none => (sampleConfig, [])
  | .seqUnchecked =>
    (sampleConfig, [(journalName, journalOf [commitOf 1 1, commitOf 1 2]), (finalName 1, [0])])
  | .numbersUnchecked | .numbersEqual =>
    (sampleConfig, [(journalName, journalOf [commitOf 1 1, commitOf 2 1]), (finalName 1, [0]),
      (finalName 2, [0])])
  | .groupsUnchecked =>
    (⟨[], sampleKey⟩, [(journalName, journalOf [commitOf 1 1]), (finalName 1, [0])])
  | .sizeUnchecked =>
    (sampleConfig, [(journalName, journalOf [commitOf 1 1]), (finalName 1, [0, 0])])
  | .missingUnchecked => (sampleConfig, [(journalName, journalOf [commitOf 1 1])])
  | .namesIgnored => (sampleConfig, [(journalName, journalOf []), (ascii "x", [])])
  | .journalAmongFiles => (sampleConfig, [(tempName 1, [])])
  | .remadeAmongFiles => (sampleConfig, [(journalName, (journalOf []).take 3), (tempName 1, [])])
  | .nextRecordsOnly => (sampleConfig, [(journalName, journalOf []), (tempName 5, [])])
  | .tornNoBump | .tailDropped | .tailUnprefixed => (sampleConfig, [(journalName, tornJournal)])
  | .tidyFirst => (sampleConfig, [(journalName, tornJournal), (tempName 1, [])])
  | .asideNever => (sampleConfig, [(journalName, tornJournal), (finalName 1, [])])
  | .asideAlways => (sampleConfig, [(journalName, journalOf []), (finalName 1, [])])
  | .asideOverQuarantine =>
    (sampleConfig, [(journalName, tornJournal), (finalName 1, []), (quarantineName 1, [])])
  | .asideAtTail =>
    (sampleConfig, [(journalName, journalOf []), (finalName 1, []), (tailName 1, [])])
  | .tempKept | .tidyUnsynced => (sampleConfig, [(journalName, journalOf []), (tempName 1, [])])
  | .exhaustedLate => (sampleConfig, [(journalName, journalOf []), (tempName (2 ^ 64 - 1), [])])
  | .keyUnchecked => (⟨[], []⟩, [])
  | .keyFromConfig => (otherConfig, [(journalName, journalOf [])])
  | .capacityLate => (sampleConfig, [])

/-- **Each rule changed here matters**: with it changed, its witness recovers otherwise. -/
theorem mutants_differ : ∀ m, m ≠ .none → m ≠ .capacityLate →
    recoverM m (witness m).1 (witness m).2 ≠ recover (witness m).1 (witness m).2 := by
  intro m hm hc
  cases m <;> first | exact absurd rfl hm | exact absurd rfl hc | decide +kernel

/-- **The bound matters**: one commit past it, recovery with it changed goes on to the rules. -/
theorem capacity_differs :
    let cs := List.replicate (capacity + 1) (commitOf 1 1)
    recoverRecordsM .capacityLate sampleConfig [] [] [] sampleKey cs none ≠
      recoverRecords sampleConfig [] [] [] sampleKey cs none := by
  decide +kernel

end DN.News.RecoveryMutant
