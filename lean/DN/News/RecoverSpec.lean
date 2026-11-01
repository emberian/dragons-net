-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Recovery
import DN.News.ScanSpec

/-!
# DN.News.RecoverSpec

Recovery's step (`DN.News.RecoverProg.stepWith`) as a function of what its area keeps between steps (`RSt`),
phase by phase under the program's names (`phase`); a step runs phases until one asks the host for something or
gives it something (`Steps`). A host that reads the directory `img` — its names in order, the journal's octets,
each final file and each name set aside — and notes what it is given (`answer`) drives the steps to what
`Recovery.recover` finds (`DN.News.RecoverDrive`). That the program's step is `phase` is not shown here.
-/

namespace DN.News.RecoverSpec

open DN.News.Journal DN.News.Recovery
open DN.News.ScanRun (St stepSpec)

/-- An action as the step gives it: a torn tail kept under a number, from where it is cut; a final file set aside
or removed, or a temporary one removed; the directory synced; the journal cut; a new journal created. -/
inductive Act
  | keep (seq cut : Nat)
  | rename (seq : Nat)
  | remove (seq : Nat) (temp : Bool)
  | syncDir
  | cut (x : Nat)
  | create
  deriving DecidableEq

/-- What a step asks of the host or gives it: a name of the directory, the journal's length, octets of the
journal, whether a final file is there and its size, whether a name set aside is; an action, a number set aside;
the store it starts with, or why it does not start. -/
inductive ROut
  | askName
  | askJournal
  | askOctets (n : Nat)
  | askFile (seq : Nat)
  | askAside (seq : Nat)
  | gives (a : Act)
  | givesAside (n : Nat)
  | done
  | refused (f : Fault)
  deriving DecidableEq

/-- What the step keeps between steps, and the host's last replies; all zero to start. -/
structure RSt where
  /-- the phase the next step runs -/
  phase : Nat := 0
  /-- a counter of the phase's -/
  i : Nat := 0
  /-- whether a file was asked about -/
  wait : Bool := false
  /-- whether the next name asked for is the directory's first -/
  first : Bool := false
  /-- how many names the first pass read -/
  names : Nat := 0
  /-- whether the journal is among them -/
  journal : Bool := false
  /-- the highest number a name carries -/
  maxSeq : Nat := 0
  /-- whether a tail is kept -/
  tails : Bool := false
  /-- the highest number a kept tail carries -/
  maxTail : Nat := 0
  /-- the journal's commits read, in its order -/
  commits : List Commit := []
  /-- how many records were read -/
  records : Nat := 0
  /-- the first group a commit carries that the configuration lacks -/
  unknown : Option Bytes := none
  /-- whether the journal ends torn -/
  torn : Bool := false
  /-- where the torn tail starts -/
  cut : Nat := 0
  /-- whether the store starts new -/
  fresh : Bool := false
  /-- the next number before a torn tail is kept -/
  next0 : Nat := 0
  /-- the next number after -/
  next : Nat := 0
  /-- where the journal ends -/
  journalEnd : Nat := 0
  /-- how many names were tidied -/
  tidied : Nat := 0
  /-- the number of a file asked about or set aside -/
  seq : Nat := 0
  /-- the scanner's state -/
  scan : St := St.start
  /-- the host's reply that no name is left -/
  ended : Bool := false
  /-- the host's name -/
  name : Bytes := []
  /-- the host's reply whether a file is there -/
  found : Bool := false
  /-- the host's size of it -/
  fileSize : Nat := 0
  /-- the host's journal's length -/
  jsize : Nat := 0

/-- The state the host's area starts in: all zero. -/
def RSt.start : RSt := {}

/-- A new journal, and the directory synced when it held no file at all. -/
def startNew (r : RSt) (synced : Bool) : RSt :=
  { r with fresh := true, next := 1, journalEnd := firstFrame, i := 0, wait := synced, phase := 10 }

/-- The first group of a commit the configuration lacks. -/
def unknownIn (cfg : Config) (c : Commit) : Option Bytes :=
  (c.groups.find? fun g => !cfg.groups.contains g.name).map (·.name)

/-- A record read: counted, and a commit noted while the index has room. -/
def recordRead (cfg : Config) (r : RSt) : Record → RSt
  | .commit c =>
    { r with commits := r.commits ++ [c],
             unknown := if r.commits.length + 1 ≤ capacity then r.unknown <|> unknownIn cfg c else r.unknown }
  | _ => r

/-- The journal read to its end, torn at `t` if it is: none records, the store new or no journal; else the
rules next. -/
def scanned (r : RSt) (t : Option Nat) : RSt × Option ROut :=
  if r.records = 0 then
    if r.names = 1 then (startNew r false, none) else (r, some (.refused .noJournal))
  else
    match t with
    | some p => ({ r with journalEnd := p, torn := true, cut := p, phase := 4 }, none)
    | none => ({ r with journalEnd := r.jsize, phase := 4 }, none)

/-- What a name does to the first pass. -/
def firstName (r : RSt) : Name → RSt
  | .journal => { r with journal := true }
  | .final s | .temp s | .quarantine s => { r with maxSeq := max r.maxSeq s }
  | .tail s => { r with maxSeq := max r.maxSeq s, tails := true, maxTail := max r.maxTail s }

/-- What a name does to the second pass: a temporary file removed; a final file no commit names set aside, or
removed when set aside already or not to be; a name set aside given. -/
def secondName (r : RSt) : Option Name → RSt × Option ROut
  | some (.temp s) => ({ r with seq := s, tidied := r.tidied + 1, phase := 13 }, some (.gives (.remove s true)))
  | some (.final s) =>
    let r1 := { r with seq := s }
    if (r.commits.map (·.seq)).contains s then (r1, some .askName)
    else if r.torn || (r.tails && decide (s < r.maxTail)) then ({ r1 with phase := 9 }, some (.askAside s))
    else ({ r1 with tidied := r.tidied + 1, phase := 13 }, some (.gives (.remove s false)))
  | some (.quarantine s) | some (.tail s) => ({ r with seq := s, phase := 13 }, some (.givesAside s))
  | _ => (r, some .askName)

/-! ## The phases, under the program's names -/

/-- Phase 0: the first name asked for. -/
def begin (r : RSt) : RSt × Option ROut :=
  ({ r with names := 0, journal := false, maxSeq := 0, tails := false, maxTail := 0, commits := [], records := 0,
            unknown := none, torn := false, fresh := false, tidied := 0, wait := false, first := true, phase := 1 },
   some .askName)

/-- Phase 1: a name of the first pass, or none left. -/
def firstPass (r : RSt) : RSt × Option ROut :=
  if r.ended then
    if r.journal then ({ r with phase := 2 }, some .askJournal)
    else if r.names = 0 then (startNew r true, none)
    else (r, some (.refused .noJournal))
  else
    match parseName r.name with
    | none => (r, some (.refused (.badName r.name)))
    | some n => ({ firstName { r with names := r.names + 1 } n with first := false }, some .askName)

/-- Phase 2: the journal's length given, the scanner set to read it. -/
def journalGiven (r : RSt) : RSt × Option ROut := ({ r with scan := St.start, phase := 3 }, none)

/-- Phase 3: a step of the scanner. -/
def scanning (cfg : Config) (J : Bytes) (r : RSt) : RSt × Option ROut :=
  match stepSpec J r.scan with
  | .want st' n => ({ r with scan := st' }, some (.askOctets n))
  | .record rec st' => (recordRead cfg { r with scan := st', records := r.records + 1 } rec, none)
  | .stop (.corrupt p w) => (r, some (.refused (.journal p w)))
  | .stop (.torn p) => scanned r (some p)
  | .clean | .stop .clean => scanned r none

/-- Phase 4: the rules across records, in the specification's order. -/
def rules (r : RSt) : RSt × Option ROut :=
  if capacity + 1 ≤ r.commits.length then (r, some (.refused (.tooMany r.commits.length)))
  else
    match seqTwice? r.commits, idTwice? r.commits, r.unknown, notAbove? [] r.commits with
    | some s, _, _, _ => (r, some (.refused (.seqTwice s)))
    | none, some m, _, _ => (r, some (.refused (.idTwice m)))
    | none, none, some g, _ => (r, some (.refused (.unknownGroup g)))
    | none, none, none, some (g, n) => (r, some (.refused (.numberNotAbove g n)))
    | none, none, none, none => ({ r with i := 0, wait := false, phase := 5 }, none)

/-- Phase 5: each commit's final file, there and of its size, in the journal's order. -/
def files (r : RSt) : RSt × Option ROut :=
  match r.commits[r.i]? with
  | none => ({ r with phase := 6 }, none)
  | some c =>
    if r.wait then
      if !r.found then (r, some (.refused (.missingFile c.seq)))
      else if r.fileSize ≠ c.fileSize then (r, some (.refused (.wrongSize c.seq)))
      else ({ r with wait := false, i := r.i + 1 }, none)
    else ({ r with seq := c.seq, wait := true }, some (.askFile c.seq))

/-- Phase 6: the next sequence number, while numbers last. -/
def numbered (r : RSt) : RSt × Option ROut :=
  let rm := (r.commits.map (·.seq)).foldl max r.maxSeq
  if rm = 2 ^ 64 - 1 ∨ (r.torn ∧ rm = 2 ^ 64 - 2) then (r, some (.refused .exhausted))
  else ({ r with next0 := rm + 1, next := rm + 1 + (if r.torn then 1 else 0), i := 0, phase := 7 }, none)

/-- Phase 7: a torn tail kept, the directory synced, the journal cut; then the second pass. -/
def tail (r : RSt) : RSt × Option ROut :=
  if !r.torn || r.i == 3 then ({ r with first := true, phase := 8 }, some .askName)
  else if r.i = 0 then ({ r with i := r.i + 1 }, some (.gives (.keep r.next0 r.cut)))
  else if r.i = 1 then ({ r with i := r.i + 1 }, some (.gives .syncDir))
  else ({ r with i := r.i + 1 }, some (.gives (.cut r.cut)))

/-- Phase 8: a name of the second pass, or none left. -/
def secondPass (r : RSt) : RSt × Option ROut :=
  if r.ended then ({ r with i := 0, phase := 11 }, none)
  else secondName { r with first := false } (parseName r.name)

/-- Phase 9: whether the name a final file is set aside under holds one already. -/
def asideGiven (r : RSt) : RSt × Option ROut :=
  if r.found then ({ r with tidied := r.tidied + 1, phase := 13 }, some (.gives (.remove r.seq false)))
  else ({ r with tidied := r.tidied + 1, phase := 12 }, some (.gives (.rename r.seq)))

/-- Phase 10: a new journal created, and the directory synced if it held no file. -/
def created (r : RSt) : RSt × Option ROut :=
  if r.i = 0 then ({ r with i := r.i + 1 }, some (.gives .create))
  else if r.i = 1 && r.wait then ({ r with i := r.i + 1 }, some (.gives .syncDir))
  else ({ r with i := r.i + 1 }, some .done)

/-- Phase 11: the directory synced after names are tidied, the torn tail's number set aside, done. -/
def finish (r : RSt) : RSt × Option ROut :=
  if r.i = 0 ∧ 0 < r.tidied then ({ r with i := r.i + 1 }, some (.gives .syncDir))
  else if r.i ≤ 1 ∧ r.torn then ({ r with i := 2 }, some (.givesAside r.next0))
  else ({ r with i := r.i + 1 }, some .done)

/-- Phase 12: the number of a final file just set aside. -/
def renamed (r : RSt) : RSt × Option ROut := ({ r with phase := 13 }, some (.givesAside r.seq))

/-- Phase 13, and any other: the next name of the second pass asked for. -/
def askNext (r : RSt) : RSt × Option ROut := ({ r with first := false, phase := 8 }, some .askName)

/-- **A phase**, as the step runs it: the state after it, and what it asks or gives, if anything. -/
def phase (cfg : Config) (J : Bytes) (r : RSt) : RSt × Option ROut :=
  match r.phase with
  | 0 => begin r
  | 1 => firstPass r
  | 2 => journalGiven r
  | 3 => scanning cfg J r
  | 4 => rules r
  | 5 => files r
  | 6 => numbered r
  | 7 => tail r
  | 8 => secondPass r
  | 9 => asideGiven r
  | 10 => created r
  | 11 => finish r
  | 12 => renamed r
  | _ => askNext r

/-- **A step**: phases from `r` until one asks or gives `o`, leaving `r'`. -/
inductive Steps (cfg : Config) (J : Bytes) : RSt → RSt → ROut → Prop
  | out {r r' : RSt} {o : ROut} : phase cfg J r = (r', some o) → Steps cfg J r r' o
  | go {r r' r'' : RSt} {o : ROut} : phase cfg J r = (r', none) → Steps cfg J r' r'' o → Steps cfg J r r'' o

/-! ## The host -/

/-- What the host keeps: the next name of the directory, the actions and the numbers set aside given. -/
structure Host where
  /-- where the next name asked for is in the directory's listing -/
  cursor : Nat
  /-- the actions given, in order -/
  acts : List Action
  /-- the numbers set aside given, in order -/
  aside : List Nat

/-- The host before any step: the directory's first name next, nothing given. -/
def Host.start : Host := ⟨0, [], []⟩

/-- An action the step gives, as the host does it: a torn tail's octets kept with where it was cut, octets the
journal `J` holds from there. -/
def actOf (cfg : Config) (J : Bytes) : Act → Action
  | .keep s x => .keep (tailName s) (le 8 x ++ J.drop x)
  | .rename s => .rename (finalName s) (quarantineName s)
  | .remove s t => .remove (if t then tempName s else finalName s)
  | .syncDir => .syncDir
  | .cut x => .cut x
  | .create => .create cfg.key

/-- **The host's answer** to what a step asks or gives, the directory `img` and its journal `J`. -/
def answer (cfg : Config) (img : Image) (J : Bytes) (r : RSt) (h : Host) : ROut → RSt × Host
  | .askName =>
    let c := if r.first then 0 else h.cursor
    match img[c]? with
    | none => ({ r with ended := true }, { h with cursor := c })
    | some p => ({ r with ended := false, name := p.1 }, { h with cursor := c + 1 })
  | .askJournal => ({ r with jsize := J.length }, h)
  | .askOctets n => ({ r with scan := r.scan.fill n }, h)
  | .askFile s =>
    match img.lookup (finalName s) with
    | none => ({ r with found := false, fileSize := 0 }, h)
    | some f => ({ r with found := true, fileSize := f.length }, h)
  | .askAside s => ({ r with found := (img.lookup (quarantineName s)).isSome }, h)
  | .gives a => (r, { h with acts := h.acts ++ [actOf cfg J a] })
  | .givesAside n => (r, { h with aside := h.aside ++ [n] })
  | .done | .refused _ => (r, h)

/-- The store a step done starts with: a new journal's key, or the journal's. -/
def storeAt (cfg : Config) (r : RSt) (h : Host) : Store :=
  ⟨if r.fresh then cfg.key else r.scan.key.getD [], r.commits, h.aside, r.next, r.journalEnd⟩

/-- Whether a step's output ends recovery. -/
def ROut.ends : ROut → Bool
  | .done | .refused _ => true
  | _ => false

/-- **Steps the host answers**, until what recovery finds. -/
inductive Drives (cfg : Config) (img : Image) (J : Bytes) :
    RSt → Host → Except Fault (Store × List Action) → Prop
  | done {r r' : RSt} {h : Host} : Steps cfg J r r' .done → Drives cfg img J r h (.ok (storeAt cfg r' h, h.acts))
  | refused {r r' : RSt} {h : Host} {e : Fault} : Steps cfg J r r' (.refused e) →
      Drives cfg img J r h (.error e)
  | next {r r' : RSt} {h : Host} {o : ROut} {x : Except Fault (Store × List Action)} : Steps cfg J r r' o →
      o.ends = false → Drives cfg img J (answer cfg img J r' h o).1 (answer cfg img J r' h o).2 x →
      Drives cfg img J r h x

end DN.News.RecoverSpec
