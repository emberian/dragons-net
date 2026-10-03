-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoveryRun

/-!
# DN.News.StoreOps

The store's program once it has started, on the file system of `DN.News.FsModel`, as
docs/decisions/0005-article-store.md says it accepts an article: a sequence number reserved; the
article written to a file under the temporary name, the file synced, moved to the final name and the
directory synced; its commit record appended to the journal and the journal synced; and only then
240. A failure known before the record is written refuses the article with 441 and removes its file;
a failed sync of any kind, or a failed write of the journal, stops the store accepting, after which
articles in flight are refused and a record in flight is not answered. Any number of articles may be
in flight, their steps in any order, and records are appended one at a time. Steps come in the order
their operations take effect. A failure the program has not yet learned of changes only the file it
failed on or whether the directory's syncs are trusted, so other operations commute with it; one
that does not, a sync of the directory after a failed one, 0005 rules out by keeping one sync of the
journal or of the directory in flight at a time. That argument is not proven here.

Proven: from a store started by recovery (`running_started`), every step — and whatever its
operation leaves when it fails — keeps the store running (`running_step`): a spool whose journal
holds the records the program keeps and at most one record in flight past them, every article in
flight apart from the others and from the commits in place, its file as its stage says, the syncs of
the journal and the directory trusted until one fails, and no record appended for an article refused
(`Running`). So a crash at any point, under what is assumed of the journal, recovers without
corruption, finding every article answered, and only commits a run appended for an article it did
not refuse, each with the octets written for it (`running_crash`); and a restart, until a sync of
the journal or the directory has failed and while numbers last, starts as `start_safe` says
(`running_restart`). The program's part is taken as given, each part shown needed by examples: a
commit appended only once its article's file is placed, one at a time, with its own number, the
file's size, a record the journal can hold and its article numbers allocated above each group's last
in groups the store carries (`Allocated`); 240 only once the journal is synced; and no article
accepted once a sync or a write of the journal has failed. The file's CRC-32C, which reads check and
recovery does not, is taken as given so that every article recovered has it.
-/

namespace DN.News.StoreOps

open DN.News.Journal
open DN.News.FsModel (Data Entry Fs Ino Op rebind Crash)
open DN.News.Recovery
open DN.News.JournalCrash
open DN.News.Spool
open DN.News.SpoolOps
open DN.News.RecoveryRun
open DN.News.CommandSpec (ascii)

/-! ## The program -/

/-- Where an article in flight is. -/
inductive Stage
  /-- a sequence number reserved, no file yet -/
  | reserved
  /-- its file created under the temporary name, being written -/
  | writing (i : Ino)
  /-- its file written whole and synced -/
  | synced (i : Ino)
  /-- its file moved to the final name -/
  | final (i : Ino)
  /-- the directory synced after the move: its file in place -/
  | placed (i : Ino)
  /-- refused with 441; its names are to be removed -/
  | refused

/-- An article in flight: the octets of its file, how many are written, and where it is. -/
structure Post where
  octets : Bytes
  written : Nat
  stage : Stage

/-- What the store's program keeps: the journal's key, its records synced, its file, the next
sequence number, the articles in flight by number, the commit whose record is appended and not yet
synced, whether it still accepts articles, whether no sync of the journal or the directory has
failed, and the number of this run of the store. -/
structure Prog where
  key : Bytes
  records : List Record
  journal : Ino
  next : Nat
  posts : Nat → Option Post
  committing : Option Commit
  accepting : Bool
  trusting : Bool
  run : Nat

/-- What the store's runs have done that a crash must not undo: the articles answered 240; the
commits whose records were appended, each with the run that appended it; the articles refused
with 441, each by its run and sequence number; and the octets written for each sequence number. -/
structure Hist where
  answered : List Commit
  appended : List (Nat × Commit)
  refused : List (Nat × Nat)
  files : Nat → Bytes

/-- The next `m` octets of an article to write. -/
def Post.chunk (x : Post) (m : Nat) : Bytes := (x.octets.drop x.written).take m

/-- The program with the article numbered `q` set. -/
def Prog.set (p : Prog) (q : Nat) (x : Option Post) : Prog :=
  { p with posts := fun n => if n = q then x else p.posts n }

/-- The record appended and not yet synced, if any. -/
def backOf (p : Prog) : List Record :=
  match p.committing with
  | some c => [.commit c]
  | none => []

/-- The spool as the store knows it, from its program and what its runs have done. -/
def viewOf (p : Prog) (h : Hist) : View :=
  ⟨.steady p.key p.records (backOf p), h.answered, h.appended.map Prod.snd, h.files, p.next⟩

/-- The commit record of `c` where the records `rs` under `k` end. -/
def commitFrame (k : Bytes) (rs : List Record) (c : Commit) : Bytes :=
  (Record.commit c).encode k (journal k rs).length

/-- What the program checks of a commit's groups before it appends the record: each one the store
carries, and the article number it allocates there above the last the records gave the group. -/
def Allocated (cfg : Config) (rs : List Record) (c : Commit) : Prop :=
  ∀ g ∈ c.groups, g.name ∈ cfg.groups ∧ highIn (commitsOf rs) g.name < g.number

/-- **A step of the store**: one operation of the file system, done or failed, or none, and what the
program and the run make of it. A step is one operation taking effect; the program learns how a
sync of the journal or the directory ended before the next sync of it begins. -/
inductive Step (cfg : Config) : Fs → Prog → Hist → Fs → Prog → Hist → Prop
  /-- a sequence number reserved for an article, while numbers last -/
  | reserve (s : Fs) (p : Prog) (h : Hist) (o : Bytes) (hr : p.next + 2 < 2 ^ 64) :
      Step cfg s p h s { p.set p.next (some ⟨o, 0, .reserved⟩) with next := p.next + 1 }
        { h with files := fun n => if n = p.next then o else h.files n }
  /-- its file created under the temporary name -/
  | create (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (hq : p.posts q = some x)
      (hs : x.stage = .reserved) :
      Step cfg s p h (s.step (.create (tempName q))).1
        (p.set q (some { x with written := 0, stage := .writing s.next })) h
  /-- part of the octets written -/
  | write (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (i : Ino) (m : Nat)
      (hq : p.posts q = some x) (hs : x.stage = .writing i) :
      Step cfg s p h (s.step (.append i (x.chunk m))).1
        (p.set q (some { x with written := x.written + (x.chunk m).length })) h
  /-- the file synced once written whole -/
  | sync (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (i : Ino) (hq : p.posts q = some x)
      (hs : x.stage = .writing i) (hw : x.written = x.octets.length) :
      Step cfg s p h (s.step (.sync i)).1 (p.set q (some { x with stage := .synced i })) h
  /-- the file moved to the final name -/
  | rename (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (i : Ino) (hq : p.posts q = some x)
      (hs : x.stage = .synced i) :
      Step cfg s p h (s.step (.rename (tempName q) (finalName q))).1
        (p.set q (some { x with stage := .final i })) h
  /-- the directory synced after the move, while no sync of the journal or the directory has
  failed -/
  | place (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (i : Ino) (hq : p.posts q = some x)
      (hs : x.stage = .final i) (ht : p.trusting = true) :
      Step cfg s p h (s.step .syncDir).1 (p.set q (some { x with stage := .placed i })) h
  /-- the article's commit record appended, one at a time, while it accepts: its own number, the
  size and CRC-32C of its file, a record the journal can hold, and its article numbers
  allocated -/
  | commit (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (i : Ino) (c : Commit)
      (hq : p.posts q = some x) (hs : x.stage = .placed i) (hc : p.committing = none)
      (ha : p.accepting = true) (hseq : c.seq = q) (hsize : c.fileSize = x.octets.length)
      (hcrc : (crc32c x.octets).toNat = c.fileCrc) (hok : (Record.commit c).ok = true)
      (hgroups : Allocated cfg p.records c) :
      Step cfg s p h (s.step (.append p.journal (commitFrame p.key p.records c))).1
        { p.set q none with committing := some c }
        { h with appended := h.appended ++ [(p.run, c)] }
  /-- the journal synced over it, while it accepts: 240 -/
  | publish (s : Fs) (p : Prog) (h : Hist) (c : Commit) (hc : p.committing = some c)
      (ha : p.accepting = true) :
      Step cfg s p h (s.step (.sync p.journal)).1
        { p with records := p.records ++ [.commit c], committing := none }
        { h with answered := h.answered ++ [c] }
  /-- an article refused with 441 before its record is written -/
  | refuse (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (hq : p.posts q = some x) :
      Step cfg s p h s (p.set q (some { x with stage := .refused }))
        { h with refused := h.refused ++ [(p.run, q)] }
  /-- a name of an article refused removed -/
  | clean (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (name : Bytes)
      (hq : p.posts q = some x) (hs : x.stage = .refused)
      (hn : name = tempName q ∨ name = finalName q) :
      Step cfg s p h (s.step (.remove name)).1 p h
  /-- an article refused forgotten -/
  | drop (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (hq : p.posts q = some x)
      (hs : x.stage = .refused) :
      Step cfg s p h s (p.set q none) h
  /-- a name opened, a file read or its size taken, the names listed -/
  | read (s : Fs) (p : Prog) (h : Hist) (op : Op)
      (hop : (∃ n, op = .open_ n) ∨ (∃ i o l, op = .read i o l) ∨ (∃ i, op = .size i) ∨
        op = .list) :
      Step cfg s p h (s.step op).1 p h
  /-- the create failed: the article refused -/
  | createFails (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (t : Fs)
      (hq : p.posts q = some x) (hs : x.stage = .reserved)
      (ht : s.Fails t (.create (tempName q))) :
      Step cfg s p h t (p.set q (some { x with stage := .refused }))
        { h with refused := h.refused ++ [(p.run, q)] }
  /-- a write failed: the article refused -/
  | writeFails (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (i : Ino) (m : Nat) (t : Fs)
      (hq : p.posts q = some x) (hs : x.stage = .writing i)
      (ht : s.Fails t (.append i (x.chunk m))) :
      Step cfg s p h t (p.set q (some { x with stage := .refused }))
        { h with refused := h.refused ++ [(p.run, q)] }
  /-- the file's sync failed: the article refused, and the store stops accepting -/
  | syncFails (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (i : Ino) (t : Fs)
      (hq : p.posts q = some x) (hs : x.stage = .writing i) (ht : s.Fails t (.sync i)) :
      Step cfg s p h t { p.set q (some { x with stage := .refused }) with accepting := false }
        { h with refused := h.refused ++ [(p.run, q)] }
  /-- the move failed: the article refused -/
  | renameFails (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (i : Ino) (t : Fs)
      (hq : p.posts q = some x) (hs : x.stage = .synced i)
      (ht : s.Fails t (.rename (tempName q) (finalName q))) :
      Step cfg s p h t (p.set q (some { x with stage := .refused }))
        { h with refused := h.refused ++ [(p.run, q)] }
  /-- the directory's sync failed: the article refused, the store stops accepting, and no later
  sync is trusted -/
  | placeFails (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (t : Fs)
      (hq : p.posts q = some x) (ht : s.Fails t .syncDir) :
      Step cfg s p h t
        { p.set q (some { x with stage := .refused }) with accepting := false, trusting := false }
        { h with refused := h.refused ++ [(p.run, q)] }
  /-- the record's write failed: its outcome unknown, the connection closed without an answer,
  and the store stops accepting -/
  | commitFails (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (i : Ino) (c : Commit)
      (t : Fs) (hq : p.posts q = some x) (hs : x.stage = .placed i) (hc : p.committing = none)
      (ha : p.accepting = true) (hseq : c.seq = q) (hsize : c.fileSize = x.octets.length)
      (hcrc : (crc32c x.octets).toNat = c.fileCrc) (hok : (Record.commit c).ok = true)
      (hgroups : Allocated cfg p.records c)
      (ht : s.Fails t (.append p.journal (commitFrame p.key p.records c))) :
      Step cfg s p h t { p.set q none with committing := some c, accepting := false }
        { h with appended := h.appended ++ [(p.run, c)] }
  /-- the journal's sync failed: the outcome unknown, the store stops accepting, and no later
  sync is trusted -/
  | publishFails (s : Fs) (p : Prog) (h : Hist) (t : Fs) (ht : s.Fails t (.sync p.journal)) :
      Step cfg s p h t { p with accepting := false, trusting := false } h
  /-- a removal failed -/
  | cleanFails (s : Fs) (p : Prog) (h : Hist) (q : Nat) (x : Post) (name : Bytes) (t : Fs)
      (hq : p.posts q = some x) (hs : x.stage = .refused)
      (hn : name = tempName q ∨ name = finalName q) (ht : s.Fails t (.remove name)) :
      Step cfg s p h t p h

/-! ## What the store keeps -/

/-- No name but the article's own two may be left holding file `i`. -/
def Owns (s : Fs) (q : Nat) (i : Ino) : Prop :=
  ∀ e ∈ s.dir, e.Leaves (some i) → e.name = tempName q ∨ e.name = finalName q

/-- What the spool holds of an article in flight, by where it is. -/
def PostHolds (s : Fs) (q : Nat) (x : Post) : Prop :=
  match x.stage with
  | .reserved => ∀ e ∈ s.dir, e.name ≠ tempName q ∧ e.name ≠ finalName q
  | .writing i => s.lookup (tempName q) = some i ∧ (∀ e ∈ s.dir, e.name ≠ finalName q) ∧
      Owns s q i ∧ x.written ≤ x.octets.length ∧
      ∃ d, s.data i = some d ∧ d.seen = x.octets.take x.written ∧ d.trusted = true
  | .synced i => s.lookup (tempName q) = some i ∧ (∀ e ∈ s.dir, e.name ≠ finalName q) ∧
      Owns s q i ∧ ∃ d, s.data i = some d ∧ d.seen = x.octets ∧ d.kept = d.seen ∧
        d.high = d.seen.length
  | .final i => s.lookup (finalName q) = some i ∧ Owns s q i ∧
      ∃ d, s.data i = some d ∧ d.seen = x.octets ∧ d.kept = d.seen ∧ d.high = d.seen.length
  | .placed i => s.entry (finalName q) = some ⟨finalName q, some i, []⟩ ∧ Owns s q i ∧
      ∃ d, s.data i = some d ∧ d.seen = x.octets ∧ d.kept = d.seen ∧ d.high = d.seen.length
  | .refused => True

/-- **The store running**: a spool whose journal holds the records the program keeps and, past
them, the record appended and not yet synced, if any; the journal's name settled; the syncs of the
journal and the directory trusted while none of them has failed, and none failed while it accepts;
while it accepts, the journal synced over its records with nothing appended past them, or holding
the record in flight whole; every article in flight numbered below the next number and apart from
the commits in place, its octets those written for it, its file as its stage says; and no commit
appended by an article refused — this run's refused numbers below the next one and never
committed, this run's committed numbers below it and no longer in flight. -/
structure Running (cfg : Config) (s : Fs) (p : Prog) (h : Hist) : Prop where
  spool : Spool cfg s (viewOf p h)
  lookup : s.lookup journalName = some p.journal
  settled : ¬ Unsettled s
  trusted : p.trusting = true → Trusted s
  accepts : p.accepting = true → p.trusting = true
  synced : p.accepting = true → p.committing = none → ∃ d, s.data p.journal = some d ∧
    d.seen = journal p.key p.records ∧ d.high = d.seen.length ∧ Fresh p.key p.records d
  inFlight : ∀ c, p.committing = some c → (Record.commit c).ok = true ∧
    (p.accepting = true → ∃ d, s.data p.journal = some d ∧
      d.seen = journal p.key p.records ++ commitFrame p.key p.records c)
  posts : ∀ q x, p.posts q = some x → q < p.next ∧ (∀ c ∈ placedSet (viewOf p h), c.seq ≠ q) ∧
    (x.stage ≠ .refused → h.files q = x.octets) ∧ PostHolds s q x
  apart : ∀ r c, (r, c) ∈ h.appended → (r, c.seq) ∉ h.refused
  past : ∀ r q, ((r, q) ∈ h.refused ∨ ∃ c, (r, c) ∈ h.appended ∧ c.seq = q) → r ≤ p.run
  runRefused : ∀ q, (p.run, q) ∈ h.refused → q < p.next ∧ ∀ x, p.posts q = some x →
    x.stage = .refused
  runAppended : ∀ c, (p.run, c) ∈ h.appended → c.seq < p.next ∧ p.posts c.seq = none

/-! ## A started store runs -/

/-- **A store started by recovery runs**, with no article in flight, in a run numbered above every
run the history names. -/
theorem running_started (cfg : Config) (st : Store) (s : Fs) (h : Hist) (r : Nat)
    (hs : Started cfg ⟨.none, h.answered, h.appended.map Prod.snd, h.files, 0⟩ st s)
    (hapart : ∀ r' c, (r', c) ∈ h.appended → (r', c.seq) ∉ h.refused)
    (hpast : ∀ r' q, ((r', q) ∈ h.refused ∨ ∃ c, (r', c) ∈ h.appended ∧ c.seq = q) → r' < r) :
    ∃ rs ij, commitsOf rs = st.articles ∧ st.journalEnd = (journal st.key rs).length ∧
      Running cfg s ⟨st.key, rs ++ [.start], ij, st.next, fun _ => none, none, true, true, r⟩
        h := by
  obtain ⟨rs, ij, d, hsp, harts, hend, hl, hd, hseen, hh, ht, hfr, htd, hset⟩ := hs
  refine ⟨rs, ij, harts, hend, hsp, hl, settled_journal s hset ij hl,
    (fun _ => ⟨htd, fun i d' hi hd' => ?_⟩), (fun _ => rfl), (fun _ _ => ⟨d, hd, hseen, hh, hfr⟩),
    (fun c hc => by cases hc), (fun q x hx => by cases hx), hapart,
    (fun r' q hq => Nat.le_of_lt (hpast r' q hq)),
    (fun q hq => absurd (hpast r q (Or.inl hq)) (Nat.lt_irrefl _)),
    (fun c hc => absurd (hpast r c.seq (Or.inr ⟨c, hc, rfl⟩)) (Nat.lt_irrefl _))⟩
  rw [hl] at hi; cases hi; rw [hd] at hd'; cases hd'; exact ht

/-! ## Names and files of articles in flight -/

theorem tempName_inj (m q : Nat) (hm : m < 2 ^ 64) (hq : q < 2 ^ 64)
    (h : tempName m = tempName q) : m = q := by
  have h1 := parseName_bytes (.temp m) (by simp [Name.valid, hm])
  have h2 := parseName_bytes (.temp q) (by simp [Name.valid, hq])
  simp only [Name.bytes] at h1 h2
  rw [h, h2] at h1
  simp only [Option.some.injEq, Name.temp.injEq] at h1
  exact h1.symm

theorem finalName_inj (m q : Nat) (hm : m < 2 ^ 64) (hq : q < 2 ^ 64)
    (h : finalName m = finalName q) : m = q := by
  have h1 := parseName_bytes (.final m) (by simp [Name.valid, hm])
  have h2 := parseName_bytes (.final q) (by simp [Name.valid, hq])
  simp only [Name.bytes] at h1 h2
  rw [h, h2] at h1
  simp only [Option.some.injEq, Name.final.injEq] at h1
  exact h1.symm

/-- The two names of an article are no other's. -/
theorem names_apart (m q : Nat) (hm : m < 2 ^ 64) (hq : q < 2 ^ 64) (hmq : m ≠ q) (name : Bytes)
    (h : name = tempName m ∨ name = finalName m) : name ≠ tempName q ∧ name ≠ finalName q := by
  rcases h with rfl | rfl
  · exact ⟨fun e => hmq (tempName_inj m q hm hq e), fun e => final_ne_temp q m e.symm⟩
  · exact ⟨fun e => final_ne_temp m q e, fun e => hmq (finalName_inj m q hm hq e)⟩

/-- The file an article in flight has, once it has one. -/
def Stage.inode : Stage → Option Ino
  | .writing i | .synced i | .final i | .placed i => some i
  | _ => none

/-- A name that holds a file only an article's names may hold is one of them. -/
theorem owns_lookup (s : Fs) (q : Nat) (i : Ino) (h : Owns s q i) (name : Bytes)
    (hl : s.lookup name = some i) : name = tempName q ∨ name = finalName q := by
  obtain ⟨e, he, hle⟩ := lookup_leaves s name i hl
  rw [← entry_name s name e he]
  exact h e (List.mem_of_find?_eq_some he) hle

/-- **What the spool holds of an article stays** through a change that leaves its two names as they
were, makes no new name of them, gives no name its file, and leaves its file's data. -/
theorem holds_frame (s u : Fs) (q : Nat) (x : Post) (h : PostHolds s q x)
    (hent : ∀ m, m = tempName q ∨ m = finalName q → u.entry m = s.entry m)
    (hnames : ∀ e ∈ u.dir, e.name = tempName q ∨ e.name = finalName q → ∃ e₀ ∈ s.dir,
      e₀.name = e.name)
    (hown : ∀ i, x.stage.inode = some i → ∀ e ∈ u.dir, e.Leaves (some i) →
      ∃ e₀ ∈ s.dir, e₀.name = e.name ∧ e₀.Leaves (some i))
    (hdata : ∀ i, x.stage.inode = some i → u.data i = s.data i) : PostHolds u q x := by
  have hlk : ∀ m, m = tempName q ∨ m = finalName q → u.lookup m = s.lookup m := by
    intro m hm; simp only [Fs.lookup, hent m hm]
  have hno : ∀ m, (∀ e ∈ s.dir, e.name ≠ m) → m = tempName q ∨ m = finalName q →
      ∀ e ∈ u.dir, e.name ≠ m := by
    intro m hm hq e he hen
    obtain ⟨e₀, he₀, hn₀⟩ := hnames e he (hen ▸ hq)
    exact hm e₀ he₀ (hn₀.trans hen)
  have howns : ∀ i, x.stage.inode = some i → Owns s q i → Owns u q i := by
    intro i hi ho e he hl
    obtain ⟨e₀, he₀, hn₀, hl₀⟩ := hown i hi e he hl
    rw [← hn₀]
    exact ho e₀ he₀ hl₀
  unfold PostHolds at h ⊢
  cases hs : x.stage with
  | reserved =>
    rw [hs] at h
    intro e he
    exact ⟨hno _ (fun e₀ he₀ => (h e₀ he₀).1) (Or.inl rfl) e he,
      hno _ (fun e₀ he₀ => (h e₀ he₀).2) (Or.inr rfl) e he⟩
  | writing i =>
    rw [hs] at h
    obtain ⟨hl, hf, ho, hw, d, hd, hseen, ht⟩ := h
    exact ⟨by rw [hlk _ (Or.inl rfl)]; exact hl, hno _ hf (Or.inr rfl),
      howns i (by rw [hs]; rfl) ho,
      hw, d, by rw [hdata i (by rw [hs]; rfl)]; exact hd, hseen, ht⟩
  | synced i =>
    rw [hs] at h
    obtain ⟨hl, hf, ho, d, hd, hrest⟩ := h
    exact ⟨by rw [hlk _ (Or.inl rfl)]; exact hl, hno _ hf (Or.inr rfl),
      howns i (by rw [hs]; rfl) ho,
      d, by rw [hdata i (by rw [hs]; rfl)]; exact hd, hrest⟩
  | final i =>
    rw [hs] at h
    obtain ⟨hl, ho, d, hd, hrest⟩ := h
    exact ⟨by rw [hlk _ (Or.inr rfl)]; exact hl, howns i (by rw [hs]; rfl) ho, d,
      by rw [hdata i (by rw [hs]; rfl)]; exact hd, hrest⟩
  | placed i =>
    rw [hs] at h
    obtain ⟨he, ho, d, hd, hrest⟩ := h
    exact ⟨by rw [hent _ (Or.inr rfl)]; exact he, howns i (by rw [hs]; rfl) ho, d,
      by rw [hdata i (by rw [hs]; rfl)]; exact hd, hrest⟩
  | refused => trivial

/-- What the spool holds of an article stays through a sync of the directory. -/
theorem holds_syncDir (s : Fs) (hs : s.Ok) (q : Nat) (x : Post) (h : PostHolds s q x) :
    PostHolds (s.step .syncDir).1 q x := by
  by_cases ht : s.dirTrusted = true
  · have hdir : (s.step .syncDir).1.dir = s.dir.filterMap Entry.settle := by
      simp [Fs.step, ht]
    have hmem : ∀ e' ∈ (s.step .syncDir).1.dir, ∃ e ∈ s.dir, e.name = e'.name ∧
        ∀ b, e'.Leaves b → b = e.seen := by
      intro e' he'
      rw [hdir] at he'
      obtain ⟨e, he, hse⟩ := List.mem_filterMap.mp he'
      refine ⟨e, he, ?_, fun b hb => (FsModel.settle_leaves e e' hse b).mp hb⟩
      simp only [Entry.settle, Option.map_eq_some_iff] at hse
      obtain ⟨_, _, rfl⟩ := hse
      rfl
    have hlk : ∀ m, (s.step .syncDir).1.lookup m = s.lookup m := syncDir_lookup s hs
    have hno : ∀ m, (∀ e ∈ s.dir, e.name ≠ m) → ∀ e ∈ (s.step .syncDir).1.dir, e.name ≠ m := by
      intro m hm e he hen
      obtain ⟨e₀, he₀, hn₀, _⟩ := hmem e he
      exact hm e₀ he₀ (hn₀.trans hen)
    have howns : ∀ i, Owns s q i → Owns (s.step .syncDir).1 q i := by
      intro i ho e he hl
      obtain ⟨e₀, he₀, hn₀, hL⟩ := hmem e he
      rw [← hn₀]
      exact ho e₀ he₀ (hL _ hl ▸ FsModel.entry_leaves_seen e₀)
    have hdata : ∀ i, (s.step .syncDir).1.data i = s.data i := fun i => by rw [syncDir_data]
    unfold PostHolds at h ⊢
    cases hst : x.stage with
    | reserved =>
      rw [hst] at h
      intro e he
      exact ⟨hno _ (fun e₀ he₀ => (h e₀ he₀).1) e he, hno _ (fun e₀ he₀ => (h e₀ he₀).2) e he⟩
    | writing i =>
      rw [hst] at h
      obtain ⟨hl, hf, ho, hw, d, hd, hrest⟩ := h
      exact ⟨by rw [hlk]; exact hl, hno _ hf, howns i ho, hw, d, by rw [hdata]; exact hd, hrest⟩
    | synced i =>
      rw [hst] at h
      obtain ⟨hl, hf, ho, d, hd, hrest⟩ := h
      exact ⟨by rw [hlk]; exact hl, hno _ hf, howns i ho, d, by rw [hdata]; exact hd, hrest⟩
    | final i =>
      rw [hst] at h
      obtain ⟨hl, ho, d, hd, hrest⟩ := h
      exact ⟨by rw [hlk]; exact hl, howns i ho, d, by rw [hdata]; exact hd, hrest⟩
    | placed i =>
      rw [hst] at h
      obtain ⟨he, ho, d, hd, hrest⟩ := h
      refine ⟨?_, howns i ho, d, by rw [hdata]; exact hd, hrest⟩
      simp only [Fs.step, ht, ↓reduceIte, Fs.entry]
      rw [entry_settle s hs, he]
      rfl
    | refused => trivial
  · have : (s.step .syncDir).1 = s := by simp [Fs.step, ht]
    rw [this]; exact h

theorem holds_owns (s : Fs) (q : Nat) (x : Post) (h : PostHolds s q x) (i : Ino)
    (hi : x.stage.inode = some i) : Owns s q i := by
  unfold PostHolds at h
  cases hs : x.stage with
  | writing j => rw [hs] at h hi; cases hi; exact h.2.2.1
  | synced j => rw [hs] at h hi; cases hi; exact h.2.2.1
  | final j => rw [hs] at h hi; cases hi; exact h.2.1
  | placed j => rw [hs] at h hi; cases hi; exact h.2.1
  | reserved => rw [hs] at hi; cases hi
  | refused => rw [hs] at hi; cases hi

/-- The file an article in flight has is held by one of its names. -/
theorem holds_lookup (s : Fs) (q : Nat) (x : Post) (h : PostHolds s q x) (i : Ino)
    (hi : x.stage.inode = some i) :
    s.lookup (tempName q) = some i ∨ s.lookup (finalName q) = some i := by
  unfold PostHolds at h
  cases hs : x.stage with
  | writing j => rw [hs] at h hi; cases hi; exact Or.inl h.1
  | synced j => rw [hs] at h hi; cases hi; exact Or.inl h.1
  | final j => rw [hs] at h hi; cases hi; exact Or.inr h.1
  | placed j =>
    rw [hs] at h hi; cases hi; exact Or.inr (by simp [Fs.lookup, h.1, Entry.seen])
  | reserved => rw [hs] at hi; cases hi
  | refused => rw [hs] at hi; cases hi

/-- An article's file is not one a name other than its own holds. -/
theorem apart_of_lookup (s : Fs) (q : Nat) (x : Post) (h : PostHolds s q x) (name : Bytes)
    (j : Ino) (hl : s.lookup name = some j) (hn : name ≠ tempName q ∧ name ≠ finalName q) :
    ∀ i, x.stage.inode = some i → i ≠ j := by
  intro i hi hij
  subst hij
  rcases owns_lookup s q i (holds_owns s q x h i hi) name hl with he | he
  · exact hn.1 he
  · exact hn.2 he

/-- What the spool holds of an article stays through an operation on another file. -/
theorem holds_onData (s : Fs) (q : Nat) (x : Post) (h : PostHolds s q x) (j : Ino)
    (f : Data → Data) (hj : ∀ i, x.stage.inode = some i → i ≠ j) :
    PostHolds (s.onData j f).1 q x :=
  holds_frame s _ q x h (fun m _ => by rw [onData_entry])
    (fun e he _ => ⟨e, by rw [FsModel.onData_dir] at he; exact he, rfl⟩)
    (fun i _ e he hl => ⟨e, by rw [FsModel.onData_dir] at he; exact he, rfl, hl⟩)
    (fun i hi => by rw [data_onData, if_neg (hj i hi)])

/-- What the spool holds of an article stays when a name not its own comes to hold nothing, or a
file not its own. -/
theorem holds_rebind (s : Fs) (q : Nat) (x : Post) (h : PostHolds s q x) (name : Bytes)
    (b : Option Ino) (hn : name ≠ tempName q ∧ name ≠ finalName q)
    (hb : ∀ i, x.stage.inode = some i → b ≠ some i) :
    PostHolds { s with dir := rebind s.dir name b } q x :=
  holds_frame s _ q x h
    (fun m hm => entry_other s name m b (by
      rcases hm with rfl | rfl
      · exact fun e => hn.1 e.symm
      · exact fun e => hn.2 e.symm))
    (fun e he hq => by
      rcases rebind_names s.dir name b e he with he' | he'
      · rcases hq with hq | hq
        · exact absurd (he'.symm.trans hq) hn.1
        · exact absurd (he'.symm.trans hq) hn.2
      · exact he')
    (fun i hi e he hl => by
      rcases rebind_leaves s.dir name b e he i hl with ⟨_, hbi⟩ | he'
      · exact absurd hbi.symm (hb i hi)
      · exact he')
    (fun _ _ => rfl)

/-- **The articles in flight stay as the store keeps them** through a step that touches at most
the article numbered `q`, given what holds of that one. -/
theorem posts_keep (cfg : Config) (s s' : Fs) (p p' : Prog) (h h' : Hist) (q : Nat)
    (hr : Running cfg s p h) (hnext : p.next ≤ p'.next)
    (hplaced : ∀ c ∈ placedSet (viewOf p' h'), c ∈ placedSet (viewOf p h) ∨ c.seq = q)
    (hfiles : ∀ n, n ≠ q → h'.files n = h.files n)
    (hothers : ∀ n, n ≠ q → p'.posts n = p.posts n)
    (hholds : ∀ n x, n ≠ q → p.posts n = some x → PostHolds s n x → PostHolds s' n x)
    (hq : ∀ x, p'.posts q = some x → q < p'.next ∧
      (∀ c ∈ placedSet (viewOf p' h'), c.seq ≠ q) ∧
      (x.stage ≠ .refused → h'.files q = x.octets) ∧ PostHolds s' q x) :
    ∀ n x, p'.posts n = some x → n < p'.next ∧ (∀ c ∈ placedSet (viewOf p' h'), c.seq ≠ n) ∧
      (x.stage ≠ .refused → h'.files n = x.octets) ∧ PostHolds s' n x := by
  intro n x hx
  by_cases hnq : n = q
  · subst hnq; exact hq x hx
  · rw [hothers n hnq] at hx
    obtain ⟨hlt, hpl, hf, hh⟩ := hr.posts n x hx
    refine ⟨Nat.lt_of_lt_of_le hlt hnext, fun c hc => ?_, fun hs => by
      rw [hfiles n hnq]; exact hf hs, hholds n x hnq hx hh⟩
    rcases hplaced c hc with hc | hc
    · exact hpl c hc
    · rw [hc]; exact Ne.symm hnq

theorem room_of (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h) :
    p.next + 1 < 2 ^ 64 := hr.spool.room.2

theorem seq_lt (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h) (q : Nat)
    (x : Post) (hx : p.posts q = some x) : q < 2 ^ 64 := by
  have := (hr.posts q x hx).1
  have := room_of cfg s p h hr
  omega

theorem placed_lt (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (c : Commit) (hc : c ∈ placedSet (viewOf p h)) : c.seq < 2 ^ 64 := by
  have := hr.spool.seqs c hc
  have := room_of cfg s p h hr
  simp only [viewOf] at *
  omega

/-- The articles in flight stay as the store keeps them through a step that touches none of
them. -/
theorem posts_all (cfg : Config) (s s' : Fs) (p p' : Prog) (h h' : Hist)
    (hr : Running cfg s p h) (hnext : p.next ≤ p'.next)
    (hplaced : ∀ c ∈ placedSet (viewOf p' h'), c ∈ placedSet (viewOf p h))
    (hfiles : h'.files = h.files) (hposts : p'.posts = p.posts)
    (hholds : ∀ n x, p.posts n = some x → PostHolds s n x → PostHolds s' n x) :
    ∀ n x, p'.posts n = some x → n < p'.next ∧ (∀ c ∈ placedSet (viewOf p' h'), c.seq ≠ n) ∧
      (x.stage ≠ .refused → h'.files n = x.octets) ∧ PostHolds s' n x := by
  intro n x hx
  rw [hposts] at hx
  obtain ⟨hlt, hpl, hf, hh⟩ := hr.posts n x hx
  exact ⟨Nat.lt_of_lt_of_le hlt hnext, fun c hc => hpl c (hplaced c hc),
    fun hs => by rw [hfiles]; exact hf hs, hholds n x hx hh⟩

/-- This run's attempts stay as the store keeps them when an article in flight changes: refused
numbers stay refused, committed ones out of flight. -/
theorem attempts_set (p : Prog) (h : Hist) (q : Nat) (x : Post) (hq : p.posts q = some x)
    (hrr : ∀ q', (p.run, q') ∈ h.refused → q' < p.next ∧ ∀ x', p.posts q' = some x' →
      x'.stage = .refused)
    (hra : ∀ c, (p.run, c) ∈ h.appended → c.seq < p.next ∧ p.posts c.seq = none)
    (y : Option Post) (hy : (p.run, q) ∈ h.refused → ∀ x', y = some x' → x'.stage = .refused) :
    (∀ q', (p.run, q') ∈ h.refused → q' < p.next ∧ ∀ x', (p.set q y).posts q' = some x' →
      x'.stage = .refused) ∧
    (∀ c, (p.run, c) ∈ h.appended → c.seq < p.next ∧ (p.set q y).posts c.seq = none) := by
  refine ⟨fun q' hq' => ⟨(hrr q' hq').1, fun x' hx' => ?_⟩, fun c hc => ⟨(hra c hc).1, ?_⟩⟩
  · simp only [Prog.set] at hx'
    split at hx'
    · rename_i he; subst he; exact hy hq' x' hx'
    · exact (hrr q' hq').2 x' hx'
  · have hne : c.seq ≠ q := fun he => by
      have := (hra c hc).2; rw [he, hq] at this; cases this
    simp only [Prog.set, if_neg hne]
    exact (hra c hc).2

/-- An article in flight not refused is no refused number of this run. -/
theorem live_not_refused (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (hq : p.posts q = some x) (hx : x.stage ≠ .refused) :
    (p.run, q) ∉ h.refused := fun hm => hx ((hr.runRefused q hm).2 x hq)

/-! ## Steps that change no file -/

/-- An article in flight marked refused, or forgotten once refused. -/
theorem running_forget (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x₀ : Post) (hq : p.posts q = some x₀) (y : Option Post)
    (hy : ∀ x, y = some x → x.stage = .refused) : Running cfg s (p.set q y) h := by
  obtain ⟨hlt, hpl, _, _⟩ := hr.posts q x₀ hq
  obtain ⟨hrr, hra⟩ := attempts_set p h q x₀ hq hr.runRefused hr.runAppended y
    (fun _ x hx => hy x hx)
  refine ⟨hr.spool, hr.lookup, hr.settled, hr.trusted, hr.accepts, hr.synced, hr.inFlight,
    posts_keep cfg s s p (p.set q y) h h q hr (Nat.le_refl _) (fun c hc => Or.inl hc)
      (fun _ _ => rfl) (fun n hn => by simp [Prog.set, hn]) (fun _ _ _ _ hh => hh)
      (fun x hx => ?_), hr.apart, hr.past, hrr, hra⟩
  simp only [Prog.set, ↓reduceIte] at hx
  have hs := hy x hx
  refine ⟨hlt, hpl, fun h' => absurd hs h', ?_⟩
  unfold PostHolds
  rw [hs]
  trivial

/-- **An article refused with 441**, the refusal recorded by its run and number. -/
theorem running_record (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (hq : p.posts q = some x) (hs : x.stage = .refused) :
    Running cfg s p { h with refused := h.refused ++ [(p.run, q)] } := by
  refine ⟨hr.spool, hr.lookup, hr.settled, hr.trusted, hr.accepts, hr.synced, hr.inFlight,
    hr.posts, fun r c hc hm => ?_, fun r q' hq' => ?_, fun q' hq' => ?_, hr.runAppended⟩
  · rcases List.mem_append.mp hm with hm | hm
    · exact hr.apart r c hc hm
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, he⟩ := hm
      have := (hr.runAppended c hc).2
      rw [he, hq] at this
      cases this
  · rcases hq' with hq' | hq'
    · rcases List.mem_append.mp hq' with hq' | hq'
      · exact hr.past r q' (Or.inl hq')
      · simp only [List.mem_singleton, Prod.mk.injEq] at hq'
        rw [hq'.1]; exact Nat.le_refl _
    · exact hr.past r q' (Or.inr hq')
  · rcases List.mem_append.mp hq' with hq' | hq'
    · exact hr.runRefused q' hq'
    · simp only [List.mem_singleton, Prod.mk.injEq] at hq'
      obtain ⟨_, rfl⟩ := hq'
      exact ⟨(hr.posts _ x hq).1, fun x' hx' => by rw [hq] at hx'; cases hx'; exact hs⟩

/-- **An article refused with 441** in flight. -/
theorem running_refuse (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (hq : p.posts q = some x) :
    Running cfg s (p.set q (some { x with stage := .refused }))
      { h with refused := h.refused ++ [(p.run, q)] } :=
  running_record cfg s _ h (running_forget cfg s p h hr q x hq _ fun z hz => by cases hz; rfl) q
    { x with stage := .refused } (by simp [Prog.set]) rfl

/-- **The journal as the store keeps it stays** through a change that leaves the journal's entry,
its file's data and whether the directory's syncs are trusted, while the program keeps its
journal. -/
theorem journal_keep (cfg : Config) (s s' : Fs) (p p' : Prog) (h : Hist) (hr : Running cfg s p h)
    (he : s'.entry journalName = s.entry journalName) (hd : s'.data p.journal = s.data p.journal)
    (hdt : p'.trusting = true → s'.dirTrusted = s.dirTrusted)
    (hk : p'.key = p.key) (hrec : p'.records = p.records) (hj : p'.journal = p.journal)
    (hc : p'.committing = p.committing) (ha : p'.accepting = true → p.accepting = true)
    (htr : p'.trusting = true → p.trusting = true) :
    s'.lookup journalName = some p'.journal ∧ ¬ Unsettled s' ∧
      (p'.trusting = true → Trusted s') ∧
      (p'.accepting = true → p'.committing = none → ∃ d, s'.data p'.journal = some d ∧
        d.seen = journal p'.key p'.records ∧ d.high = d.seen.length ∧ Fresh p'.key p'.records d) ∧
      (∀ c, p'.committing = some c → (Record.commit c).ok = true ∧
        (p'.accepting = true → ∃ d, s'.data p'.journal = some d ∧
          d.seen = journal p'.key p'.records ++ commitFrame p'.key p'.records c)) := by
  have hl : s'.lookup journalName = some p'.journal := by
    simp only [Fs.lookup, he, hj]; exact hr.lookup
  rw [hk, hrec, hj, hc]
  refine ⟨by rw [← hj]; exact hl, fun hu => hr.settled (by
      unfold Unsettled at hu ⊢; rw [he] at hu; exact hu), fun htr' => ?_,
    fun hacc hcn => by rw [hd]; exact hr.synced (ha hacc) hcn,
    fun c hcc => ⟨(hr.inFlight c hcc).1, fun hacc => by
      rw [hd]; exact (hr.inFlight c hcc).2 (ha hacc)⟩⟩
  obtain ⟨htd, htj⟩ := hr.trusted (htr htr')
  refine ⟨by rw [hdt htr']; exact htd, fun i d hi hd' => ?_⟩
  rw [hj] at hl
  rw [hl] at hi
  cases hi
  rw [hd] at hd'
  exact htj _ d hr.lookup hd'

/-- A removal leaves the file system as it was, or the name holding nothing. -/
theorem remove_cases (s : Fs) (name : Bytes) :
    (s.step (.remove name)).1 = s ∨
      (s.step (.remove name)).1 = { s with dir := rebind s.dir name none } := by
  simp only [Fs.step]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- What the spool holds of an article stays through a new file under a name not its own. -/
theorem holds_create (s : Fs) (hs : s.Ok) (q : Nat) (x : Post) (h : PostHolds s q x)
    (name : Bytes) (hfree : s.lookup name = none) (hn : name ≠ tempName q ∧ name ≠ finalName q) :
    PostHolds (s.step (.create name)).1 q x := by
  rw [create_eq s name hfree]
  have hheld : ∀ i, x.stage.inode = some i → ∃ d, i < s.next ∧ s.data i = some d := by
    intro i hi
    rcases holds_lookup s q x h i hi with hl | hl
    · exact ⟨_, held_below s hs _ _ hl, (data_some s hs _ _ hl).choose_spec⟩
    · exact ⟨_, held_below s hs _ _ hl, (data_some s hs _ _ hl).choose_spec⟩
  refine holds_frame s _ q x h
    (fun m hm => entry_other s name m _ (by
      rcases hm with rfl | rfl
      · exact fun e => hn.1 e.symm
      · exact fun e => hn.2 e.symm))
    (fun e he hq => by
      rcases rebind_names s.dir name _ e he with he' | he'
      · rcases hq with hq | hq
        · exact absurd (he'.symm.trans hq) hn.1
        · exact absurd (he'.symm.trans hq) hn.2
      · exact he')
    (fun i hi e he hl => by
      rcases rebind_leaves s.dir name _ e he i hl with ⟨_, hbi⟩ | he'
      · obtain ⟨_, hlt, _⟩ := hheld i hi
        rw [Option.some.inj hbi] at hlt
        exact absurd hlt (Nat.lt_irrefl _)
      · exact he')
    (fun i hi => ?_)
  obtain ⟨d, _, hd⟩ := hheld i hi
  show (s.files ++ _).lookup i = s.files.lookup i
  rw [lookup_append_new _ _ _ _ hd]
  exact hd.symm

/-- A name opened, a file read or its size taken, the names listed. -/
theorem running_read (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (op : Op) (hop : (∃ n, op = .open_ n) ∨ (∃ i o l, op = .read i o l) ∨ (∃ i, op = .size i) ∨
      op = .list) : Running cfg (s.step op).1 p h := by
  rw [step_pure s op hop]; exact hr

/-- A name of an article refused removed, or its removal failed. -/
theorem running_clean (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (hq : p.posts q = some x) (hs : x.stage = .refused) (name : Bytes)
    (hn : name = tempName q ∨ name = finalName q) (t : Fs)
    (ht : t = s ∨ t = (s.step (.remove name)).1) : Running cfg t p h := by
  rcases ht with rfl | rfl
  · exact hr
  have hq64 := seq_lt cfg s p h hr q x hq
  have hj : name ≠ journalName := by
    rcases hn with rfl | rfl
    · exact temp_ne_journal q
    · exact final_ne_journal q
  have hsp := spool_remove cfg s _ hr.spool name hj fun c hc e => by
    have hcq := (hr.posts q x hq).2.1 c hc
    rcases hn with rfl | rfl
    · exact final_ne_temp _ _ e
    · exact hcq (finalName_inj _ _ (placed_lt cfg s p h hr c hc) hq64 e)
  obtain ⟨he, hf, hdt⟩ := other_journal s (.remove name) (Or.inl ⟨name, rfl, hj⟩)
  obtain ⟨hl, hu, htr, hsy, hin⟩ := journal_keep cfg s _ p p h hr he
    (by simp only [Fs.data, hf]) (fun _ => hdt) rfl rfl rfl rfl id id
  refine ⟨hsp, hl, hu, htr, hr.accepts, hsy, hin, posts_keep cfg s _ p p h h q hr (Nat.le_refl _)
    (fun c hc => Or.inl hc) (fun _ _ => rfl) (fun _ _ => rfl) (fun n y hnq hy hh => ?_)
    (fun y hy => by
      rw [hq] at hy; cases hy
      obtain ⟨hlt, hpl, hf', _⟩ := hr.posts q x hq
      exact ⟨hlt, hpl, hf', by unfold PostHolds; rw [hs]; trivial⟩),
    hr.apart, hr.past, hr.runRefused, hr.runAppended⟩
  have hapart := names_apart q n hq64 (seq_lt cfg s p h hr n y hy) (Ne.symm hnq) name hn
  rcases remove_cases s name with h' | h'
  · rw [h']; exact hh
  · rw [h']; exact holds_rebind s n y hh name none hapart (fun _ _ h => by cases h)

/-- **A sequence number reserved** for an article, while numbers last. -/
theorem running_reserve (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (o : Bytes) (hroom : p.next + 2 < 2 ^ 64) :
    Running cfg s { p.set p.next (some ⟨o, 0, .reserved⟩) with next := p.next + 1 }
      { h with files := fun n => if n = p.next then o else h.files n } := by
  have hlt : ∀ c ∈ placedSet (viewOf p h), c.seq ≠ p.next := fun c hc => by
    have := hr.spool.seqs c hc; simp only [viewOf] at this; omega
  have hsp := spool_files cfg s _ (spool_next cfg s _ hr.spool (p.next + 1)
    (by simp [viewOf]) (by omega)) p.next o hlt
  refine ⟨hsp, hr.lookup, hr.settled, hr.trusted, hr.accepts, hr.synced, hr.inFlight,
    posts_keep cfg s s p _ h _ p.next hr (Nat.le_succ _) (fun c hc => Or.inl hc)
      (fun n hn => by simp [hn]) (fun n hn => by simp [Prog.set, hn])
      (fun _ _ _ _ hh => hh) (fun x hx => ?_), hr.apart, hr.past, fun q hq => ?_, fun c hc => ?_⟩
  · simp only [Prog.set, ↓reduceIte, Option.some.injEq] at hx
    subst hx
    refine ⟨Nat.lt_succ_self _, hlt, fun _ => by simp, ?_⟩
    unfold PostHolds
    have hv : p.next < 2 ^ 64 := by have := room_of cfg s p h hr; omega
    intro e he
    obtain ⟨m, hm, hseq⟩ := hr.spool.names e he
    refine ⟨fun hen => ?_, fun hen => ?_⟩
    · rw [hen, show tempName p.next = (Name.temp p.next).bytes from rfl,
        parseName_bytes _ (by simp [Name.valid, hv])] at hm
      cases hm
      exact Nat.lt_irrefl _ (hseq p.next rfl)
    · rw [hen, show finalName p.next = (Name.final p.next).bytes from rfl,
        parseName_bytes _ (by simp [Name.valid, hv])] at hm
      cases hm
      exact Nat.lt_irrefl _ (hseq p.next rfl)
  · obtain ⟨hlt', hpq⟩ := hr.runRefused q hq
    have hne : q ≠ p.next := Nat.ne_of_lt hlt'
    exact ⟨Nat.lt_succ_of_lt hlt', fun x hx => hpq x (by simpa [Prog.set, hne] using hx)⟩
  · obtain ⟨hlt', hpq⟩ := hr.runAppended c hc
    have hne : c.seq ≠ p.next := Nat.ne_of_lt hlt'
    exact ⟨Nat.lt_succ_of_lt hlt', by simp [Prog.set, hne, hpq]⟩

/-- The store stops accepting articles. -/
theorem running_stop (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h) :
    Running cfg s { p with accepting := false } h :=
  ⟨hr.spool, hr.lookup, hr.settled, hr.trusted, (fun h => by cases h), (fun h => by cases h),
    (fun c hc => ⟨(hr.inFlight c hc).1, fun h => by cases h⟩), hr.posts, hr.apart, hr.past,
    hr.runRefused, hr.runAppended⟩

/-- A name no entry has holds nothing. -/
theorem lookup_none_of (s : Fs) (name : Bytes) (h : ∀ e ∈ s.dir, e.name ≠ name) :
    s.lookup name = none := by
  have : s.entry name = none := by
    simp only [Fs.entry, List.find?_eq_none, beq_iff_eq]
    exact fun e he => h e he
  simp [Fs.lookup, this]

/-- **The article's file created** under its temporary name. -/
theorem running_create (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (hq : p.posts q = some x) (hs : x.stage = .reserved) :
    Running cfg (s.step (.create (tempName q))).1
      (p.set q (some { x with written := 0, stage := .writing s.next })) h := by
  obtain ⟨hlt, hpl, hf, hh⟩ := hr.posts q x hq
  have hnames : ∀ e ∈ s.dir, e.name ≠ tempName q ∧ e.name ≠ finalName q := by
    unfold PostHolds at hh; rw [hs] at hh; exact hh
  have hfree := lookup_none_of s _ fun e he => (hnames e he).1
  have hq64 := seq_lt cfg s p h hr q x hq
  have hj : tempName q ≠ journalName := temp_ne_journal q
  have hsp := spool_create cfg s _ hr.spool (tempName q) hj
    ⟨.temp q, parseName_bytes (.temp q) (by simp [Name.valid, hq64]), fun q' hq' => by
      simp only [seqOf, Option.some.injEq] at hq'; subst hq'; exact hlt⟩
    ⟨(fun h => by cases h), (fun h => by cases h)⟩ hr.settled
  have hok := hr.spool.ok
  obtain ⟨dj, hdj⟩ := data_some s hok _ _ hr.lookup
  obtain ⟨hl, hu, htr, hsy, hin⟩ := journal_keep cfg s (s.step (.create (tempName q))).1 p
    (p.set q (some { x with written := 0, stage := .writing s.next })) h hr
    (by rw [create_eq s _ hfree]; exact entry_other s _ journalName _ (Ne.symm hj))
    (by
      rw [create_eq s _ hfree]
      show (s.files ++ _).lookup _ = _
      rw [lookup_append_new _ _ _ _ hdj]; exact hdj.symm)
    (fun _ => by rw [create_eq s _ hfree]) rfl rfl rfl rfl id id
  have hlive := live_not_refused cfg s p h hr q x hq (by rw [hs]; exact fun h => by cases h)
  obtain ⟨hrr, hra⟩ := attempts_set p h q x hq hr.runRefused hr.runAppended _
    (fun hm => absurd hm hlive)
  refine ⟨hsp, hl, hu, htr, hr.accepts, hsy, hin, posts_keep cfg s _ p _ h h q hr (Nat.le_refl _)
    (fun c hc => Or.inl hc) (fun _ _ => rfl) (fun n hn => by simp [Prog.set, hn])
    (fun n y hnq hy hh' => holds_create s hok n y hh' _ hfree
      (names_apart q n hq64 (seq_lt cfg s p h hr n y hy) (Ne.symm hnq) _ (Or.inl rfl)))
    (fun y hy => ?_), hr.apart, hr.past, hrr, hra⟩
  simp only [Prog.set, ↓reduceIte, Option.some.injEq] at hy
  subst hy
  refine ⟨hlt, hpl, fun _ => hf (by rw [hs]; exact fun h => by cases h), ?_⟩
  unfold PostHolds
  have hstep := create_eq s _ hfree
  refine ⟨by rw [FsModel.lookup_create s _ _ hfree, if_pos rfl], fun e he hen => ?_,
    fun e he hle => ?_, Nat.zero_le _, Data.empty, ?_, by simp [Data.empty], rfl⟩
  · rw [hstep] at he
    rcases rebind_names s.dir _ _ e he with he' | ⟨e₀, he₀, hn₀⟩
    · exact final_ne_temp q q (hen.symm.trans he')
    · exact (hnames e₀ he₀).2 (hn₀.trans hen)
  · rw [hstep] at he
    rcases rebind_leaves s.dir _ _ e he _ hle with ⟨he', _⟩ | ⟨e₀, he₀, _, hl₀⟩
    · exact Or.inl he'
    · exact absurd (leaves_below s hok e₀ he₀ _ hl₀) (Nat.lt_irrefl _)
  · rw [hstep]
    exact lookup_append_fresh s.next Data.empty s.files fun p hp heq => by
      have := hok.2.2.1 p hp; rw [heq] at this; exact Nat.lt_irrefl _ this

theorem take_chunk {α : Type} (o : List α) (w m : Nat) :
    o.take w ++ (o.drop w).take m = o.take (w + ((o.drop w).take m).length) := by
  rw [List.take_add]
  congr 1
  simp

/-- An article's file is neither the journal's nor that of a commit in place. -/
theorem file_apart (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (hq : p.posts q = some x) (i : Ino) (hi : x.stage.inode = some i) :
    s.lookup journalName ≠ some i ∧ ∀ c ∈ placedSet (viewOf p h), ∀ e,
      s.entry (finalName c.seq) = some e → e.synced ≠ some i := by
  obtain ⟨_, hpl, _, hh⟩ := hr.posts q x hq
  have ho := holds_owns s q x hh i hi
  have hq64 := seq_lt cfg s p h hr q x hq
  refine ⟨fun hl => ?_, fun c hc e he hsyn => ?_⟩
  · rcases owns_lookup s q i ho _ hl with he | he
    · exact temp_ne_journal q he.symm
    · exact final_ne_journal q he.symm
  · rcases ho e (List.mem_of_find?_eq_some he) (Or.inl hsyn.symm) with hn | hn
    · rw [entry_name s _ e he] at hn; exact final_ne_temp _ _ hn
    · rw [entry_name s _ e he] at hn
      exact hpl c hc (finalName_inj _ _ (placed_lt cfg s p h hr c hc) hq64 hn)

/-- **An operation on an article's own file** keeps the store running, its file as the
article's new stage says. -/
theorem running_onFile (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (hq : p.posts q = some x) (i : Ino) (hi : x.stage.inode = some i)
    (f : Data → Data) (hf : ∀ d, d.Ok → (f d).Ok) (y : Post) (acc : Bool)
    (hacc : acc = true → p.accepting = true)
    (hy : y.stage ≠ .refused → h.files q = y.octets)
    (hyr : (p.run, q) ∈ h.refused → y.stage = .refused)
    (hyh : PostHolds (s.onData i f).1 q y) :
    Running cfg (s.onData i f).1 { p.set q (some y) with accepting := acc } h := by
  obtain ⟨hlt, hpl, _, hh⟩ := hr.posts q x hq
  obtain ⟨hj, hp⟩ := file_apart cfg s p h hr q x hq i hi
  have hsp := spool_file cfg s _ hr.spool i f hf hj fun c hc hpl' =>
    placed_other s _ c i f hpl' (hp c hc)
  have hne : p.journal ≠ i := fun e => hj (by rw [← e]; exact hr.lookup)
  obtain ⟨hl, hu, htr, hsy, hin⟩ := journal_keep cfg s (s.onData i f).1 p
    { p.set q (some y) with accepting := acc } h hr (by rw [onData_entry])
    (by rw [data_onData, if_neg hne]) (fun _ => onData_dirTrusted s i f) rfl rfl rfl rfl hacc id
  have hq64 := seq_lt cfg s p h hr q x hq
  obtain ⟨hrr, hra⟩ := attempts_set p h q x hq hr.runRefused hr.runAppended (some y)
    (fun hm x' hx' => by cases hx'; exact hyr hm)
  refine ⟨hsp, hl, hu, htr, fun ha => hr.accepts (hacc ha), hsy, hin,
    posts_keep cfg s _ p _ h h q hr (Nat.le_refl _)
    (fun c hc => Or.inl hc) (fun _ _ => rfl) (fun n hn => by simp [Prog.set, hn])
    (fun n z hnq hz hh' => holds_onData s n z hh' i f (by
      rcases holds_lookup s q x hh i hi with hlq | hlq
      · exact apart_of_lookup s n z hh' _ i hlq
          (names_apart q n hq64 (seq_lt cfg s p h hr n z hz) (Ne.symm hnq) _ (Or.inl rfl))
      · exact apart_of_lookup s n z hh' _ i hlq
          (names_apart q n hq64 (seq_lt cfg s p h hr n z hz) (Ne.symm hnq) _ (Or.inr rfl))))
    (fun z hz => ?_), hr.apart, hr.past, hrr, hra⟩
  simp only [Prog.set, ↓reduceIte, Option.some.injEq] at hz
  subst hz
  exact ⟨hlt, hpl, hy, hyh⟩

/-- **Part of the octets written** to the article's file. -/
theorem running_write (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (i : Ino) (m : Nat) (hq : p.posts q = some x) (hs : x.stage = .writing i) :
    Running cfg (s.step (.append i (x.chunk m))).1
      (p.set q (some { x with written := x.written + (x.chunk m).length })) h := by
  obtain ⟨_, _, hf, hh⟩ := hr.posts q x hq
  have hlive := live_not_refused cfg s p h hr q x hq (by rw [hs]; exact fun h => by cases h)
  unfold PostHolds at hh
  rw [hs] at hh
  obtain ⟨hl, hnf, ho, hw, d, hd, hseen, ht⟩ := hh
  exact running_onFile cfg s p h hr q x hq i (by rw [hs]; rfl)
    (fun d => d.append (x.chunk m)) (fun d hd => FsModel.append_ok d hd _)
    { x with written := x.written + (x.chunk m).length } p.accepting (fun h => h)
    (fun _ => hf (by rw [hs]; exact fun h => by cases h)) (fun hm => absurd hm hlive) (by
      unfold PostHolds
      simp only [hs]
      refine ⟨by rw [onData_lookup]; exact hl, by rw [FsModel.onData_dir]; exact hnf,
        by unfold Owns; rw [FsModel.onData_dir]; exact ho, ?_, d.append (x.chunk m),
        by rw [data_onData, if_pos rfl, hd]; rfl, ?_, ht⟩
      · simp only [Post.chunk, List.length_take, List.length_drop]; omega
      · simp only [Data.append, hseen, Post.chunk]; exact take_chunk _ _ _)

/-- **The article's file synced** once written whole. -/
theorem running_sync (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (i : Ino) (hq : p.posts q = some x) (hs : x.stage = .writing i)
    (hw : x.written = x.octets.length) :
    Running cfg (s.step (.sync i)).1 (p.set q (some { x with stage := .synced i })) h := by
  obtain ⟨_, _, hf, hh⟩ := hr.posts q x hq
  have hlive := live_not_refused cfg s p h hr q x hq (by rw [hs]; exact fun h => by cases h)
  unfold PostHolds at hh
  rw [hs] at hh
  obtain ⟨hl, hnf, ho, _, d, hd, hseen, ht⟩ := hh
  have hs' : d.seen = x.octets := by rw [hseen, hw, List.take_length]
  exact running_onFile cfg s p h hr q x hq i (by rw [hs]; rfl) Data.sync
    (fun d hd => FsModel.sync_ok d hd) { x with stage := .synced i } p.accepting (fun h => h)
    (fun _ => hf (by rw [hs]; exact fun h => by cases h)) (fun hm => absurd hm hlive) (by
      unfold PostHolds
      exact ⟨by rw [onData_lookup]; exact hl, by rw [FsModel.onData_dir]; exact hnf,
        by unfold Owns; rw [FsModel.onData_dir]; exact ho, d.sync,
        by rw [data_onData, if_pos rfl, hd]; rfl, by rw [seen_sync]; exact hs',
        by simp [Data.sync, ht], by rw [high_sync d ht, seen_sync]⟩)

/-- A write or a sync of the article's file failed: the article marked refused, and after a failed
sync the store stops accepting. -/
theorem running_fileFails (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (i : Ino) (hq : p.posts q = some x) (hs : x.stage = .writing i)
    (f : Data → Data) (hf : ∀ d, d.Ok → (f d).Ok) (acc : Bool)
    (hacc : acc = true → p.accepting = true) :
    Running cfg (s.onData i f).1
      { p.set q (some { x with stage := .refused }) with accepting := acc } h :=
  running_onFile cfg s p h hr q x hq i (by rw [hs]; rfl) f hf _ acc hacc
    (fun h => absurd rfl h) (fun _ => rfl) (by unfold PostHolds; trivial)

/-- **The article's file moved** to its final name. -/
theorem running_rename (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (i : Ino) (hq : p.posts q = some x) (hs : x.stage = .synced i) :
    Running cfg (s.step (.rename (tempName q) (finalName q))).1
      (p.set q (some { x with stage := .final i })) h := by
  obtain ⟨hlt, hpl, hf, hh⟩ := hr.posts q x hq
  have hlive := live_not_refused cfg s p h hr q x hq (by rw [hs]; exact fun h => by cases h)
  unfold PostHolds at hh
  rw [hs] at hh
  obtain ⟨hl, hnf, ho, d, hd, hseen, hk, hhigh⟩ := hh
  have hq64 := seq_lt cfg s p h hr q x hq
  have hfree := lookup_none_of s (finalName q) hnf
  have hstep : (s.step (.rename (tempName q) (finalName q))).1 =
      { s with dir := rebind (rebind s.dir (finalName q) (some i)) (tempName q) none } := by
    simp [Fs.step, hl, hfree]
  have hps : ∀ c ∈ placedSet (viewOf p h), finalName c.seq ≠ finalName q := fun c hc e =>
    hpl c hc (finalName_inj _ _ (placed_lt cfg s p h hr c hc) hq64 e)
  have hsp := spool_rename cfg s _ hr.spool (tempName q) (finalName q) (temp_ne_journal q)
    (final_ne_journal q) (fun c _ => final_ne_temp _ _) hps
    ⟨.final q, parseName_bytes (.final q) (by simp [Name.valid, hq64]), fun q' hq' => by
      simp only [seqOf, Option.some.injEq] at hq'; subst hq'; exact hlt⟩
  obtain ⟨he, hfl, hdt⟩ := other_journal s (.rename (tempName q) (finalName q))
    (Or.inr ⟨_, _, rfl, temp_ne_journal q, final_ne_journal q⟩)
  obtain ⟨hl', hu, htr, hsy, hin⟩ := journal_keep cfg s _ p
    (p.set q (some { x with stage := .final i })) h hr he (by simp only [Fs.data, hfl])
    (fun _ => hdt) rfl rfl rfl rfl id id
  obtain ⟨hrr, hra⟩ := attempts_set p h q x hq hr.runRefused hr.runAppended _
    (fun hm => absurd hm hlive)
  refine ⟨hsp, hl', hu, htr, hr.accepts, hsy, hin, posts_keep cfg s _ p _ h h q hr (Nat.le_refl _)
    (fun c hc => Or.inl hc) (fun _ _ => rfl) (fun n hn => by simp [Prog.set, hn])
    (fun n z hnq hz hh' => ?_) (fun z hz => ?_), hr.apart, hr.past, hrr, hra⟩
  · have hap := names_apart q n hq64 (seq_lt cfg s p h hr n z hz) (Ne.symm hnq)
    rw [hstep]
    exact holds_rebind { s with dir := rebind s.dir (finalName q) (some i) } n z
      (holds_rebind s n z hh' _ _ (hap _ (Or.inr rfl)) fun j hj e => by
        cases e; exact apart_of_lookup s n z hh' _ _ hl (hap _ (Or.inl rfl)) i hj rfl)
      _ none (hap _ (Or.inl rfl)) (fun _ _ h => by cases h)
  · simp only [Prog.set, ↓reduceIte, Option.some.injEq] at hz
    subst hz
    refine ⟨hlt, hpl, fun _ => hf (by rw [hs]; exact fun h => by cases h), ?_⟩
    unfold PostHolds
    refine ⟨by rw [FsModel.lookup_rename s _ _ _ i hl (by rw [hfree]; exact fun h => by cases h),
        if_neg (final_ne_temp q q), if_pos rfl], fun e he hle => ?_, d,
      by rw [hstep]; exact hd, hseen, hk, hhigh⟩
    rw [hstep] at he
    rcases rebind_leaves _ _ _ e he i hle with ⟨_, hb⟩ | ⟨e₁, he₁, hn₁, hl₁⟩
    · cases hb
    · rcases rebind_leaves _ _ _ e₁ he₁ i hl₁ with ⟨hn, _⟩ | ⟨e₀, he₀, hn₀, hl₀⟩
      · exact Or.inr (hn₁ ▸ hn)
      · rw [← hn₁, ← hn₀]; exact ho e₀ he₀ hl₀

/-- **The directory synced** after the move: the article's file in place. -/
theorem running_place (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (i : Ino) (hq : p.posts q = some x) (hs : x.stage = .final i)
    (ht : p.trusting = true) :
    Running cfg (s.step .syncDir).1 (p.set q (some { x with stage := .placed i })) h := by
  obtain ⟨hlt, hpl, hf, hh⟩ := hr.posts q x hq
  have hlive := live_not_refused cfg s p h hr q x hq (by rw [hs]; exact fun h => by cases h)
  have hok := hr.spool.ok
  obtain ⟨htd, htj⟩ := hr.trusted ht
  have hh' := holds_syncDir s hok q x hh
  unfold PostHolds at hh hh'
  rw [hs] at hh hh'
  have hsp := spool_syncDir cfg s _ hr.spool
  obtain ⟨hrr, hra⟩ := attempts_set p h q x hq hr.runRefused hr.runAppended _
    (fun hm => absurd hm hlive)
  refine ⟨hsp, by rw [syncDir_lookup s hok]; exact hr.lookup,
    syncDir_unsettled s hok htd _ hr.lookup,
    fun ht' => trusted_syncDir s hok (hr.trusted ht'), hr.accepts,
    fun hacc hc => by rw [syncDir_data]; exact hr.synced hacc hc,
    fun c hc => ⟨(hr.inFlight c hc).1, fun hacc => by
      rw [syncDir_data]; exact (hr.inFlight c hc).2 hacc⟩,
    posts_keep cfg s _ p _ h h q hr (Nat.le_refl _) (fun c hc => Or.inl hc) (fun _ _ => rfl)
      (fun n hn => by simp [Prog.set, hn]) (fun n z _ _ hz => holds_syncDir s hok n z hz)
      (fun z hz => ?_), hr.apart, hr.past, hrr, hra⟩
  simp only [Prog.set, ↓reduceIte, Option.some.injEq] at hz
  subst hz
  refine ⟨hlt, hpl, fun _ => hf (by rw [hs]; exact fun h => by cases h), ?_⟩
  unfold PostHolds
  exact ⟨syncDir_settled s hok htd _ i hh.1, hh'.2⟩

/-- The directory's sync failed: the article marked refused, the store stops accepting, and no
later sync is trusted. -/
theorem running_placeFails (cfg : Config) (s : Fs) (p : Prog) (h : Hist)
    (hr : Running cfg s p h) (q : Nat) (x : Post) (hq : p.posts q = some x) :
    Running cfg { s with dirTrusted := false }
      { p.set q (some { x with stage := .refused }) with accepting := false, trusting := false }
      h := by
  have hr' := running_forget cfg s p h hr q x hq (some { x with stage := .refused })
    fun z hz => by cases hz; rfl
  exact ⟨spool_untrustDir cfg s _ hr'.spool, hr'.lookup, hr'.settled, (fun h => by cases h),
    (fun h => by cases h), (fun h => by cases h),
    (fun c hc => ⟨(hr'.inFlight c hc).1, fun h => by cases h⟩),
    (fun n z hz => hr'.posts n z hz), hr'.apart, hr'.past, hr'.runRefused, hr'.runAppended⟩

/-- An operation on the journal's file keeps what the spool holds of every article in flight. -/
theorem holds_journal (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (n : Nat) (z : Post) (hh : PostHolds s n z) (f : Data → Data) :
    PostHolds (s.onData p.journal f).1 n z :=
  holds_onData s n z hh p.journal f (apart_of_lookup s n z hh _ _ hr.lookup
    ⟨fun e => temp_ne_journal n e.symm, fun e => final_ne_journal n e.symm⟩)

/-- A commit numbered above the commits before it. -/
theorem seqTwice_snoc (c : Commit) : ∀ cs : List Commit, seqTwice? cs = none →
    (∀ c' ∈ cs, c'.seq ≠ c.seq) → seqTwice? (cs ++ [c]) = none
  | [], _, _ => rfl
  | a :: cs, h, hne => by
    have hcs : cs.any (·.seq == a.seq) = false := by
      cases hh : cs.any (·.seq == a.seq)
      · rfl
      · simp only [seqTwice?, hh, ↓reduceIte] at h; cases h
    have h' : seqTwice? cs = none := by simpa [seqTwice?, hcs] using h
    have hca : (c.seq == a.seq) = false := by
      simpa using fun e => hne a (List.mem_cons_self ..) e.symm
    simp only [List.cons_append, seqTwice?, List.any_append, hcs, List.any_cons, List.any_nil,
      hca, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    exact seqTwice_snoc c cs h' fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')

/-- A commit whose article numbers are above those the commits before it gave its groups. -/
theorem notAbove_snoc (c : Commit) : ∀ (before cs : List Commit), notAbove? before cs = none →
    (c.groups.find? fun g => g.number ≤ highIn (before ++ cs) g.name) = none →
    notAbove? before (cs ++ [c]) = none
  | before, [], _, hc => by
    simp only [List.append_nil] at hc
    simp [notAbove?, hc]
  | before, a :: cs, h, hc => by
    simp only [notAbove?] at h
    split at h
    · cases h
    · rename_i hfa
      simp only [List.cons_append, notAbove?, hfa]
      exact notAbove_snoc c (before ++ [a]) cs h (by simpa using hc)

/-- A commit whose groups the store carries. -/
theorem unknownGroup_snoc (cfg : Config) (cs : List Commit) (c : Commit)
    (h : unknownGroup? cfg cs = none) (hc : ∀ g ∈ c.groups, g.name ∈ cfg.groups) :
    unknownGroup? cfg (cs ++ [c]) = none := by
  simp only [unknownGroup?, Option.map_eq_none_iff] at h ⊢
  rw [List.flatMap_append, List.find?_append, h]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Option.none_or]
  rw [List.find?_eq_none]
  intro g hg
  simpa using hc g hg

/-- **The rules recovery checks, kept by a commit the program numbered**: its own sequence number,
and its article numbers allocated in groups the store carries. -/
theorem rules_snoc (cfg : Config) (rs : List Record) (c : Commit) (h : Rules cfg (commitsOf rs))
    (hseq : ∀ c' ∈ commitsOf rs, c'.seq ≠ c.seq) (ha : Allocated cfg rs c) :
    Rules cfg (commitsOf (rs ++ [.commit c])) := by
  have hcs : commitsOf (rs ++ [.commit c]) = commitsOf rs ++ [c] := by simp [commitsOf]
  rw [hcs]
  refine ⟨seqTwice_snoc c _ h.1 hseq, notAbove_snoc c [] _ h.2.1 ?_,
    unknownGroup_snoc cfg _ c h.2.2 fun g hg => (ha g hg).1⟩
  rw [List.find?_eq_none]
  intro g hg hle
  have := (ha g hg).2
  simp only [List.nil_append, decide_eq_true_eq] at hle
  omega

/-- **An article's commit record appended**, whole or, if the write failed, in part; once
appended whole the store goes on accepting, and after a failure it stops. -/
theorem running_commit (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (q : Nat) (x : Post) (i : Ino) (c : Commit) (hq : p.posts q = some x)
    (hs : x.stage = .placed i) (hc : p.committing = none) (ha : p.accepting = true)
    (hseq : c.seq = q) (hsize : c.fileSize = x.octets.length)
    (hcrc : (crc32c x.octets).toNat = c.fileCrc) (hok : (Record.commit c).ok = true)
    (hgroups : Allocated cfg p.records c) (j : Nat) (acc : Bool)
    (hacc : acc = true → j = (commitFrame p.key p.records c).length) :
    Running cfg (s.onData p.journal fun d => d.append ((commitFrame p.key p.records c).take j)).1
      { p.set q none with committing := some c, accepting := acc }
      { h with appended := h.appended ++ [(p.run, c)] } := by
  obtain ⟨hlt, hplq, hf, hh⟩ := hr.posts q x hq
  have hlive := live_not_refused cfg s p h hr q x hq (by rw [hs]; exact fun h => by cases h)
  unfold PostHolds at hh
  rw [hs] at hh
  obtain ⟨hent, _, dq, hdq, hseen, hk, hhigh⟩ := hh
  obtain ⟨d, hd, hjs, hjh, hfr⟩ := hr.synced ha hc
  have hsp := hr.spool
  have hph : (viewOf p h).phase = .steady p.key p.records [] := by simp [viewOf, backOf, hc]
  have hne' : (viewOf p h).phase ≠ .none := by rw [hph]; exact fun h => by cases h
  obtain ⟨_, ij', d', _, hl', _, hd', hholds, _⟩ := hsp.journal hne'
  rw [hr.lookup] at hl'
  cases hl'
  rw [hd] at hd'
  cases hd'
  rw [hph] at hholds
  have hfq : h.files q = x.octets := hf (by rw [hs]; exact fun h => by cases h)
  have hplc : Placed s h.files c := by
    refine ⟨_, i, dq, by rw [hseq]; exact hent, ⟨rfl, rfl⟩, rfl, hdq, hk, hhigh, ?_, ?_, ?_⟩
    · rw [hseq, hfq]; exact hseen
    · rw [hseq, hfq]; exact hsize.symm
    · rw [hseq, hfq]; exact hcrc
  have hold : placedSet (viewOf p h) = commitsOf p.records := by
    simp [placedSet, viewOf, backOf, hc, Phase.kept, Phase.back]
  have hrules := rules_snoc cfg p.records c hsp.rules.1
    (fun c' hc' => by rw [hseq]; exact hplq c' (by rw [hold]; exact hc')) hgroups
  have hmap : (h.appended ++ [(p.run, c)]).map Prod.snd = h.appended.map Prod.snd ++ [c] := by
    simp
  have hsp1 : Spool cfg s { viewOf p h with
      appended := (h.appended ++ [(p.run, c)]).map Prod.snd } := by
    rw [hmap]; exact spool_appended cfg s _ hsp c
  have hsp2 := spool_journal cfg s _ hsp1 p.journal hr.lookup
    (fun d => d.append ((commitFrame p.key p.records c).take j))
    (fun d hd => FsModel.append_ok d hd _) (.steady p.key p.records [.commit c])
    (fun d₀ hd₀ => by
      rw [hd] at hd₀; cases hd₀
      exact steady_mono _ _ _ _ _ (steady_append _ _ _ d hholds hjs (by rw [hjh, hjs]) _ hok rfl
        (Or.inl hfr) j) fun r hr => List.mem_singleton.mpr hr)
    (fun hor => by
      rcases hor with hor | hor | hor
      · cases hor
      · cases hor
      · exact absurd hor hr.settled)
    (fun c' hc' => by
      simp only [Phase.kept, Phase.back, commitsOf_append, List.mem_append] at hc'
      rcases hc' with hc' | hc'
      · have hmem : c' ∈ placedSet (viewOf p h) := by rw [hold]; exact hc'
        exact hsp.placed c' hmem
      · simp [commitsOf] at hc'; subst hc'; exact hplc)
    ⟨hsp.rules.1, fun r hr => by
      simp only [Phase.back, List.mem_singleton] at hr; subst hr; exact hrules⟩
    (fun c' hc' => by
      simp only [Phase.kept, Phase.back, commitsOf_append, List.mem_append] at hc'
      rcases hc' with hc' | hc'
      · have hmem : c' ∈ placedSet (viewOf p h) := by rw [hold]; exact hc'
        exact hsp.seqs c' hmem
      · simp [commitsOf] at hc'; subst hc'; show c'.seq < p.next; rw [hseq]; exact hlt)
    (fun c' hc' => hsp.answered c' hc')
    (fun c' hc' => by
      show c' ∈ (h.appended ++ [(p.run, c)]).map Prod.snd
      rw [hmap]
      simp only [Phase.kept, Phase.back, commitsOf_append, List.mem_append] at hc'
      rcases hc' with hc' | hc'
      · have hmem : c' ∈ placedSet (viewOf p h) := by rw [hold]; exact hc'
        exact List.mem_append_left _ (hsp.appended c' hmem)
      · simp [commitsOf] at hc'; subst hc'
        exact List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨hrr, hra⟩ := attempts_set p h q x hq hr.runRefused hr.runAppended none
    (fun _ _ h => by cases h)
  refine ⟨hsp2, by rw [onData_lookup]; exact hr.lookup, fun hu => hr.settled (by
      unfold Unsettled at hu ⊢; rw [onData_entry] at hu; exact hu),
    (fun ht => trusted_onData s _ _ (fun _ => rfl) (hr.trusted ht)), (fun _ => hr.accepts ha),
    (fun _ h => by cases h), (fun c' hc' => ?_), ?_, fun r c' hc' hm => ?_, fun r q' hq' => ?_,
    fun q' hq' => hrr q' hq', fun c' hc' => ?_⟩
  · simp only [Option.some.injEq] at hc'
    subst hc'
    refine ⟨hok, fun hacc' => ⟨d.append ((commitFrame p.key p.records c).take j), ?_, ?_⟩⟩
    · show (s.onData p.journal _).1.data p.journal = _
      rw [data_onData, if_pos rfl, hd]; rfl
    · show (d.append _).seen = journal p.key p.records ++ commitFrame p.key p.records c
      simp only [Data.append, hjs, hacc hacc', List.take_length]
  · refine posts_keep cfg s _ p _ h _ q hr (Nat.le_refl _) (fun c' hc' => ?_) (fun _ _ => rfl)
      (fun n hn => by simp [Prog.set, hn])
      (fun n z _ _ hz => holds_journal cfg s p h hr n z hz _)
      (fun z hz => by simp [Prog.set] at hz)
    simp only [placedSet, viewOf, backOf, Phase.kept, Phase.back, commitsOf_append,
      List.mem_append] at hc'
    rcases hc' with hc' | hc'
    · left; rw [hold]; exact hc'
    · right; simp [commitsOf] at hc'; rw [hc', hseq]
  · rcases List.mem_append.mp hc' with hc' | hc'
    · exact hr.apart r c' hc' hm
    · simp only [List.mem_singleton, Prod.mk.injEq] at hc'
      obtain ⟨rfl, rfl⟩ := hc'
      rw [hseq] at hm
      exact hlive hm
  · rcases hq' with hq' | ⟨c', hc', hcq⟩
    · exact hr.past r q' (Or.inl hq')
    · rcases List.mem_append.mp hc' with hc' | hc'
      · exact hr.past r q' (Or.inr ⟨c', hc', hcq⟩)
      · simp only [List.mem_singleton, Prod.mk.injEq] at hc'
        rw [hc'.1]; exact Nat.le_refl _
  · rcases List.mem_append.mp hc' with hc' | hc'
    · exact hra c' hc'
    · simp only [List.mem_singleton, Prod.mk.injEq] at hc'
      obtain ⟨_, rfl⟩ := hc'
      exact ⟨by rw [hseq]; exact hlt, by simp [Prog.set, hseq]⟩

/-- **The journal synced over the record in flight: 240.** -/
theorem running_publish (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (c : Commit) (hc : p.committing = some c) (ha : p.accepting = true) :
    Running cfg (s.step (.sync p.journal)).1
      { p with records := p.records ++ [.commit c], committing := none }
      { h with answered := h.answered ++ [c] } := by
  show Running cfg (s.onData p.journal Data.sync).1 _ _
  obtain ⟨hok, hin⟩ := hr.inFlight c hc
  obtain ⟨d, hd, hseen⟩ := hin ha
  obtain ⟨htd, htj⟩ := hr.trusted (hr.accepts ha)
  have ht := htj _ d hr.lookup hd
  have hsp := hr.spool
  have hph : (viewOf p h).phase = .steady p.key p.records [.commit c] := by
    simp [viewOf, backOf, hc]
  have hne' : (viewOf p h).phase ≠ .none := by rw [hph]; exact fun h => by cases h
  obtain ⟨_, ij', d', _, hl', _, hd', hholds, _⟩ := hsp.journal hne'
  rw [hr.lookup] at hl'
  cases hl'
  rw [hd] at hd'
  cases hd'
  rw [hph] at hholds
  have hrules := hsp.rules
  rw [hph] at hrules
  obtain ⟨hst, hfr⟩ := steady_sync _ _ _ d hholds ht (.commit c) hok rfl hseen
  have hpl : placedSet (viewOf p h) = commitsOf (p.records ++ [.commit c]) := by
    simp [placedSet, viewOf, backOf, hc, Phase.kept, Phase.back]
  have hsp1 := spool_rephase cfg s _ hsp p.journal hr.lookup Data.sync
    (fun d hd => FsModel.sync_ok d hd) (.steady p.key (p.records ++ [.commit c]) [])
    (fun d₀ hd₀ => by
      rw [hd] at hd₀; cases hd₀; exact steady_mono _ _ _ _ _ hst fun _ h => h.elim)
    (fun hor => by rcases hor with hor | hor <;> cases hor)
    (fun c' hc' => by rw [hpl]; simpa [Phase.kept, Phase.back] using hc')
    (fun c' hc' => by
      rw [hph] at hc'
      simp only [Phase.kept, commitsOf_append] at hc' ⊢
      exact List.mem_append_left _ hc')
    ⟨hrules.2 _ (List.mem_singleton_self _), fun r hr => by cases hr⟩
  have hsp2 := spool_answer cfg _ _ hsp1 c (by
    simp only [Phase.kept, commitsOf_append]
    exact List.mem_append_right _ (by simp [commitsOf]))
  refine ⟨hsp2, by rw [onData_lookup]; exact hr.lookup, fun hu => hr.settled (by
      unfold Unsettled at hu ⊢; rw [onData_entry] at hu; exact hu),
    (fun ht' => trusted_onData s _ _ sync_trusted (hr.trusted ht')), hr.accepts,
    (fun _ _ => ⟨d.sync, ?_, ?_, ?_, hfr⟩), (fun c' hc' => by cases hc'),
    posts_all cfg s _ p _ h _ hr (Nat.le_refl _)
      (fun c' hc' => by rw [hpl]; simpa [placedSet, viewOf, backOf, Phase.kept, Phase.back]
        using hc') rfl rfl (fun n z _ hz => holds_journal cfg s p h hr n z hz _),
    hr.apart, hr.past, hr.runRefused, hr.runAppended⟩
  · show (s.onData p.journal _).1.data p.journal = _
    rw [data_onData, if_pos rfl, hd]; rfl
  · show d.sync.seen = journal p.key (p.records ++ [.commit c])
    rw [seen_sync, hseen, journal_append]; rfl
  · rw [high_sync d ht, seen_sync]

/-- The journal's sync failed: the outcome unknown, the store stops accepting, and no later sync is
trusted. -/
theorem running_publishFails (cfg : Config) (s : Fs) (p : Prog) (h : Hist)
    (hr : Running cfg s p h) :
    Running cfg (s.onData p.journal Data.untrust).1
      { p with accepting := false, trusting := false } h :=
  ⟨spool_journal_untrust cfg s _ hr.spool p.journal hr.lookup,
    by rw [onData_lookup]; exact hr.lookup,
    fun hu => hr.settled (by unfold Unsettled at hu ⊢; rw [onData_entry] at hu; exact hu),
    (fun h => by cases h), (fun h => by cases h), (fun h => by cases h),
    (fun c hc => ⟨(hr.inFlight c hc).1, fun h => by cases h⟩),
    posts_all cfg s _ p _ h h hr (Nat.le_refl _) (fun _ hc => hc) rfl rfl
      (fun n z _ hz => holds_journal cfg s p h hr n z hz _),
    hr.apart, hr.past, hr.runRefused, hr.runAppended⟩

theorem Prog.set_set (p : Prog) (q : Nat) (a b : Option Post) :
    (p.set q a).set q b = p.set q b := by
  simp only [Prog.set]
  congr 1
  funext n
  split <;> rfl

/-- **Every step of the store keeps it running**: each operation done or failed, and what the
program and the run make of it. -/
theorem running_step (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (s' : Fs) (p' : Prog) (h' : Hist) (hs : Step cfg s p h s' p' h') : Running cfg s' p' h' := by
  cases hs with
  | reserve o hroom => exact running_reserve cfg s p h hr o hroom
  | create q x hq hst => exact running_create cfg s p h hr q x hq hst
  | write q x i m hq hst => exact running_write cfg s p h hr q x i m hq hst
  | sync q x i hq hst hw => exact running_sync cfg s p h hr q x i hq hst hw
  | rename q x i hq hst => exact running_rename cfg s p h hr q x i hq hst
  | place q x i hq hst ht => exact running_place cfg s p h hr q x i hq hst ht
  | commit q x i c hq hst hc ha hseq hsize hcrc hok hgroups =>
    have := running_commit cfg s p h hr q x i c hq hst hc ha hseq hsize hcrc hok hgroups
      (commitFrame p.key p.records c).length p.accepting (fun _ => rfl)
    rw [List.take_length] at this
    exact this
  | publish c hc ha => exact running_publish cfg s p h hr c hc ha
  | refuse q x hq => exact running_refuse cfg s p h hr q x hq
  | clean q x name hq hst hn =>
    exact running_clean cfg s p h hr q x hq hst name hn _ (Or.inr rfl)
  | drop q x hq hst => exact running_forget cfg s p h hr q x hq none fun _ h => by cases h
  | read op hop => exact running_read cfg s p h hr op hop
  | createFails q x _ hq hst ht =>
    rcases fails_whole s s' _ ht (fun _ _ h => by cases h) (fun _ h => by cases h)
      (fun h => by cases h) with rfl | rfl
    · exact running_refuse cfg _ p h hr q x hq
    · have h1 := running_forget cfg _ _ h (running_create cfg s p h hr q x hq hst) q
        { x with written := 0, stage := .writing s.next } (by simp [Prog.set])
        (some { x with stage := .refused }) fun z hz => by cases hz; rfl
      rw [Prog.set_set] at h1
      exact running_record cfg _ _ h h1 q { x with stage := .refused } (by simp [Prog.set]) rfl
  | writeFails q x i m _ hq hst ht =>
    obtain ⟨k, rfl⟩ := fails_append s s' i _ ht
    exact running_record cfg _ _ h
      (running_fileFails cfg s p h hr q x i hq hst _ (fun d hd => FsModel.append_ok d hd _)
        p.accepting id) q { x with stage := .refused } (by simp [Prog.set]) rfl
  | syncFails q x i _ hq hst ht =>
    rw [fails_sync s s' i ht]
    exact running_record cfg _ _ h
      (running_fileFails cfg s p h hr q x i hq hst _ (fun d hd => FsModel.untrust_ok d hd)
        false (fun h => by cases h)) q { x with stage := .refused } (by simp [Prog.set]) rfl
  | renameFails q x i _ hq hst ht =>
    rcases fails_whole s s' _ ht (fun _ _ h => by cases h) (fun _ h => by cases h)
      (fun h => by cases h) with rfl | rfl
    · exact running_refuse cfg _ p h hr q x hq
    · have h1 := running_forget cfg _ _ h (running_rename cfg s p h hr q x i hq hst) q
        { x with stage := .final i } (by simp [Prog.set])
        (some { x with stage := .refused }) fun z hz => by cases hz; rfl
      rw [Prog.set_set] at h1
      exact running_record cfg _ _ h h1 q { x with stage := .refused } (by simp [Prog.set]) rfl
  | placeFails q x _ hq ht =>
    rw [fails_syncDir s s' ht]
    exact running_record cfg _ _ h (running_placeFails cfg s p h hr q x hq) q
      { x with stage := .refused } (by simp [Prog.set]) rfl
  | commitFails q x i c _ hq hst hc ha hseq hsize hcrc hok hgroups ht =>
    obtain ⟨k, rfl⟩ := fails_append s s' _ _ ht
    exact running_commit cfg s p h hr q x i c hq hst hc ha hseq hsize hcrc hok hgroups k false
      (fun h => by cases h)
  | publishFails _ ht =>
    rw [fails_sync s s' _ ht]
    exact running_publishFails cfg s p h hr
  | cleanFails q x name _ hq hst hn ht =>
    exact running_clean cfg s p h hr q x hq hst name hn s'
      (fails_whole s s' _ ht (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun h => by cases h))

/-- **A crash of the store running**, under what is assumed of the journal, recovers without
corruption, finding every article answered 240, and only commits whose records a run appended for
an article it did not refuse, each with the octets written for it and the CRC-32C its record
gives. -/
theorem running_crash (cfg : Config) (hkey : cfg.key.length = keyLength) (s : Fs) (p : Prog)
    (h : Hist) (hr : Running cfg s p h) (t : Fs) (hc : Crash s t) (ha : Assumed (viewOf p h) s t) :
    ∃ st ops, recover cfg (image t) = .ok (st, ops) ∧ (∀ c ∈ h.answered, c ∈ st.articles) ∧
      ∀ c ∈ st.articles, (∃ r, (r, c) ∈ h.appended ∧ (r, c.seq) ∉ h.refused) ∧
        (image t).lookup (finalName c.seq) = some (h.files c.seq) ∧
        (crc32c (h.files c.seq)).toNat = c.fileCrc := by
  obtain ⟨st, ops, _, hrec, ⟨hans, hart⟩, _⟩ := spool_crash cfg hkey s _ hr.spool t hc ha
  refine ⟨st, ops, hrec, hans, fun c hc => ⟨?_, (hart c hc).2.1, (hart c hc).2.2⟩⟩
  obtain ⟨⟨r, c'⟩, hm, rfl⟩ := List.mem_map.mp (hart c hc).1
  exact ⟨r, hm, hr.apart r c' hm⟩

/-- **A restart of the store running**, while no sync of the journal or the directory has failed
and numbers last, under what is assumed of the journal: the start keeps the spool, as
`start_safe` says. -/
theorem running_restart (cfg : Config) (hkey : cfg.key.length = keyLength) (s : Fs) (p : Prog)
    (h : Hist) (hr : Running cfg s p h) (ht : p.trusting = true)
    (ha : RestartAssumed (viewOf p h) s) (hroom : p.next + 2 < 2 ^ 64) :
    image (startSyncs s) = image (s.crashWith s.current) ∧
    ∃ st acts, recover cfg (image (startSyncs s)) = .ok (st, acts) ∧
      Recovers (viewOf p h) (image (startSyncs s)) st ∧
      Safe (Point cfg (viewOf p h) (p.next + 1)) (Failed cfg (viewOf p h) (p.next + 1)) s
        (startOps cfg s) ∧
      Started cfg (viewOf p h) st (s.run (startOps cfg s)) :=
  start_safe cfg hkey s _ hr.spool (hr.trusted ht) ha hroom

/-- The octets the journal's file keeps begin with its format under the program's key. -/
theorem running_format (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (hr : Running cfg s p h)
    (d : Data) (hd : s.data p.journal = some d) :
    (Record.format p.key).encode p.key 0 <+: d.kept := by
  have hne : (viewOf p h).phase ≠ .none := by simp [viewOf]
  obtain ⟨_, ij, d', _, hl, _, hd', hholds, _⟩ := hr.spool.journal hne
  rw [hr.lookup] at hl
  cases hl
  rw [hd] at hd'
  cases hd'
  have hk : d.kept = journal p.key p.records := hholds.kept
  rw [hk]
  exact format_prefix_journal _ _

/-! ## The premises can hold -/

/-- The examples' store: the journal of a run's start and the commit of article 1, the commit of
article 2 appended and not synced. -/
def wProg : Prog := ⟨sampleKey, wRecords, 0, 3, fun _ => none, some (articleOf 2), true, true, 0⟩

/-- What it has done: article 1 answered, both commits appended in run 0, none refused, `body`
written for each. -/
def wHist : Hist := ⟨[articleOf 1], [(0, articleOf 1), (0, articleOf 2)], [], fun _ => body⟩

/-- The premise `Running` can hold: of the examples' spool, with the commit of article 2 in
flight. -/
theorem running_witness : Running sampleConfig wSpool wProg wHist := by
  obtain ⟨_, _, hseen, _, htr⟩ := jSynced_steady
  refine ⟨spool_witness, wSpool_journal, wSpool_settled, fun _ => ⟨rfl, fun i d hi hd => ?_⟩,
    (fun _ => rfl), (fun _ h => by cases h), (fun c hc => ?_), (fun q x hx => by cases hx),
    (fun r c _ h => by cases h), (fun r q hq => ?_), (fun q hq => by cases hq), fun c hc => ?_⟩
  · rw [wSpool_journal] at hi
    cases hi
    have : wSpool.data 0 = some wJournal := rfl
    rw [this] at hd
    cases hd
    exact htr
  · cases hc
    exact ⟨articleOf_ok 2 (by decide) (by decide), fun _ => ⟨wJournal, rfl, by
      show jSynced.seen ++ wCommit = _; rw [hseen]; rfl⟩⟩
  · rcases hq with hq | ⟨c, hc, _⟩
    · cases hq
    · simp only [wHist, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact Nat.le_refl _
  · simp only [wHist, wProg, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
    rcases hc with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, rfl⟩

/-- The premises hold together with an article in flight: a number reserved in that store. -/
theorem running_inFlight_witness : ∃ p h x, Running sampleConfig wSpool p h ∧ p.posts 3 = some x :=
  ⟨_, _, ⟨body, 0, .reserved⟩, running_reserve sampleConfig _ _ _ running_witness body (by decide),
    by simp [Prog.set, wProg]⟩

/-- The premises hold together with an article in flight carried through every stage to its file
in place: a number reserved in that store, its file created, written whole, synced, moved and
placed. -/
theorem running_placed_witness : ∃ s p h x i, Running sampleConfig s p h ∧ p.posts 3 = some x ∧
    x.stage = .placed i := by
  have r1 := running_reserve sampleConfig _ _ _ running_witness body (by decide)
  have r2 := running_create sampleConfig _ _ _ r1 3 _ rfl rfl
  have r3 := running_write sampleConfig _ _ _ r2 3 _ wSpool.next body.length rfl rfl
  have r4 := running_sync sampleConfig _ _ _ r3 3 _ wSpool.next rfl rfl (by simp [Post.chunk])
  have r5 := running_rename sampleConfig _ _ _ r4 3 _ wSpool.next rfl rfl
  have r6 := running_place sampleConfig _ _ _ r5 3 _ wSpool.next rfl rfl rfl
  exact ⟨_, _, _, _, _, r6, rfl, rfl⟩

/-- The premise `Allocated` can hold: of article 2 after the examples' records. -/
theorem allocated_witness : Allocated sampleConfig wRecords (articleOf 2) := by
  intro g hg
  simp only [articleOf, List.mem_singleton] at hg
  subst hg
  exact ⟨by decide, by decide⟩

/-- The premise `Step` can hold, from that store: the journal synced over the commit of
article 2, and 240. -/
theorem step_witness : Step sampleConfig wSpool wProg wHist (wSpool.step (.sync 0)).1
    { wProg with records := wRecords ++ [.commit (articleOf 2)], committing := none }
    { wHist with answered := wHist.answered ++ [articleOf 2] } :=
  .publish _ _ _ (articleOf 2) rfl rfl

/-- The examples' program with article 2's file in place and no record in flight. -/
def wPlaced : Prog :=
  { wProg with
    committing := none
    posts := fun n => if n = 2 then some ⟨body, body.length, .placed 2⟩ else none }

/-- A commit step's premises hold together: article 2's file in place and its record appended. -/
theorem commit_witness : ∃ s' p' h', Step sampleConfig wSpool wPlaced wHist s' p' h' :=
  ⟨_, _, _, .commit _ _ _ 2 ⟨body, body.length, .placed 2⟩ 2 (articleOf 2) (by simp [wPlaced])
    rfl rfl rfl rfl rfl (by simp only [articleOf]) (articleOf_ok 2 (by decide) (by decide))
    allocated_witness⟩

/-- The premise `Owns` can hold: of article 2's file in that spool. -/
theorem owns_witness : Owns wSpool 2 2 := by
  intro e he hl
  simp only [wSpool, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp_all [Entry.Leaves]

/-- The premise `PostHolds` can hold: of article 2's file in place in that spool. -/
theorem postHolds_witness : PostHolds wSpool 2 ⟨body, body.length, .placed 2⟩ := by
  refine ⟨by decide, owns_witness, wFile, rfl, ?_⟩
  rw [wFile_eq]
  exact ⟨rfl, rfl, rfl⟩

/-- The premise `Rules` can hold: of the examples' records and the commit of article 2. -/
theorem rules_witness : Rules sampleConfig (commitsOf (wRecords ++ [.commit (articleOf 2)])) := by
  have := wRules 2 (Or.inr rfl)
  simpa using this

/-! ## Examples -/

/-- What the store's program does, for the examples. -/
inductive Cmd
  | reserve (o : Bytes)
  | create (q : Nat)
  | write (q m : Nat)
  | sync (q : Nat)
  | rename (q : Nat)
  | place (q : Nat)
  | commit (q : Nat) (c : Commit)
  | publish
  | refuse (q : Nat)
  | clean (q : Nat) (final : Bool)
  | drop (q : Nat)

/-- The article a command works on, if one. -/
def Cmd.post : Cmd → Option Nat
  | .create q | .write q _ | .sync q | .rename q | .place q => some q
  | _ => none

/-- The store as the examples run it. -/
structure St where
  fs : Fs
  prog : Prog
  hist : Hist

/-- What a command does when its operation succeeds (`after_step`). -/
def St.after (x : St) : Cmd → St
  | .reserve o => ⟨x.fs, { x.prog.set x.prog.next (some ⟨o, 0, .reserved⟩) with
      next := x.prog.next + 1 },
      { x.hist with files := fun n => if n = x.prog.next then o else x.hist.files n }⟩
  | .create q => match x.prog.posts q with
    | some y => ⟨(x.fs.step (.create (tempName q))).1,
        x.prog.set q (some { y with written := 0, stage := .writing x.fs.next }), x.hist⟩
    | none => x
  | .write q m => match x.prog.posts q with
    | some y => match y.stage with
      | .writing i => ⟨(x.fs.step (.append i (y.chunk m))).1,
          x.prog.set q (some { y with written := y.written + (y.chunk m).length }), x.hist⟩
      | _ => x
    | none => x
  | .sync q => match x.prog.posts q with
    | some y => match y.stage with
      | .writing i => ⟨(x.fs.step (.sync i)).1, x.prog.set q (some { y with stage := .synced i }),
          x.hist⟩
      | _ => x
    | none => x
  | .rename q => match x.prog.posts q with
    | some y => match y.stage with
      | .synced i => ⟨(x.fs.step (.rename (tempName q) (finalName q))).1,
          x.prog.set q (some { y with stage := .final i }), x.hist⟩
      | _ => x
    | none => x
  | .place q => match x.prog.posts q with
    | some y => match y.stage with
      | .final i => ⟨(x.fs.step .syncDir).1, x.prog.set q (some { y with stage := .placed i }),
          x.hist⟩
      | _ => x
    | none => x
  | .commit q c =>
    ⟨(x.fs.step (.append x.prog.journal (commitFrame x.prog.key x.prog.records c))).1,
      { x.prog.set q none with committing := some c },
      { x.hist with appended := x.hist.appended ++ [(x.prog.run, c)] }⟩
  | .publish => match x.prog.committing with
    | some c => ⟨(x.fs.step (.sync x.prog.journal)).1,
        { x.prog with records := x.prog.records ++ [.commit c], committing := none },
        { x.hist with answered := x.hist.answered ++ [c] }⟩
    | none => x
  | .refuse q => match x.prog.posts q with
    | some y => ⟨x.fs, x.prog.set q (some { y with stage := .refused }),
        { x.hist with refused := x.hist.refused ++ [(x.prog.run, q)] }⟩
    | none => x
  | .clean q f => ⟨(x.fs.step (.remove (if f then finalName q else tempName q))).1, x.prog, x.hist⟩
  | .drop q => ⟨x.fs, x.prog.set q none, x.hist⟩

/-- What a command needs for its operation to be a step of the store. -/
def Cmd.Allowed (cfg : Config) (x : St) : Cmd → Prop
  | .reserve _ => x.prog.next + 2 < 2 ^ 64
  | .create q => ∃ y, x.prog.posts q = some y ∧ y.stage = .reserved
  | .write q _ => ∃ y i, x.prog.posts q = some y ∧ y.stage = .writing i
  | .sync q => ∃ y i, x.prog.posts q = some y ∧ y.stage = .writing i ∧
      y.written = y.octets.length
  | .rename q => ∃ y i, x.prog.posts q = some y ∧ y.stage = .synced i
  | .place q => ∃ y i, x.prog.posts q = some y ∧ y.stage = .final i ∧ x.prog.trusting = true
  | .commit q c => ∃ y i, x.prog.posts q = some y ∧ y.stage = .placed i ∧
      x.prog.committing = none ∧ x.prog.accepting = true ∧ c.seq = q ∧
      c.fileSize = y.octets.length ∧ (crc32c y.octets).toNat = c.fileCrc ∧
      (Record.commit c).ok = true ∧ Allocated cfg x.prog.records c
  | .publish => ∃ c, x.prog.committing = some c ∧ x.prog.accepting = true
  | .refuse q => ∃ y, x.prog.posts q = some y
  | .clean q _ => ∃ y, x.prog.posts q = some y ∧ y.stage = .refused
  | .drop q => ∃ y, x.prog.posts q = some y ∧ y.stage = .refused

/-- **What the examples run are steps of the store**: a command its premises allow is a `Step`. -/
theorem after_step (cfg : Config) (x : St) (c : Cmd) (h : c.Allowed cfg x) :
    Step cfg x.fs x.prog x.hist (x.after c).fs (x.after c).prog (x.after c).hist := by
  cases c with
  | reserve o => exact .reserve _ _ _ o h
  | create q =>
    obtain ⟨y, hq, hs⟩ := h
    simp only [St.after, hq]
    exact .create _ _ _ q y hq hs
  | write q m =>
    obtain ⟨y, i, hq, hs⟩ := h
    simp only [St.after, hq, hs]
    rw [← hs]
    exact .write _ _ _ q y i m hq hs
  | sync q =>
    obtain ⟨y, i, hq, hs, hw⟩ := h
    simp only [St.after, hq, hs]
    exact .sync _ _ _ q y i hq hs hw
  | rename q =>
    obtain ⟨y, i, hq, hs⟩ := h
    simp only [St.after, hq, hs]
    exact .rename _ _ _ q y i hq hs
  | place q =>
    obtain ⟨y, i, hq, hs, ht⟩ := h
    simp only [St.after, hq, hs]
    exact .place _ _ _ q y i hq hs ht
  | commit q c =>
    obtain ⟨y, i, hq, hs, hc, ha, hseq, hsize, hcrc, hok, hg⟩ := h
    exact .commit _ _ _ q y i c hq hs hc ha hseq hsize hcrc hok hg
  | publish =>
    obtain ⟨c, hc, ha⟩ := h
    simp only [St.after, hc]
    exact .publish _ _ _ c hc ha
  | refuse q =>
    obtain ⟨y, hq⟩ := h
    simp only [St.after, hq]
    exact .refuse _ _ _ q y hq
  | clean q f =>
    obtain ⟨y, hq, hs⟩ := h
    exact .clean _ _ _ q y _ hq hs (by cases f <;> simp)
  | drop q =>
    obtain ⟨y, hq, hs⟩ := h
    exact .drop _ _ _ q y hq hs

/-- `Cmd.Allowed`, computed. -/
def Cmd.allowed (cfg : Config) (x : St) : Cmd → Bool
  | .reserve _ => decide (x.prog.next + 2 < 2 ^ 64)
  | .create q => match x.prog.posts q with
    | some ⟨_, _, .reserved⟩ => true
    | _ => false
  | .write q _ => match x.prog.posts q with
    | some ⟨_, _, .writing _⟩ => true
    | _ => false
  | .sync q => match x.prog.posts q with
    | some ⟨o, w, .writing _⟩ => w == o.length
    | _ => false
  | .rename q => match x.prog.posts q with
    | some ⟨_, _, .synced _⟩ => true
    | _ => false
  | .place q => match x.prog.posts q with
    | some ⟨_, _, .final _⟩ => x.prog.trusting
    | _ => false
  | .commit q c => match x.prog.posts q with
    | some ⟨o, _, .placed _⟩ => x.prog.committing.isNone && x.prog.accepting && c.seq == q &&
        c.fileSize == o.length && (crc32c o).toNat == c.fileCrc && (Record.commit c).ok &&
        c.groups.all fun g => cfg.groups.contains g.name &&
          decide (highIn (commitsOf x.prog.records) g.name < g.number)
    | _ => false
  | .publish => x.prog.committing.isSome && x.prog.accepting
  | .refuse q => (x.prog.posts q).isSome
  | .clean q _ | .drop q => match x.prog.posts q with
    | some ⟨_, _, .refused⟩ => true
    | _ => false

theorem allowed_sound (cfg : Config) (x : St) (c : Cmd) (h : c.allowed cfg x = true) :
    c.Allowed cfg x := by
  cases c with
  | reserve o => exact of_decide_eq_true (p := x.prog.next + 2 < 2 ^ 64) h
  | publish =>
    simp only [Cmd.allowed, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨c, hc⟩, ha⟩ := h
    exact ⟨c, hc, ha⟩
  | refuse q =>
    simp only [Cmd.allowed, Option.isSome_iff_exists] at h
    obtain ⟨y, hy⟩ := h
    exact ⟨y, hy⟩
  | create q | write q _ | sync q | rename q | place q | commit q _ | clean q _ | drop q =>
    simp only [Cmd.Allowed]
    cases hq : x.prog.posts q with
    | none => simp [Cmd.allowed, hq] at h
    | some y =>
      obtain ⟨o, w, st⟩ := y
      cases st <;> simp [Cmd.allowed, hq] at h
      all_goals first
        | exact ⟨_, rfl, rfl⟩
        | exact ⟨_, _, rfl, rfl⟩
        | exact ⟨_, _, rfl, rfl, h⟩
        | obtain ⟨⟨⟨⟨⟨⟨hc, ha⟩, hs⟩, hz⟩, hcrc⟩, hok⟩, hg⟩ := h
          exact ⟨_, _, rfl, rfl, hc, ha, hs, hz, hcrc, hok, hg⟩

/-- Whether each command of a run is allowed where it is run. -/
def allowedRun (cfg : Config) : St → List Cmd → Bool
  | _, [] => true
  | x, c :: cs => c.allowed cfg x && allowedRun cfg (x.after c) cs

/-- The premise `Cmd.Allowed` can hold: the commit of article 2, its file in place. -/
theorem allowed_witness :
    (Cmd.commit 2 (articleOf 2)).Allowed sampleConfig ⟨wSpool, wPlaced, wHist⟩ :=
  ⟨⟨body, body.length, .placed 2⟩, 2, by simp [wPlaced], rfl, rfl, rfl, rfl, rfl,
    by simp only [articleOf], articleOf_ok 2 (by decide) (by decide), allocated_witness⟩

/-- An article refused after a failure, the store accepting still. -/
def St.refusedAt (x : St) (q : Nat) (t : Fs) : St :=
  match x.prog.posts q with
  | some y => ⟨t, x.prog.set q (some { y with stage := .refused }),
      { x.hist with refused := x.hist.refused ++ [(x.prog.run, q)] }⟩
  | none => ⟨t, x.prog, x.hist⟩

/-- An article refused after a failed sync of its file: the store stops accepting. -/
def St.stoppedAt (x : St) (q : Nat) (t : Fs) : St :=
  match x.prog.posts q with
  | some y => ⟨t, { x.prog.set q (some { y with stage := .refused }) with accepting := false },
      { x.hist with refused := x.hist.refused ++ [(x.prog.run, q)] }⟩
  | none => ⟨t, x.prog, x.hist⟩

/-- An article refused after a failed sync of the directory: the store stops accepting and trusts
no later sync. -/
def St.untrustedAt (x : St) (q : Nat) (t : Fs) : St :=
  match x.prog.posts q with
  | some y => ⟨t, { x.prog.set q (some { y with stage := .refused }) with
        accepting := false
        trusting := false },
      { x.hist with refused := x.hist.refused ++ [(x.prog.run, q)] }⟩
  | none => ⟨t, x.prog, x.hist⟩

/-- What an operation that fails may leave, an append cut at its start, after one octet, half way
and one octet short. -/
def sampleFails (s : Fs) (op : Op) : List Fs :=
  match op with
  | .append i bs => ([0, 1, bs.length / 2, bs.length - 1].eraseDups.filter (· < bs.length)).map
      fun k => (s.step (.append i (bs.take k))).1
  | op => s.failures op

theorem sampleFails_fails (s t : Fs) (op : Op) (h : t ∈ sampleFails s op) : s.Fails t op := by
  unfold sampleFails at h
  split at h
  · rename_i i bs
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at h
    obtain ⟨k, ⟨_, hk⟩, rfl⟩ := h
    simp only [Fs.Fails, Fs.failures, List.mem_map, List.mem_range]
    exact ⟨k, by omega, rfl⟩
  · exact h

/-- What a command leaves when its operation fails (`fails_step`). -/
def St.fails (x : St) : Cmd → List St
  | .create q => (x.fs.failures (.create (tempName q))).map (x.refusedAt q)
  | .write q m => match x.prog.posts q with
    | some y => match y.stage with
      | .writing i => (sampleFails x.fs (.append i (y.chunk m))).map (x.refusedAt q)
      | _ => []
    | none => []
  | .sync q => match x.prog.posts q with
    | some y => match y.stage with
      | .writing i => (x.fs.failures (.sync i)).map (x.stoppedAt q)
      | _ => []
    | none => []
  | .rename q => (x.fs.failures (.rename (tempName q) (finalName q))).map (x.refusedAt q)
  | .place q => (x.fs.failures .syncDir).map (x.untrustedAt q)
  | .commit q c =>
    (sampleFails x.fs (.append x.prog.journal (commitFrame x.prog.key x.prog.records c))).map
      fun t => ⟨t, { x.prog.set q none with committing := some c, accepting := false },
        { x.hist with appended := x.hist.appended ++ [(x.prog.run, c)] }⟩
  | .publish => (x.fs.failures (.sync x.prog.journal)).map fun t =>
      ⟨t, { x.prog with accepting := false, trusting := false }, x.hist⟩
  | .clean q f => (x.fs.failures (.remove (if f then finalName q else tempName q))).map fun t =>
      ⟨t, x.prog, x.hist⟩
  | _ => []

/-- **What the examples leave of a failure are steps of the store**. -/
theorem fails_step (cfg : Config) (x : St) (c : Cmd) (h : c.Allowed cfg x) (u : St)
    (hu : u ∈ x.fails c) : Step cfg x.fs x.prog x.hist u.fs u.prog u.hist := by
  cases c with
  | create q =>
    obtain ⟨y, hq, hs⟩ := h
    simp only [St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simp only [St.refusedAt, hq]
    exact .createFails _ _ _ q y t hq hs ht
  | write q m =>
    obtain ⟨y, i, hq, hs⟩ := h
    simp only [St.fails, hq, hs, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simp only [St.refusedAt, hq]
    exact .writeFails _ _ _ q y i m t hq hs (sampleFails_fails _ _ _ ht)
  | sync q =>
    obtain ⟨y, i, hq, hs, _⟩ := h
    simp only [St.fails, hq, hs, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simp only [St.stoppedAt, hq]
    exact .syncFails _ _ _ q y i t hq hs ht
  | rename q =>
    obtain ⟨y, i, hq, hs⟩ := h
    simp only [St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simp only [St.refusedAt, hq]
    exact .renameFails _ _ _ q y i t hq hs ht
  | place q =>
    obtain ⟨y, _, hq, _, _⟩ := h
    simp only [St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simp only [St.untrustedAt, hq]
    exact .placeFails _ _ _ q y t hq ht
  | commit q c =>
    obtain ⟨y, i, hq, hs, hc, ha, hseq, hsize, hcrc, hok, hg⟩ := h
    simp only [St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact .commitFails _ _ _ q y i c t hq hs hc ha hseq hsize hcrc hok hg
      (sampleFails_fails _ _ _ ht)
  | publish =>
    simp only [St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact .publishFails _ _ _ t ht
  | clean q f =>
    obtain ⟨y, hq, hs⟩ := h
    simp only [St.fails, List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact .cleanFails _ _ _ q y _ t hq hs (by cases f <;> simp) ht
  | reserve o => simp [St.fails] at hu
  | refuse q => simp [St.fails] at hu
  | drop q => simp [St.fails] at hu

/-- After a failure, the article's names removed and the article forgotten, as the program does. -/
def St.cleanup (u : St) (q : Nat) : List St :=
  let u₁ := u.after (.clean q false)
  let u₂ := u₁.after (.clean q true)
  [u, u₁, u₂, u₂.after (.drop q)]

/-- How a crash may leave the names: as the directory's last sync left them, or as the program
sees them. -/
def liteNames (s : Fs) : List (List (Option Ino)) := [s.dir.map (·.synced), s.dir.map Entry.seen]

/-- How a crash may leave the files: each with what is kept, or with what the program sees; and the
journal with each of the octets `Data.cuts` gives it, the others either way. -/
def liteData (s : Fs) : List (List Bytes) :=
  [s.files.map (·.2.kept), s.files.map (·.2.seen)] ++
    match s.lookup journalName with
    | some j => match s.data j with
      | some d => ((Data.cuts d).filter d.leaves).flatMap fun c =>
          [s.files.map fun p => if p.1 == j then c else p.2.kept,
           s.files.map fun p => if p.1 == j then c else p.2.seen]
      | none => []
    | none => []

/-- Crashes of `s`, not all of them: the names and the files as `liteNames` and `liteData` give
them. -/
def liteCrashes (s : Fs) : List Fs :=
  ((liteNames s).flatMap fun ns => (liteData s).map fun ds => s.crashWith ⟨ns, ds⟩).eraseDups

theorem data_of_mem (s : Fs) (hs : s.Ok) (p : Ino × Data) (hp : p ∈ s.files) :
    s.data p.1 = some p.2 := by
  simp only [Fs.data, FsModel.lookup_eq_find, FsModel.find_key s.files hs.2.1 p hp,
    Option.map_some]

/-- **Every crash `liteCrashes` lists is a crash.** -/
theorem liteCrashes_crash (s : Fs) (hs : s.Ok) (t : Fs) (ht : t ∈ liteCrashes s) : Crash s t := by
  simp only [liteCrashes, List.mem_eraseDups, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨ns, hns, ds, hds, rfl⟩ := ht
  have hok : ∀ p ∈ s.files, p.2.Ok := hs.2.2.2.1
  have hkept : ∀ p ∈ s.files, p.2.Leaves p.2.kept := fun p hp =>
    ⟨List.prefix_refl _, Nat.le_trans (hok p hp).1.length_le (hok p hp).2⟩
  refine ⟨⟨ns, ds⟩, ⟨?_, ?_⟩, rfl⟩
  · simp only [liteNames, List.mem_cons, List.not_mem_nil, or_false] at hns
    rcases hns with rfl | rfl
    · exact FsModel.each_map _ _ _ fun e _ => Or.inl rfl
    · exact FsModel.each_map _ _ _ fun e _ => FsModel.entry_leaves_seen e
  · simp only [liteData, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hds
    rcases hds with (rfl | rfl) | hds
    · exact FsModel.each_map _ _ _ fun p hp => hkept p hp
    · exact FsModel.each_map _ _ _ fun p hp => FsModel.leaves_seen _ (hok p hp)
    · split at hds
      · rename_i j hj
        split at hds
        · rename_i d hd
          simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, List.not_mem_nil,
            or_false] at hds
          obtain ⟨c, ⟨_, hc⟩, hds⟩ := hds
          have hjd : ∀ p ∈ s.files, p.1 = j → p.2 = d := fun p hp he => by
            have := data_of_mem s hs p hp; rw [he, hd] at this; exact (Option.some.inj this).symm
          rcases hds with rfl | rfl
          · refine FsModel.each_map _ _ _ fun p hp => ?_
            by_cases he : p.1 = j
            · simp only [he, beq_self_eq_true, ↓reduceIte]
              rw [hjd p hp he]; exact (FsModel.leaves_iff d c).mp hc
            · simp only [show (p.1 == j) = false by simpa using he, Bool.false_eq_true,
                ↓reduceIte]
              exact hkept p hp
          · refine FsModel.each_map _ _ _ fun p hp => ?_
            by_cases he : p.1 = j
            · simp only [he, beq_self_eq_true, ↓reduceIte]
              rw [hjd p hp he]; exact (FsModel.leaves_iff d c).mp hc
            · simp only [show (p.1 == j) = false by simpa using he, Bool.false_eq_true,
                ↓reduceIte]
              exact FsModel.leaves_seen _ (hok p hp)
        · cases hds
      · cases hds

/-- Whether every crash `liteCrashes` lists recovers under `cfg` with every article answered, and
only commits appended for articles not refused, each with the octets written for it and their
CRC-32C. -/
def recoversAll (cfg : Config) (u : St) : Bool :=
  (liteCrashes u.fs).all fun t =>
    match recover cfg (image t) with
    | .ok (st, _) => u.hist.answered.all (st.articles.contains ·) &&
        st.articles.all fun c =>
          u.hist.appended.any (fun a => a.2 == c && !u.hist.refused.contains (a.1, c.seq)) &&
          (image t).lookup (finalName c.seq) == some (u.hist.files c.seq) &&
          (crc32c (u.hist.files c.seq)).toNat == c.fileCrc
    | .error _ => false

/-- Every point of a run of commands, and whatever each leaves when its operation fails, followed,
for an article, by its names removed and the article forgotten. -/
def runOn (x : St) : List Cmd → List St
  | [] => [x]
  | c :: cs => x :: (x.fails c).flatMap (fun u => match c.post with
      | some q => u.cleanup q
      | none => [u]) ++ runOn (x.after c) cs

/-- A second article, of another length. -/
def bodyB : Bytes := ascii "Subject: x\r\n\r\nyyyy\r\n"

/-- The commit of an article numbered `seq` in the sample group with `number`, its file `o`. -/
def commitFor (seq number : Nat) (o : Bytes) : Commit :=
  ⟨seq, ascii "<x@y>" ++ [BitVec.ofNat 8 seq], [⟨ascii "local.test", number⟩], 14, o.length,
    (crc32c o).toNat⟩

/-- A store just started: the journal of a run's start, synced, and its name. -/
def startSt : St :=
  ⟨Fs.empty.run started, ⟨sampleKey, [.start], 0, 1, fun _ => none, none, true, true, 0⟩,
    ⟨[], [], [], fun _ => []⟩⟩

/-- Two articles reserved, created and written before either is placed. -/
def written2 : List Cmd :=
  [.reserve body, .reserve bodyB, .create 1, .create 2, .write 1 100, .sync 1, .rename 1,
    .write 2 100, .sync 2, .rename 2]

/-- **Articles in flight together**: three reserved and created, written in parts in turn, one
refused, its name removed and forgotten, the other two moved, placed and committed one at a time,
the second placed while the first's record is in flight, each command a step where it is run. Every
crash listed at every point, and of whatever each operation leaves when it fails and the cleaning
after, recovers with every article answered and only commits appended for articles not refused,
each file the octets written; and both articles end answered. -/
def regression_922 : Bool :=
  let script : List Cmd :=
    [.reserve body, .reserve bodyB, .reserve body, .create 1, .create 2, .create 3, .write 1 5,
      .write 2 3, .write 3 4, .write 1 100, .sync 1, .refuse 3, .clean 3 false, .drop 3,
      .write 2 100, .sync 2, .rename 2, .rename 1, .place 1, .commit 1 (commitFor 1 1 body),
      .place 2, .publish, .commit 2 (commitFor 2 2 bodyB), .publish]
  allowedRun sampleConfig startSt script && (runOn startSt script).all (recoversAll sampleConfig) &&
    (script.foldl St.after startSt).hist.answered == [commitFor 1 1 body, commitFor 2 2 bodyB]

/-- 240 given with the record appended and not yet synced. -/
def answerEarly (x : St) : St :=
  match x.prog.committing with
  | some c => ⟨x.fs, x.prog, { x.hist with answered := x.hist.answered ++ [c] }⟩
  | none => x

/-- After the record's write failed, the store going on accepting as if it had not. -/
def goOn (x : St) (c : Commit) : St :=
  ⟨(x.fs.step (.append x.prog.journal ((commitFrame x.prog.key x.prog.records c).take 5))).1,
    x.prog.set 1 none, { x.hist with appended := x.hist.appended ++ [(x.prog.run, c)] }⟩

/-- **What the program must do**, each broken once: a commit appended before the directory is
synced after the move, one giving another size, one with an article number not above the group's
last, one in a group the store does not carry, one the journal cannot hold, one naming a number
whose file is not in place, two records appended before either is synced, 240 before the journal's
sync, and the store going on accepting after the record's write failed — each leaves a crash that
recovery refuses or that loses an article answered, the first seven by a command `Cmd.Allowed`
rules out; with all kept, every command allowed, none does. -/
def regression_923 : Bool :=
  let c1 := commitFor 1 1 body
  let fine := written2 ++ [.place 1, .commit 1 c1, .publish, .place 2,
    .commit 2 (commitFor 2 2 bodyB), .publish]
  let broken (cs : List Cmd) := !allowedRun sampleConfig startSt (written2 ++ cs) &&
    !(runOn startSt (written2 ++ cs)).all (recoversAll sampleConfig)
  broken [.commit 1 c1, .publish] &&
    broken [.place 1, .commit 1 (commitFor 1 1 bodyB), .publish] &&
    broken [.place 1, .commit 1 c1, .publish, .place 2, .commit 2 (commitFor 2 1 bodyB),
      .publish] &&
    broken [.place 1, .commit 1 { c1 with groups := [⟨ascii "local.other", 1⟩] }, .publish] &&
    broken [.place 1, .commit 1 { c1 with groups := [] }, .publish] &&
    broken [.reserve body, .place 1, .commit 1 (commitFor 3 1 body), .publish] &&
    broken [.place 1, .place 2, .commit 1 c1, .commit 2 (commitFor 2 2 bodyB), .publish] &&
    !((runOn startSt (written2 ++ [.place 1, .commit 1 c1])).map answerEarly).all
      (recoversAll sampleConfig) &&
    !(runOn (goOn ((written2 ++ ([.place 1, .place 2] : List Cmd)).foldl St.after startSt) c1)
      [.commit 2 (commitFor 2 2 bodyB), .publish]).all (recoversAll sampleConfig) &&
    allowedRun sampleConfig startSt fine && (runOn startSt fine).all (recoversAll sampleConfig)

end DN.News.StoreOps
