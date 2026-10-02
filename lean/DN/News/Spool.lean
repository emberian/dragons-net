-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.JournalCrash
import DN.News.Recovery

/-!
# DN.News.Spool

The spool directory on the file system of `DN.News.FsModel`, as docs/decisions/0005-article-store.md
says the store keeps it, and what recovery (`DN.News.Recovery`) finds after a crash of it or a
restart. Recovery reads the directory as each name that holds a file, with the octets the program
sees there (`image`).

The store's knowledge and history is a `View`: where the journal is (`Phase`), the articles answered
240, the commits whose records it appended, the octets it wrote for each sequence number, and a
bound on the numbers. The spool as the store keeps it is `Spool`: every name of a shape recovery
reads, numbered below the bound, with room for one more; no file before a journal; the journal's
file in the state `DN.News.JournalCrash` gives its phase, under no other name; no other file while
the journal has no format or its name is not settled, and no article answered then; the file of
every commit kept, or that a crash may leave whole where the records end, in place — its final name
and its octets settled, of the size and CRC-32C its commit gives (`Placed`); the rules across
commits that recovery checks kept, with or without that commit; and every article answered kept,
every commit kept appended.

Proven: a crash of a spool, under what is assumed of the journal (`Assumed`), recovers without
corruption, finding every article answered and only commits the store appended, each with the file
it wrote and that file's CRC-32C (`spool_crash`); what the crash left is a spool again — the journal
gone with every other file, left with no format, or read as its records — so the next start begins
from a spool. A restart, its syncs trusted, is read as a crash that lost nothing, and what the start
has synced is a spool again (`spool_restart`), assuming only what is assumed past the journal's
format. That recovery's own actions keep a spool, so that a crash during them is like any other,
`DN.News.RecoveryRun` proves.
-/

namespace DN.News.Spool

open DN.News.Journal
open DN.News.FsModel (Data Entry Fs Ino Crash crash_lookup crash_data crash_ok crash_settles
  crashDir crashDir_names lookup_held find_key lookup_eq_find leaves_exact find_name)
open DN.News.Recovery
open DN.News.JournalCrash
open DN.News.CommandSpec (ascii)

/-! ## The directory as recovery reads it -/

/-- Each name that holds a file, with the octets the program sees there. -/
def image (s : Fs) : Image :=
  s.dir.filterMap fun e => e.seen.bind fun i => (s.data i).map fun d => (e.name, d.seen)

theorem lookup_filterMap (name : Bytes) :
    ∀ (es : List Entry) (f : Entry → Option (Bytes × Bytes)),
      (∀ e p, f e = some p → p.1 = e.name) → (es.map Entry.name).Nodup →
      (es.filterMap f).lookup name = ((es.find? (·.name == name)).bind f).map Prod.snd
  | [], _, _, _ => rfl
  | e :: es, f, hf, hn => by
    simp only [List.map_cons, List.nodup_cons] at hn
    have ih := lookup_filterMap name es f hf hn.2
    by_cases he : e.name = name
    · subst he
      have hfind : es.find? (·.name == e.name) = none := by
        rw [List.find?_eq_none]
        intro x hx h
        simp only [beq_iff_eq] at h
        exact hn.1 (h ▸ List.mem_map_of_mem hx)
      have hnone : (es.filterMap f).lookup e.name = none := by rw [ih, hfind]; rfl
      have hfirst : (e :: es).find? (·.name == e.name) = some e := by simp
      rw [hfirst, Option.bind_some, List.filterMap_cons]
      cases hfe : f e with
      | none => simpa using hnone
      | some p =>
        obtain ⟨a, b⟩ := p
        have ha : a = e.name := hf e _ hfe
        subst ha
        simp
    · have hrest : (e :: es).find? (·.name == name) = es.find? (·.name == name) := by
        simp [he]
      rw [hrest, List.filterMap_cons]
      cases hfe : f e with
      | none => exact ih
      | some p =>
        obtain ⟨a, b⟩ := p
        have ha : a = e.name := hf e _ hfe
        subst ha
        have hb : (name == e.name) = false := by
          simp only [beq_eq_false_iff_ne]; exact fun h => he h.symm
        rw [List.lookup_cons, hb]
        exact ih

/-- **What recovery reads under a name** is the file the program finds there, as it sees it. -/
theorem image_lookup (s : Fs) (hs : s.Ok) (name : Bytes) :
    (image s).lookup name = (s.lookup name).bind fun i => (s.data i).map (·.seen) := by
  simp only [image, Fs.lookup, Fs.entry]
  rw [lookup_filterMap name s.dir _ ?_ hs.1]
  · cases s.dir.find? (·.name == name) with
    | none => rfl
    | some e =>
      simp only [Option.bind_some]
      cases e.seen with
      | none => rfl
      | some i =>
        simp only [Option.bind_some]
        cases s.data i <;> rfl
  · intro e p hp
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨_, _, _, _, rfl⟩ := hp
    rfl

/-- Every name recovery reads is a name of the directory. -/
theorem image_names (s : Fs) (p : Bytes × Bytes) (hp : p ∈ image s) :
    ∃ e ∈ s.dir, e.name = p.1 := by
  simp only [image, List.mem_filterMap, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
  obtain ⟨e, he, _, _, _, _, rfl⟩ := hp
  exact ⟨e, he, rfl⟩

/-- The names that hold a file, with the file each holds. -/
def named (s : Fs) : List (Bytes × Ino) := s.dir.filterMap fun e => e.seen.map (e.name, ·)

theorem image_named (s : Fs) :
    image s = (named s).filterMap fun p => (s.data p.2).map fun d => (p.1, d.seen) := by
  simp only [image, named, List.filterMap_filterMap]
  congr 1
  funext e
  cases e.seen <;> rfl

theorem filterMap_congr {α β : Type} (f g : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr f g l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **Recovery reads the same** of two file systems whose names hold the same files, and whose
files those names hold the program sees alike. -/
theorem image_eq (s u : Fs) (hn : named u = named s)
    (hf : ∀ p ∈ named s, (u.data p.2).map (·.seen) = (s.data p.2).map (·.seen)) :
    image u = image s := by
  rw [image_named, image_named, hn]
  exact filterMap_congr _ _ _ fun p hp => by
    have := hf p hp
    cases hu : u.data p.2 <;> cases hs : s.data p.2 <;> simp_all

theorem named_settle (dir : List Entry) :
    (dir.filterMap Entry.settle).filterMap (fun e => e.seen.map (e.name, ·)) =
      dir.filterMap fun e => e.seen.map (e.name, ·) := by
  rw [List.filterMap_filterMap]
  congr 1
  funext e
  simp only [Entry.settle]
  cases e.seen <;> rfl

theorem crashDir_current : ∀ es : List Entry,
    FsModel.crashDir es (es.map Entry.seen) = es.filterMap Entry.settle
  | [] => rfl
  | e :: es => by
    simp only [List.map_cons, List.filterMap_cons, Entry.settle]
    cases h : e.seen with
    | none => simp [FsModel.crashDir, crashDir_current es]
    | some i => simp [FsModel.crashDir, crashDir_current es]

theorem lookup_change (j i : Ino) (f : Data → Data) : ∀ ps : List (Ino × Data),
    (FsModel.change ps i f).lookup j = (ps.lookup j).map fun d => if j = i then f d else d
  | [] => rfl
  | (k, d) :: ps => by
    have ih := lookup_change j i f ps
    simp only [FsModel.change, List.map_cons, beq_iff_eq] at ih ⊢
    by_cases hj : j = k
    · subst hj
      by_cases hk : j = i
      · subst hk; simp
      · simp [hk]
    · have hb : (j == k) = false := by simp [hj]
      by_cases hk : k = i
      · simp only [hk, ↓reduceIte, List.lookup_cons]
        rw [← hk] at ih ⊢
        simp only [hb]
        exact ih
      · simp only [hk, ↓reduceIte, List.lookup_cons, hb]
        exact ih

/-- An operation on a file's data that leaves what the program sees leaves what recovery reads. -/
theorem image_onData (s : Fs) (i : Ino) (f : Data → Data) (hf : ∀ d, (f d).seen = d.seen) :
    image (s.onData i f).1 = image s := by
  unfold Fs.onData
  split
  · refine image_eq s _ rfl fun p _ => ?_
    simp only [Fs.data, lookup_change]
    cases s.files.lookup p.2 with
    | none => rfl
    | some d => simp only [Option.map_some]; split <;> simp [hf]
  · rfl

/-- A sync of the directory leaves what recovery reads. -/
theorem image_syncDir (s : Fs) : image (s.step .syncDir).1 = image s := by
  simp only [Fs.step]
  split
  · exact image_eq s _ (named_settle s.dir) fun _ _ => rfl
  · rfl

theorem lookup_crashFiles_current (i : Ino) : ∀ ps : List (Ino × Data),
    (FsModel.crashFiles ps (ps.map fun p => p.2.seen)).lookup i =
      (ps.lookup i).map fun d => d.after d.seen
  | [] => rfl
  | (k, d) :: ps => by
    simp only [List.map_cons, FsModel.crashFiles, List.lookup_cons]
    split <;> simp [lookup_crashFiles_current i ps]

/-- **A crash that loses nothing is read as the file system it left.** -/
theorem image_current (s : Fs) : image (s.crashWith s.current) = image s := by
  refine image_eq s _ ?_ fun p hp => ?_
  · simp only [named, Fs.crashWith, Fs.prune, Fs.current, crashDir_current]
    exact named_settle s.dir
  · obtain ⟨e, he, hpm⟩ := List.mem_filterMap.mp hp
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hpm
    have hh : (Fs.mk (FsModel.crashDir s.dir (s.dir.map Entry.seen))
        (FsModel.crashFiles s.files (s.files.map fun p => p.2.seen)) s.next true).holds i =
          true := by
      simp only [Fs.holds, crashDir_current, List.any_eq_true]
      refine ⟨⟨e.name, some i, []⟩, List.mem_filterMap.mpr ⟨e, he, ?_⟩, ?_⟩
      · simp [Entry.settle, hi]
      · simp [Entry.holds, Entry.Leaves]
    simp only [Fs.data, Fs.crashWith, Fs.prune, Fs.current, FsModel.lookup_filter, hh, ↓reduceIte,
      lookup_crashFiles_current]
    cases s.files.lookup i <;> rfl

/-! ## What the store keeps -/

/-- Where the journal is. -/
inductive Phase
  /-- no journal, and no file in the directory -/
  | none
  /-- its format being written -/
  | creating
  /-- a crash left it with no format -/
  | unformatted
  /-- its format and the records `rs` kept under `k`; `back` what a crash may leave whole where
  they end -/
  | steady (k : Bytes) (rs back : List Record)
  /-- a crash left it reading as the records `rs` under `k`, before any cut -/
  | found (k : Bytes) (rs back : List Record)

def Phase.kept : Phase → List Record
  | .steady _ rs _ | .found _ rs _ => rs
  | _ => []

def Phase.back : Phase → List Record
  | .steady _ _ back | .found _ _ back => back
  | _ => []

/-- What the journal's data is in a phase. -/
def Phase.Holds : Phase → Data → Prop
  | .none, _ => False
  | .creating, d => Creating d ∧ (d.seen = [] ∨ (0, d.seen) ∈ d.written)
  | .unformatted, d => Unformatted d
  | .steady k rs back, d => Steady k rs (· ∈ back) d
  | .found k rs back, d => Found k rs (· ∈ back) d

/-- What the store knows and what it has done: where the journal is, the articles answered 240, the
commits whose records it appended, the octets it wrote for each sequence number, and a number above
every sequence number a name or a record carries. -/
structure View where
  phase : Phase
  answered : List Commit
  appended : List Commit
  files : Nat → Bytes
  next : Nat

/-- The rules recovery checks across commits, kept. -/
def Rules (cfg : Config) (cs : List Commit) : Prop :=
  seqTwice? cs = none ∧ notAbove? [] cs = none ∧ unknownGroup? cfg cs = none

/-- **The file of a commit in place**: its final name settled, holding a file all of whose octets
are kept, the octets the store wrote for it, of the size and CRC-32C the commit gives. -/
def Placed (s : Fs) (files : Nat → Bytes) (c : Commit) : Prop :=
  ∃ e i d, s.entry (finalName c.seq) = some e ∧ e.Settled ∧ e.synced = some i ∧
    s.data i = some d ∧ d.kept = d.seen ∧ d.high = d.seen.length ∧ d.seen = files c.seq ∧
    (files c.seq).length = c.fileSize ∧ (crc32c (files c.seq)).toNat = c.fileCrc

/-- The journal's name not settled in the directory, or not there. -/
def Unsettled (s : Fs) : Prop := ∀ e, s.entry journalName = some e → ¬ e.Settled

/-- No name but the journal's may be left holding a file. -/
def Alone (s : Fs) : Prop := ∀ e ∈ s.dir, e.name ≠ journalName → ∀ i, ¬ e.Leaves (some i)

/-- No name but the journal's may be left holding file `i`. -/
def Apart (s : Fs) (i : Ino) : Prop := ∀ e ∈ s.dir, e.name ≠ journalName → ¬ e.Leaves (some i)

/-- **The spool as the store keeps it**: every name of a shape recovery reads, numbered below
`next`, and room for one more number past it; no file at all before a journal, and the journal's
file as its phase says, held under no other name; no other file while the journal has no format or
its name is not settled, nor any article answered; the file of every commit kept, or that a crash
may leave whole, in place; the rules across commits kept, with or without that one; and every
article answered kept, every commit kept appended. -/
structure Spool (cfg : Config) (s : Fs) (v : View) : Prop where
  ok : s.Ok
  names : ∀ e ∈ s.dir, ∃ n, parseName e.name = some n ∧ ∀ q, seqOf n = some q → q < v.next
  room : 1 ≤ v.next ∧ v.next + 1 < 2 ^ 64
  empty : v.phase = .none → ∀ e ∈ s.dir, ∀ i, ¬ e.Leaves (some i)
  journal : v.phase ≠ .none → ∃ e ij d, s.entry journalName = some e ∧
    s.lookup journalName = some ij ∧ (∀ b, e.Leaves b → b = none ∨ b = some ij) ∧
    s.data ij = some d ∧ v.phase.Holds d ∧ Apart s ij
  alone : v.phase = .creating ∨ v.phase = .unformatted ∨ Unsettled s → Alone s
  quiet : Unsettled s → v.answered = []
  placed : ∀ c ∈ commitsOf (v.phase.kept ++ v.phase.back), Placed s v.files c
  rules : Rules cfg (commitsOf v.phase.kept) ∧
    ∀ r ∈ v.phase.back, Rules cfg (commitsOf (v.phase.kept ++ [r]))
  seqs : ∀ c ∈ commitsOf (v.phase.kept ++ v.phase.back), c.seq < v.next
  answered : ∀ c ∈ v.answered, c ∈ commitsOf v.phase.kept
  appended : ∀ c ∈ commitsOf (v.phase.kept ++ v.phase.back), c ∈ v.appended

/-- **Assumed of a crash of the spool**, of the journal's file: once its format is kept, what
`Unforged` assumes; while it is written, what `FormatWritten` assumes. -/
def Assumed (v : View) (s t : Fs) : Prop :=
  ∀ i d d', t.lookup journalName = some i → s.data i = some d → t.data i = some d' →
    match v.phase with
    | .creating => FormatWritten d d'.seen
    | .steady k _ _ => Unforged k d d'.seen
    | _ => True

/-! ## What a crash leaves of the spool -/

/-- A name a crash leaves holding a file was one the name could be left holding. -/
theorem crash_held (s t : Fs) (hs : s.Ok) (h : Crash s t) (name : Bytes) (i : Ino)
    (hl : t.lookup name = some i) : ∃ e, s.entry name = some e ∧ e.Leaves (some i) := by
  have hc := crash_lookup s t hs h name
  rw [hl] at hc
  unfold Fs.Leaves at hc
  cases he : s.entry name with
  | none => rw [he] at hc; cases hc
  | some e => rw [he] at hc; exact ⟨e, rfl, hc⟩

/-- A file a name holds is there. -/
theorem data_some (s : Fs) (hs : s.Ok) (name : Bytes) (i : Ino) (hl : s.lookup name = some i) :
    ∃ d, s.data i = some d := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (lookup_held s hs name i hl)
  refine ⟨p.2, ?_⟩
  simp only [Fs.data, lookup_eq_find, find_key s.files hs.2.1 p hp, Option.map_some]

/-- Every name a crash leaves is a name of the directory before it. -/
theorem crash_names (s t : Fs) (h : Crash s t) (e : Entry) (he : e ∈ t.dir) :
    ∃ e₀ ∈ s.dir, e₀.name = e.name := by
  obtain ⟨c, _, rfl⟩ := h
  have hm : e.name ∈ (crashDir s.dir c.names).map Entry.name := List.mem_map_of_mem he
  obtain ⟨e₀, he₀, hn⟩ := List.mem_map.mp ((crashDir_names s.dir c.names).subset hm)
  exact ⟨e₀, he₀, hn⟩

/-- What a crash leaves under a name is settled. -/
theorem crash_entry (s t : Fs) (h : Crash s t) (name : Bytes) (e : Entry)
    (he : t.entry name = some e) : e.Settled :=
  (crash_settles s t h).2.1 e (List.mem_of_find?_eq_some he)

/-- **A commit's file in place stays in place** through a crash, and recovery reads it whole. -/
theorem crash_placed (s t : Fs) (hs : s.Ok) (h : Crash s t) (files : Nat → Bytes) (c : Commit)
    (hp : Placed s files c) :
    Placed t files c ∧ (image t).lookup (finalName c.seq) = some (files c.seq) := by
  obtain ⟨e, i, d, he, ⟨hheld, _⟩, hsyn, hd, hk, hh, hseen, hlen, hcrc⟩ := hp
  have ht := crash_ok s t hs h
  have hl : t.lookup (finalName c.seq) = some i := by
    have hc := crash_lookup s t hs h (finalName c.seq)
    unfold Fs.Leaves at hc
    rw [he] at hc
    rcases hc with hc | hc
    · rw [hc, hsyn]
    · rw [hheld] at hc; cases hc
  obtain ⟨d', hd'⟩ := data_some t ht _ i hl
  obtain ⟨cc, hcc, hor⟩ := (crash_data s t hs h i).1 d hd
  have hcc' := (leaves_exact d hk hh cc).mp hcc
  subst hcc'
  have hdt : t.data i = some (d.after d.seen) := by
    rcases hor with hor | hor
    · exact hor
    · rw [hor] at hd'; cases hd'
  obtain ⟨e', he', hsome⟩ : ∃ e', t.entry (finalName c.seq) = some e' ∧ e'.seen = some i := by
    simp only [Fs.lookup, Option.bind_eq_some_iff] at hl
    exact hl
  have hset := crash_entry s t h _ e' he'
  refine ⟨⟨e', i, d.after d.seen, he', hset, ?_, hdt, rfl, rfl, hseen, hlen, hcrc⟩, ?_⟩
  · have : e'.seen = e'.synced := by simp [Entry.seen, hset.1]
    rw [← this, hsome]
  · rw [image_lookup t ht, hl, Option.bind_some, hdt, Option.map_some]
    exact congrArg some hseen

/-- What a crash leaves under the journal's name: nothing, or the journal's file, holding octets a
crash may leave of it. -/
theorem crash_journal (s t : Fs) (hs : s.Ok) (h : Crash s t) (e : Entry) (ij : Ino) (d : Data)
    (he : s.entry journalName = some e) (hb : ∀ b, e.Leaves b → b = none ∨ b = some ij)
    (hd : s.data ij = some d) :
    t.lookup journalName = none ∨ t.lookup journalName = some ij ∧
      ∃ c, d.Leaves c ∧ t.data ij = some (d.after c) := by
  have hc := crash_lookup s t hs h journalName
  unfold Fs.Leaves at hc
  rw [he] at hc
  rcases hb _ hc with hl | hl
  · exact Or.inl hl
  · refine Or.inr ⟨hl, ?_⟩
    obtain ⟨c, hcl, hor⟩ := (crash_data s t hs h ij).1 d hd
    refine ⟨c, hcl, ?_⟩
    rcases hor with hor | hor
    · exact hor
    · obtain ⟨d', hd'⟩ := data_some t (crash_ok s t hs h) _ ij hl
      rw [hor] at hd'; cases hd'

/-- The file an entry of a file system as operations leave it holds is what the program finds under
its name. -/
theorem lookup_entry (s : Fs) (hs : s.Ok) (e : Entry) (he : e ∈ s.dir) :
    s.entry e.name = some e ∧ s.lookup e.name = e.seen := by
  have := find_name s.dir hs.1 e he
  exact ⟨this, by simp [Fs.lookup, Fs.entry, this]⟩

/-- **A file no other name could hold, no other name holds after a crash.** -/
theorem crash_apart (s t : Fs) (hs : s.Ok) (h : Crash s t) (i : Ino) (ha : Apart s i) :
    Apart t i := by
  intro e he hn hl
  have hset := crash_entry s t h e.name e (lookup_entry t (crash_ok s t hs h) e he).1
  have hseen : e.seen = some i := by
    rcases hl with hl | hl
    · simp [Entry.seen, hset.1, hl]
    · rw [hset.1] at hl; cases hl
  have hlook := (lookup_entry t (crash_ok s t hs h) e he).2
  rw [hseen] at hlook
  obtain ⟨e₀, he₀, hl₀⟩ := crash_held s t hs h e.name i hlook
  have hname : e₀.name = e.name := by
    have := List.find?_some he₀
    simpa using this
  exact ha e₀ (List.mem_of_find?_eq_some he₀) (hname ▸ hn) hl₀

/-- With no other name able to hold a file, none can after a crash. -/
theorem crash_alone (s t : Fs) (hs : s.Ok) (h : Crash s t) (ha : Alone s) : Alone t :=
  fun e he hn i => crash_apart s t hs h i (fun e' he' hn' => ha e' he' hn' i) e he hn

/-- With the journal's name left holding nothing and no other name holding a file, a crash leaves
an empty directory. -/
theorem crash_empty (s t : Fs) (hs : s.Ok) (h : Crash s t) (ha : Alone s)
    (hj : t.lookup journalName = none) : t.dir = [] := by
  cases hd : t.dir with
  | nil => rfl
  | cons e es =>
    exfalso
    have he : e ∈ t.dir := by rw [hd]; exact List.mem_cons_self ..
    have hset := crash_entry s t h e.name e (lookup_entry t (crash_ok s t hs h) e he).1
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hset.2
    by_cases hn : e.name = journalName
    · have hlook := (lookup_entry t (crash_ok s t hs h) e he).2
      rw [hn, hj] at hlook
      simp [Entry.seen, hset.1, hi] at hlook
    · exact crash_alone s t hs h ha e he hn i (Or.inl hi.symm)

/-- No file anywhere: recovery reads nothing. -/
theorem image_nil (s : Fs) (h : s.dir = []) : image s = [] := by
  simp [image, h]

/-- What a crash leaves when no name but the journal's held a file: the journal alone, if any. -/
theorem crash_image_alone (s t : Fs) (hs : s.Ok) (h : Crash s t) (ha : Alone s) (ij : Ino)
    (d : Data) (hj : t.lookup journalName = some ij) (hd : t.data ij = some d) :
    image t = [(journalName, d.seen)] := by
  have ht := crash_ok s t hs h
  have hat := crash_alone s t hs h ha
  have hall : ∀ e ∈ t.dir, e.name = journalName := by
    intro e he
    refine Classical.byContradiction fun hn => ?_
    have hset := crash_entry s t h e.name e (lookup_entry t ht e he).1
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hset.2
    exact hat e he hn i (Or.inl hi.symm)
  have hn := ht.1
  cases hdir : t.dir with
  | nil =>
    simp [Fs.lookup, Fs.entry, hdir] at hj
  | cons e es =>
    cases es with
    | cons e₂ es =>
      rw [hdir] at hn hall
      have h1 := hall e (List.mem_cons_self ..)
      have h2 := hall e₂ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      simp [h1, h2] at hn
    | nil =>
      rw [hdir] at hall
      have h1 := hall e (List.mem_cons_self ..)
      have hseen : e.seen = some ij := by
        have := (lookup_entry t ht e (by rw [hdir]; exact List.mem_cons_self ..)).2
        rw [h1, hj] at this
        exact this.symm
      simp [image, hdir, hseen, hd, h1]

/-- The first file of each commit missing or of another size is none when every commit's file is
there and of its size. -/
theorem fileFault_of (img : Image) : ∀ cs : List Commit,
    (∀ c ∈ cs, ∃ f, img.lookup (finalName c.seq) = some f ∧ f.length = c.fileSize) →
      fileFault? img cs = none
  | [], _ => rfl
  | c :: cs, h => by
    obtain ⟨f, hf, hl⟩ := h c (List.mem_cons_self ..)
    simp only [fileFault?, hf, hl, ↓reduceIte]
    exact fileFault_of img cs fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- With no append made where the records end, nothing can be left whole there: any record
allowed. -/
theorem steady_vacant (k : Bytes) (rs : List Record) (P Q : Record → Prop) (d : Data)
    (h : Steady k rs P d) (hw : Fresh k rs d) : Steady k rs Q d :=
  ⟨h.key, h.records, h.kept, h.high, h.written, fun w _ hm _ _ _ =>
    absurd (hw _ w hm) (Nat.lt_irrefl _)⟩

/-- **A crash of the journal once its format is kept**, seen record by record: the records kept,
with what `P` allows still able to come back where they end; or those and one more allowed, after
which nothing can. -/
theorem crash_found_back (k : Bytes) (rs : List Record) (P : Record → Prop) (d : Data)
    (h : Steady k rs P d) (c : Bytes) (hc : d.Leaves c) (hu : Unforged k d c) :
    Found k rs P (d.after c) ∨
      ∃ r, P r ∧ r.ok = true ∧ r.key = none ∧ Found k (rs ++ [r]) (fun _ => False) (d.after c) := by
  obtain ⟨rs', t, hct, hrs, hscan⟩ := steady_crash k rs P d h c hc hu
  rcases hrs with rfl | ⟨r, hP, hr, hkey, rfl⟩
  · exact Or.inl ⟨rfl, rfl, ⟨t, hct, hscan⟩, (steady_cut k rs' P d h c hc rs' t hct (Or.inl rfl)).1⟩
  · refine Or.inr ⟨r, hP, hr, hkey, rfl, rfl, ⟨t, hct, hscan⟩, ?_⟩
    have hcut := (steady_cut k rs P d h c hc (rs ++ [r]) t hct (Or.inr ⟨r, hr, hkey, rfl⟩)).1
    refine steady_vacant k _ P _ _ hcut fun o w hm => ?_
    have hle := (h.written o w (by simpa [Data.truncate, Data.after] using hm)).1
    have := encode_length r k (journal k rs).length
    rw [journal_append, List.length_append]
    omega

/-- What recovery finds after a crash of the spool: every article answered, and only commits the
store appended, each with the file the store wrote for it. -/
def Recovers (v : View) (img : Image) (st : Store) : Prop :=
  (∀ c ∈ v.answered, c ∈ st.articles) ∧
    ∀ c ∈ st.articles, c ∈ v.appended ∧ img.lookup (finalName c.seq) = some (v.files c.seq) ∧
      (crc32c (v.files c.seq)).toNat = c.fileCrc

/-- Recovery's next sequence number is at most one above the highest a record or a name carries. -/
theorem recoverRecords_next (cfg : Config) (img : Image) (names : List Name) (content key : Bytes)
    (cs : List Commit) (cut : Option Nat) (st : Store) (ops : List Action)
    (h : recoverRecords cfg img names content key cs cut = .ok (st, ops)) :
    st.next ≤ nextSeq cs names + 1 := by
  revert h
  unfold recoverRecords
  split
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · dsimp only
    intro h
    cases hcut : cut.isSome
    · simp only [hcut, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        dsimp only
        omega
    · simp only [hcut, ↓reduceIte] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        dsimp only
        omega

theorem commitsOf_append (a b : List Record) : commitsOf (a ++ b) = commitsOf a ++ commitsOf b := by
  simp [commitsOf]

theorem found_mono (k : Bytes) (rs : List Record) (P Q : Record → Prop) (d : Data)
    (h : Found k rs P d) (hpq : ∀ r, P r → Q r) : Found k rs Q d :=
  ⟨h.kept, h.high, h.reads, ⟨h.cut.key, h.cut.records, h.cut.kept, h.cut.high, h.cut.written,
    fun w r hm hr hp hf => hpq r (h.cut.back w r hm hr hp hf)⟩⟩

/-- The names a crash leaves are of a shape recovery reads, numbered below `next`. -/
theorem crash_spool_names (cfg : Config) (s t : Fs) (v : View) (h : Spool cfg s v)
    (hc : Crash s t) :
    ∀ e ∈ t.dir, ∃ n, parseName e.name = some n ∧ ∀ q, seqOf n = some q → q < v.next := by
  intro e he
  obtain ⟨e₀, he₀, hn⟩ := crash_names s t hc e he
  rw [← hn]
  exact h.names e₀ he₀

theorem crash_spool_parse (cfg : Config) (s t : Fs) (v : View) (h : Spool cfg s v)
    (hc : Crash s t) : ∀ p ∈ image t, (parseName p.1).isSome := by
  intro p hp
  obtain ⟨e, he, hn⟩ := image_names t p hp
  obtain ⟨n, hpn, _⟩ := crash_spool_names cfg s t v h hc e he
  rw [← hn, hpn]
  rfl

/-- The journal's name settled after a crash that left it a file. -/
theorem crash_journal_settled (s t : Fs) (hc : Crash s t) (ij : Ino)
    (hj : t.lookup journalName = some ij) :
    ∃ e, t.entry journalName = some e ∧ e.Settled ∧ e.synced = some ij ∧
      ∀ b, e.Leaves b → b = none ∨ b = some ij := by
  obtain ⟨e, he, hs'⟩ : ∃ e, t.entry journalName = some e ∧ e.seen = some ij := by
    simp only [Fs.lookup, Option.bind_eq_some_iff] at hj
    exact hj
  have hset := crash_entry s t hc _ e he
  have hsyn : e.synced = some ij := by simpa [Entry.seen, hset.1] using hs'
  refine ⟨e, he, hset, hsyn, fun b hb => Or.inr ?_⟩
  rcases hb with hb | hb
  · rw [hb, hsyn]
  · rw [hset.1] at hb; cases hb

/-- **A crash of the spool once the journal's format is kept**: given what the journal's file reads
as, recovery finds the articles answered and only commits appended, with their files, and the spool
it leaves is one again. -/
theorem crash_spool_found (cfg : Config) (hkey : cfg.key.length = keyLength) (s t : Fs) (v : View)
    (h : Spool cfg s v) (hc : Crash s t) (k : Bytes) (rs back rs' back' : List Record)
    (hph : v.phase.kept = rs ∧ v.phase.back = back)
    (hsub : ∀ c ∈ commitsOf (rs' ++ back'), c ∈ commitsOf (rs ++ back))
    (hkept : ∀ c ∈ commitsOf rs, c ∈ commitsOf rs')
    (hrules : Rules cfg (commitsOf rs') ∧ ∀ r ∈ back', Rules cfg (commitsOf (rs' ++ [r])))
    (ij : Ino) (d' : Data) (hj : t.lookup journalName = some ij) (hd : t.data ij = some d')
    (hf : Found k rs' (· ∈ back') d') (hap : Apart s ij) :
    ∃ st ops, recover cfg (image t) = .ok (st, ops) ∧ Recovers v (image t) st ∧
      Spool cfg t { v with phase := .found k rs' back' } ∧ st.articles = commitsOf rs' ∧
      st.key = k ∧ st.next ≤ v.next + 1 := by
  obtain ⟨hk, hb⟩ := hph
  have ht := crash_ok s t h.ok hc
  have hall := crash_spool_parse cfg s t v h hc
  have hnames := crash_spool_names cfg s t v h hc
  have hplaced : ∀ c ∈ commitsOf (rs' ++ back'),
      Placed t v.files c ∧ (image t).lookup (finalName c.seq) = some (v.files c.seq) := by
    intro c hcm
    have := hsub c hcm
    rw [← hk, ← hb] at this
    exact crash_placed s t h.ok hc v.files c (h.placed c this)
  obtain ⟨tl, hseen, hscan⟩ := hf.reads
  have hlook : (image t).lookup journalName = some d'.seen := by
    rw [image_lookup t ht, hj, Option.bind_some, hd, Option.map_some]
  have hnc : ∀ x w, (if tl.isEmpty then End.clean else End.torn (journal k rs').length) ≠
      .corrupt x w := by
    intro x w; split <;> simp
  rw [recover_of cfg hkey (image t) d'.seen k rs' _ hall hlook hscan hnc]
  have hfile : fileFault? (image t) (commitsOf rs') = none := by
    refine fileFault_of _ _ fun c hcm => ⟨v.files c.seq, ?_, ?_⟩
    · exact (hplaced c (by rw [commitsOf_append]; exact List.mem_append_left _ hcm)).2
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, hlen, _⟩ :=
        (hplaced c (by rw [commitsOf_append]; exact List.mem_append_left _ hcm)).1
      exact hlen
  have hseqs : ∀ c ∈ commitsOf rs', c.seq < v.next := by
    intro c hcm
    have := hsub c (by rw [commitsOf_append]; exact List.mem_append_left _ hcm)
    rw [← hk, ← hb] at this
    exact h.seqs c this
  have hle : nextSeq (commitsOf rs') ((image t).filterMap (parseName ·.1)) ≤ v.next := by
    have := nextSeq_le (commitsOf rs') ((image t).filterMap (parseName ·.1)) (v.next - 1)
      (fun c hcm => by have := hseqs c hcm; omega) (fun n hn q hq => by
        obtain ⟨p, hp, hpn⟩ := List.mem_filterMap.mp hn
        obtain ⟨e, he, hen⟩ := image_names t p hp
        obtain ⟨n', hn', hlt⟩ := hnames e he
        rw [hen, hpn] at hn'
        cases hn'
        have := hlt q hq
        omega)
    have := h.room.1
    omega
  obtain ⟨st, ops, hrec, harts, hkey'⟩ := recoverRecords_of cfg (image t)
    ((image t).filterMap (parseName ·.1)) d'.seen k (commitsOf rs') _ hrules.1.1 hrules.1.2.1
    hrules.1.2.2 hfile (by have := h.room.2; split <;> omega)
  refine ⟨st, ops, hrec, ⟨fun c hcm => ?_, fun c hcm => ?_⟩, ?_, harts, hkey',
    Nat.le_trans (recoverRecords_next _ _ _ _ _ _ _ _ _ hrec) (Nat.add_le_add_right hle 1)⟩
  · have := h.answered c hcm
    rw [hk] at this
    rw [harts]
    exact hkept c this
  · rw [harts] at hcm
    have hmem := hsub c (by rw [commitsOf_append]; exact List.mem_append_left _ hcm)
    rw [← hk, ← hb] at hmem
    have hpl := hplaced c (by rw [commitsOf_append]; exact List.mem_append_left _ hcm)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcrc⟩ := hpl.1
    exact ⟨h.appended c hmem, hpl.2, hcrc⟩
  · obtain ⟨e, he, hset, hsyn, hleaves⟩ := crash_journal_settled s t hc ij hj
    have hnu : ¬ Unsettled t := fun hu => hu e he hset
    refine ⟨ht, hnames, h.room, (fun hne => by cases hne),
      fun _ => ⟨e, ij, d', he, hj, hleaves, hd, hf, crash_apart s t h.ok hc ij hap⟩,
      fun hor => ?_, fun hu => absurd hu hnu, fun c hcm => (hplaced c hcm).1, hrules,
      fun c hcm => ?_, fun c hcm => ?_, fun c hcm => ?_⟩
    · rcases hor with hor | hor | hor
      · cases hor
      · cases hor
      · exact absurd hor hnu
    · have := hsub c hcm
      rw [← hk, ← hb] at this
      exact h.seqs c this
    · have := h.answered c hcm
      rw [hk] at this
      exact hkept c this
    · have := hsub c hcm
      rw [← hk, ← hb] at this
      exact h.appended c this

theorem rules_nil (cfg : Config) : Rules cfg (commitsOf []) := ⟨rfl, rfl, rfl⟩

/-- **A crash of the spool that leaves the journal with no format**, alone: recovery makes it again,
with no article, and the spool it leaves is one again. -/
theorem crash_spool_unformatted (cfg : Config) (hkey : cfg.key.length = keyLength) (s t : Fs)
    (v : View) (h : Spool cfg s v) (hc : Crash s t) (ha : Alone s) (hans : v.answered = [])
    (ij : Ino) (d' : Data) (hj : t.lookup journalName = some ij) (hd : t.data ij = some d')
    (hu : Unformatted d') :
    ∃ st ops, recover cfg (image t) = .ok (st, ops) ∧ Recovers v (image t) st ∧
      Spool cfg t { v with phase := .unformatted } ∧ st.articles = [] ∧ st.next ≤ v.next + 1 := by
  have ht := crash_ok s t h.ok hc
  have himg := crash_image_alone s t h.ok hc ha ij d' hj hd
  have hrec : recover cfg (image t) = .ok (fresh cfg, [.create cfg.key]) := by
    rw [himg]
    refine recover_unformatted cfg hkey d'.seen (by rw [hu.reads]) fun x w => ?_
    rw [hu.reads]
    split <;> simp
  refine ⟨fresh cfg, _, hrec, ⟨by simp [hans], by simp [fresh]⟩, ?_, rfl,
    by simp only [fresh]; omega⟩
  obtain ⟨e, he, hset, _, hleaves⟩ := crash_journal_settled s t hc ij hj
  have hnu : ¬ Unsettled t := fun hu => hu e he hset
  have hat := crash_alone s t h.ok hc ha
  refine ⟨ht, crash_spool_names cfg s t v h hc, h.room, (fun hne => by cases hne),
    fun _ => ⟨e, ij, d', he, hj, hleaves, hd, hu, fun e' he' hn' => hat e' he' hn' ij⟩,
    fun _ => hat,
    fun hu => absurd hu hnu, fun c hcm => by simp [Phase.kept, Phase.back, commitsOf] at hcm,
    ⟨rules_nil cfg, fun r hr => by simp [Phase.back] at hr⟩,
    fun c hcm => by simp [Phase.kept, Phase.back, commitsOf] at hcm,
    fun c hcm => by simp [hans] at hcm,
    fun c hcm => by simp [Phase.kept, Phase.back, commitsOf] at hcm⟩

/-- The commits of the records kept and one more allowed are among those of the records kept and
all allowed. -/
theorem commits_snoc (rs back : List Record) (r : Record) (hr : r ∈ back) :
    ∀ c ∈ commitsOf (rs ++ [r] ++ []), c ∈ commitsOf (rs ++ back) := by
  intro c hc
  simp only [List.append_nil, commitsOf_append, List.mem_append] at hc ⊢
  rcases hc with hc | hc
  · exact Or.inl hc
  · refine Or.inr ?_
    simp only [commitsOf, List.mem_filterMap] at hc ⊢
    obtain ⟨q, hq, hqc⟩ := hc
    simp only [List.mem_singleton] at hq
    exact ⟨q, hq ▸ hr, hqc⟩

/-- **A crash of the spool**, under what is assumed of the journal: recovery does not find the store
corrupt; it finds every article answered 240, and only commits whose records the store appended,
each with the file the store wrote for it; and what the crash left is a spool again, with the
journal gone with every other file, left with no format, or read as its records. -/
theorem spool_crash (cfg : Config) (hkey : cfg.key.length = keyLength) (s : Fs) (v : View)
    (h : Spool cfg s v) (t : Fs) (hc : Crash s t) (ha : Assumed v s t) :
    ∃ st ops ph, recover cfg (image t) = .ok (st, ops) ∧ Recovers v (image t) st ∧
      Spool cfg t { v with phase := ph } ∧ st.articles = commitsOf ph.kept ∧
      st.next ≤ v.next + 1 ∧
      (∀ c ∈ commitsOf (ph.kept ++ ph.back), c ∈ commitsOf (v.phase.kept ++ v.phase.back)) ∧
      (ph = .none ∨ ph = .unformatted ∨ ∃ k rs back, ph = .found k rs back ∧ st.key = k) := by
  have ht := crash_ok s t h.ok hc
  have hnil : ∀ ph : Phase, ph = .none ∨ ph = .unformatted →
      ∀ c ∈ commitsOf (ph.kept ++ ph.back), c ∈ commitsOf (v.phase.kept ++ v.phase.back) := by
    intro ph hph c hcm
    rcases hph with rfl | rfl <;> simp [Phase.kept, Phase.back, commitsOf] at hcm
  by_cases hj : t.lookup journalName = none
  · have hU : Unsettled s := by
      intro e he hset
      have hc' := crash_lookup s t h.ok hc journalName
      unfold Fs.Leaves at hc'
      rw [he, hj] at hc'
      rcases hc' with hc' | hc'
      · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hset.2
        rw [hi] at hc'; cases hc'
      · rw [hset.1] at hc'; cases hc'
    have hA := h.alone (Or.inr (Or.inr hU))
    have hq := h.quiet hU
    have hdir := crash_empty s t h.ok hc hA hj
    refine ⟨fresh cfg, _, .none, by rw [image_nil t hdir]; exact recover_empty cfg hkey,
      ⟨by simp [hq], by simp [fresh]⟩, ?_, rfl, by simp only [fresh]; omega,
      hnil _ (Or.inl rfl), Or.inl rfl⟩
    refine ⟨ht, by simp [hdir], h.room, fun _ e he => by simp [hdir] at he,
      fun hne => absurd rfl hne, fun _ e he => by simp [hdir] at he, fun _ => hq,
      fun c hcm => by simp [Phase.kept, Phase.back, commitsOf] at hcm,
      ⟨rules_nil cfg, fun r hr => by simp [Phase.back] at hr⟩,
      fun c hcm => by simp [Phase.kept, Phase.back, commitsOf] at hcm,
      fun c hcm => by simp [hq] at hcm,
      fun c hcm => by simp [Phase.kept, Phase.back, commitsOf] at hcm⟩
  · obtain ⟨ij, hij⟩ := Option.ne_none_iff_exists'.mp hj
    have hne : v.phase ≠ .none := fun hn => by
      obtain ⟨e, he, hl⟩ := crash_held s t h.ok hc journalName ij hij
      exact h.empty hn e (List.mem_of_find?_eq_some he) ij hl
    obtain ⟨e, ij', d, he, _, hb, hd, hholds, hap⟩ := h.journal hne
    rcases crash_journal s t h.ok hc e ij' d he hb hd with hl | ⟨hl, cj, hcl, hdt⟩
    · exact absurd hl hj
    rw [hij] at hl
    cases hl
    have hA := ha ij d (d.after cj) hij hd hdt
    simp only [Data.after] at hA
    cases hp : v.phase with
    | none => exact absurd hp hne
    | creating =>
      rw [hp] at hholds hA
      have hans : v.answered = [] := by
        cases hv : v.answered with
        | nil => rfl
        | cons c cs =>
          have := h.answered c (by rw [hv]; exact List.mem_cons_self ..)
          rw [hp] at this
          simp [Phase.kept, commitsOf] at this
      rcases crash_unformatted d hholds.1 cj hcl hA with hu | ⟨k, hk, rfl, hf⟩
      · obtain ⟨st, ops, hrec, hrv, hsp, harts, hnx⟩ := crash_spool_unformatted cfg hkey s t v h
          hc (h.alone (Or.inl hp)) hans ij _ hij hdt hu
        exact ⟨st, ops, .unformatted, hrec, hrv, hsp, harts, hnx,
          fun c hcm => by simp [Phase.kept, Phase.back, commitsOf] at hcm,
          Or.inr (Or.inl rfl)⟩
      · obtain ⟨st, ops, hrec, hrv, hsp, harts, hkey', hnx⟩ := crash_spool_found cfg hkey s t v h
          hc k [] [] [] [] (by rw [hp]; exact ⟨rfl, rfl⟩) (fun c hcm => hcm) (fun c hcm => hcm)
          ⟨rules_nil cfg, fun r hr => by simp at hr⟩ ij _ hij hdt
          (found_mono k [] _ _ _ hf fun _ h => h.elim) hap
        exact ⟨st, ops, .found k [] [], hrec, hrv, hsp, harts, hnx,
          fun c hcm => by simp [Phase.kept, Phase.back, commitsOf] at hcm,
          Or.inr (Or.inr ⟨k, [], [], rfl, hkey'⟩)⟩
    | unformatted =>
      rw [hp] at hholds
      have hans : v.answered = [] := by
        cases hv : v.answered with
        | nil => rfl
        | cons c cs =>
          have := h.answered c (by rw [hv]; exact List.mem_cons_self ..)
          rw [hp] at this
          simp [Phase.kept, commitsOf] at this
      obtain ⟨rfl, hu⟩ := unformatted_crash d hholds cj hcl
      obtain ⟨st, ops, hrec, hrv, hsp, harts, hnx⟩ := crash_spool_unformatted cfg hkey s t v h hc
        (h.alone (Or.inr (Or.inl hp))) hans ij _ hij hdt hu
      exact ⟨st, ops, .unformatted, hrec, hrv, hsp, harts, hnx,
        fun c hcm => by simp [Phase.kept, Phase.back, commitsOf] at hcm,
        Or.inr (Or.inl rfl)⟩
    | steady k rs back =>
      rw [hp] at hholds hA
      have hrules := h.rules
      rw [hp] at hrules
      rcases crash_found_back k rs _ d hholds cj hcl hA with hf | ⟨r, hr, _, _, hf⟩
      · obtain ⟨st, ops, hrec, hrv, hsp, harts, hkey', hnx⟩ := crash_spool_found cfg hkey s t v h
          hc k rs back rs back (by rw [hp]; exact ⟨rfl, rfl⟩) (fun c hcm => hcm)
          (fun c hcm => hcm) hrules ij _ hij hdt hf hap
        exact ⟨st, ops, .found k rs back, hrec, hrv, hsp, harts, hnx,
          fun c hcm => hcm, Or.inr (Or.inr ⟨k, rs, back, rfl, hkey'⟩)⟩
      · have hsub := commits_snoc rs back r hr
        obtain ⟨st, ops, hrec, hrv, hsp, harts, hkey', hnx⟩ := crash_spool_found cfg hkey s t v h
          hc k rs back (rs ++ [r]) [] (by rw [hp]; exact ⟨rfl, rfl⟩) hsub
          (fun c hcm => by rw [commitsOf_append]; exact List.mem_append_left _ hcm)
          ⟨hrules.2 r hr, fun r' hr' => by simp at hr'⟩ ij _ hij hdt
          (found_mono k _ _ _ _ hf fun _ h => h.elim) hap
        exact ⟨st, ops, .found k (rs ++ [r]) [], hrec, hrv, hsp, harts, hnx,
          fun c hcm => hsub c hcm, Or.inr (Or.inr ⟨k, rs ++ [r], [], rfl, hkey'⟩)⟩
    | found k rs back =>
      rw [hp] at hholds
      have hrules := h.rules
      rw [hp] at hrules
      obtain ⟨rfl, hf⟩ := found_crash k rs _ d hholds cj hcl
      obtain ⟨st, ops, hrec, hrv, hsp, harts, hkey', hnx⟩ := crash_spool_found cfg hkey s t v h hc
        k rs back rs back (by rw [hp]; exact ⟨rfl, rfl⟩) (fun c hcm => hcm) (fun c hcm => hcm)
        hrules ij _ hij hdt hf hap
      exact ⟨st, ops, .found k rs back, hrec, hrv, hsp, harts, hnx,
        fun c hcm => hcm, Or.inr (Or.inr ⟨k, rs, back, rfl, hkey'⟩)⟩

/-- A spool stays one with a higher bound on its numbers, while numbers last. -/
theorem spool_next (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (n : Nat)
    (hn : v.next ≤ n) (hroom : n + 1 < 2 ^ 64) : Spool cfg s { v with next := n } :=
  ⟨h.ok, fun e he => by
    obtain ⟨m, hm, hlt⟩ := h.names e he
    exact ⟨m, hm, fun q hq => by have := hlt q hq; show q < n; omega⟩,
    ⟨by have := h.room.1; show 1 ≤ n; omega, hroom⟩, h.empty, h.journal, h.alone, h.quiet, h.placed,
    h.rules, fun c hc => by have := h.seqs c hc; show c.seq < n; omega, h.answered, h.appended⟩

/-! ## A restart -/

/-- The syncs a start makes before it reads: the journal's file, if a name holds it, then the
directory. -/
def startSyncs (s : Fs) : Fs :=
  ((match s.lookup journalName with
    | some i => (s.step (.sync i)).1
    | none => s).step .syncDir).1

theorem image_startSyncs (s : Fs) : image (startSyncs s) = image s := by
  unfold startSyncs
  rw [image_syncDir]
  split
  · exact image_onData s _ Data.sync seen_sync
  · rfl

theorem startSyncs_ok (s : Fs) (hs : s.Ok) : (startSyncs s).Ok := by
  unfold startSyncs
  split <;> exact FsModel.step_ok _ (by first | exact FsModel.step_ok s hs _ | exact hs) _

theorem startSyncs_dir (s : Fs) (ht : s.dirTrusted = true) :
    (startSyncs s).dir = s.dir.filterMap Entry.settle := by
  unfold startSyncs
  split <;> simp [Fs.step, Fs.onData, ht] <;> split <;> simp

theorem startSyncs_data (s : Fs) (i : Ino) :
    (startSyncs s).data i =
      if s.lookup journalName = some i then (s.data i).map Data.sync else s.data i := by
  have hsd : ∀ u : Fs, (u.step .syncDir).1.data i = u.data i := by
    intro u; simp only [Fs.step]; split <;> rfl
  unfold startSyncs
  rw [hsd]
  split
  · rename_i j hj
    rw [hj]
    simp only [Fs.step, Fs.onData]
    by_cases hij : i = j
    · subst hij
      split
      · simp [Fs.data, lookup_change]
      · rename_i hnone
        simp only [Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at hnone
        simp [hnone]
    · have hne : (some j = some i) = False := by simp [Ne.symm hij]
      split <;> simp [Fs.data, lookup_change, hij, hne]
  · rename_i hl
    simp [hl]

theorem entry_of_dir (s u : Fs) (h : u.dir = s.dir) : u.entry = s.entry := by
  funext n; simp [Fs.entry, h]

theorem lookup_of_dir (s u : Fs) (h : u.dir = s.dir) : u.lookup = s.lookup := by
  funext n; simp [Fs.lookup, entry_of_dir s u h]

/-- A spool is one again with the same names, the same journal's file, and the files of its commits
in place. -/
theorem spool_transfer (cfg : Config) (t u : Fs) (v : View) (h : Spool cfg t v) (hu : u.Ok)
    (hdir : u.dir = t.dir) (hj : ∀ i, t.lookup journalName = some i → u.data i = t.data i)
    (hp : ∀ c ∈ commitsOf (v.phase.kept ++ v.phase.back), Placed u v.files c) : Spool cfg u v := by
  have hent := entry_of_dir t u hdir
  have hlk := lookup_of_dir t u hdir
  have hU : Unsettled u ↔ Unsettled t := by simp only [Unsettled, hent]
  have hA : Alone u ↔ Alone t := by simp only [Alone, hdir]
  refine ⟨hu, by rw [hdir]; exact h.names, h.room, by rw [hdir]; exact h.empty, fun hne => ?_,
    fun hor => ?_, fun hun => h.quiet (hU.mp hun), hp, h.rules, h.seqs, h.answered,
    h.appended⟩
  · obtain ⟨e, ij, d, he, hl, hb, hd, hholds, hap⟩ := h.journal hne
    refine ⟨e, ij, d, by rw [hent]; exact he, by rw [hlk]; exact hl, hb, by rw [hj ij hl]; exact hd,
      hholds, by unfold Apart; rw [hdir]; exact hap⟩
  · refine hA.mpr (h.alone ?_)
    rcases hor with hor | hor | hor
    · exact Or.inl hor
    · exact Or.inr (Or.inl hor)
    · exact Or.inr (Or.inr (hU.mp hor))

/-- What a crash that loses nothing leaves of a file a name holds: the octets the program saw. -/
theorem data_current (s : Fs) (i : Ino) (n : Bytes)
    (h : (s.crashWith s.current).lookup n = some i) :
    (s.crashWith s.current).data i = (s.data i).map fun d => d.after d.seen := by
  obtain ⟨e, he, hs⟩ : ∃ e, (s.crashWith s.current).entry n = some e ∧ e.seen = some i := by
    simp only [Fs.lookup, Option.bind_eq_some_iff] at h
    exact h
  have hm := List.mem_of_find?_eq_some he
  have hh : (Fs.mk (FsModel.crashDir s.dir (s.dir.map Entry.seen))
      (FsModel.crashFiles s.files (s.files.map fun p => p.2.seen)) s.next true).holds i = true := by
    simp only [Fs.holds, List.any_eq_true]
    refine ⟨e, ?_, ?_⟩
    · simpa [Fs.crashWith, Fs.prune, Fs.current] using hm
    · simp only [Entry.holds, decide_eq_true_eq]
      rw [← hs]
      exact FsModel.entry_leaves_seen e
  simp only [Fs.data, Fs.crashWith, Fs.prune, Fs.current, FsModel.lookup_filter, hh, ↓reduceIte,
    lookup_crashFiles_current]

theorem finalName_ne (q : Nat) : finalName q ≠ journalName := by
  intro h
  have := congrArg List.length h
  simp [finalName, journalName, hex16, hexOf_length, ascii] at this

/-- A commit's file in place stays in place through the syncs a start makes. -/
theorem placed_startSyncs (s : Fs) (hs : s.Ok) (ht : s.dirTrusted = true) (ij : Ino)
    (hj : s.lookup journalName = some ij) (hap : Apart s ij) (files : Nat → Bytes) (c : Commit)
    (hp : Placed s files c) : Placed (startSyncs s) files c := by
  obtain ⟨e, i, d, he, hset, hsyn, hd, hk, hh, hseen, hlen, hcrc⟩ := hp
  have hname : e.name = finalName c.seq := by
    have := List.find?_some he
    simpa using this
  have hmem : e ∈ (startSyncs s).dir := by
    rw [startSyncs_dir s ht]
    refine List.mem_filterMap.mpr ⟨e, List.mem_of_find?_eq_some he, ?_⟩
    obtain ⟨name, synced, held⟩ := e
    simp only at hset hsyn
    obtain ⟨rfl, _⟩ := hset
    subst hsyn
    rfl
  have hent := (lookup_entry _ (startSyncs_ok s hs) e hmem).1
  rw [hname] at hent
  have hne : s.lookup journalName ≠ some i := by
    rw [hj]
    intro hji
    cases hji
    exact hap e (List.mem_of_find?_eq_some he) (by rw [hname]; exact finalName_ne _)
      (Or.inl hsyn.symm)
  refine ⟨e, i, d, hent, hset, hsyn, ?_, hk, hh, hseen, hlen, hcrc⟩
  rw [startSyncs_data, if_neg hne, hd]

/-- What a restart assumes of the journal: once its format is kept, what `Unforged` assumes of the
octets the program sees in it, which it wrote. -/
def RestartAssumed (v : View) (s : Fs) : Prop :=
  ∀ i d, s.lookup journalName = some i → s.data i = some d →
    match v.phase with
    | .steady k _ _ => Unforged k d d.seen
    | _ => True

/-- **A restart of a spool**, its syncs trusted: once the start has synced the journal and the
directory, recovery reads it as a crash that lost nothing — no corruption, every article answered,
only commits appended, each with its file — and the spool it syncs is one again. Only what is
assumed past the journal's format is assumed, of octets the program wrote. -/
theorem spool_restart (cfg : Config) (hkey : cfg.key.length = keyLength) (s : Fs) (v : View)
    (h : Spool cfg s v) (htd : s.dirTrusted = true)
    (htj : ∀ i d, s.lookup journalName = some i → s.data i = some d → d.trusted = true)
    (ha : RestartAssumed v s) :
    ∃ st ops ph, recover cfg (image (startSyncs s)) = .ok (st, ops) ∧
      Recovers v (image (startSyncs s)) st ∧ Spool cfg (startSyncs s) { v with phase := ph } ∧
      st.articles = commitsOf ph.kept ∧ st.next ≤ v.next + 1 ∧
      (∀ c ∈ commitsOf (ph.kept ++ ph.back), c ∈ commitsOf (v.phase.kept ++ v.phase.back)) ∧
      (ph = .none ∨ ph = .unformatted ∨ ∃ k rs back, ph = .found k rs back ∧ st.key = k) := by
  let t := s.crashWith s.current
  have hc : Crash s t := FsModel.crash_nothing_lost s h.ok
  have himg : image (startSyncs s) = image t := by rw [image_startSyncs, image_current]
  have hdir : (startSyncs s).dir = t.dir := by
    rw [startSyncs_dir s htd]
    simp [t, Fs.crashWith, Fs.prune, Fs.current, crashDir_current]
  -- the journal's file is the one the name holds before and after
  have hjt : ∀ i, t.lookup journalName = some i → s.lookup journalName = some i := by
    intro i hi
    obtain ⟨e, he, hl⟩ := crash_held s t h.ok hc journalName i hi
    have hsl := (lookup_entry s h.ok e (List.mem_of_find?_eq_some he)).2
    have hname : e.name = journalName := by
      have := List.find?_some he
      simpa using this
    rw [hname] at hsl
    rw [hsl]
    by_cases hp : v.phase = .none
    · exact absurd hl (h.empty hp e (List.mem_of_find?_eq_some he) i)
    · obtain ⟨e', ij, d, he', hl', hb, _, _, _⟩ := h.journal hp
      rw [he] at he'
      cases he'
      rcases hb _ hl with hb | hb
      · cases hb
      · rw [hsl] at hl'; rw [hl', hb]
  have hA : Assumed v s t := by
    intro i d d' hi hd hd'
    have hsl₀ := hjt i hi
    have hd'' : d' = d.after d.seen := by
      rw [data_current s i journalName hi, hd] at hd'
      exact (Option.some.inj hd').symm
    subst hd''
    have hp : v.phase ≠ .none := fun hn => by
      obtain ⟨e, he, hl⟩ := crash_held s t h.ok hc journalName i hi
      exact h.empty hn e (List.mem_of_find?_eq_some he) i hl
    obtain ⟨e', ij, d₀, _, hl', _, hd₀, hholds, _⟩ := h.journal hp
    rw [hsl₀] at hl'
    cases hl'
    rw [hd] at hd₀
    cases hd₀
    have hra := ha i d hsl₀ hd
    cases hph : v.phase with
    | creating =>
      rw [hph] at hholds
      simp only [Data.after]
      rcases hholds.2 with hs0 | hw
      · rw [hs0]; exact formatWritten_nil d
      · exact fun _ => ⟨d.seen, hw, List.take_prefix _ _⟩
    | steady k rs back =>
      rw [hph] at hra
      simpa [Data.after] using hra
    | none => trivial
    | unformatted => trivial
    | found _ _ _ => trivial
  obtain ⟨st, ops, ph, hrec, hrv, hsp, harts, hnx, hsub, hkind⟩ :=
    spool_crash cfg hkey s v h t hc hA
  refine ⟨st, ops, ph, by rw [himg]; exact hrec, by rw [himg]; exact hrv, ?_, harts, hnx, hsub,
    hkind⟩
  refine spool_transfer cfg t _ _ hsp (startSyncs_ok s h.ok) hdir (fun i hi => ?_) fun c hcm => ?_
  · have hsl₀ := hjt i hi
    obtain ⟨d, hd⟩ := data_some s h.ok _ i hsl₀
    rw [startSyncs_data, if_pos hsl₀, hd, data_current s i journalName hi, hd]
    simp only [Option.map_some]
    rw [sync_after d (htj i d hsl₀ hd)]
  · have hp : v.phase ≠ .none := by
      intro hn
      have hkb : v.phase.kept = [] ∧ v.phase.back = [] := by rw [hn]; exact ⟨rfl, rfl⟩
      have hm := hsub c hcm
      rw [hkb.1, hkb.2] at hm
      simp [commitsOf] at hm
    obtain ⟨_, ij, _, _, hl, _, _, _, hap⟩ := h.journal hp
    exact placed_startSyncs s h.ok htd ij hl hap _ c (h.placed c (hsub c hcm))

/-! ## The premises can hold -/

/-- An article's file. -/
def body : Bytes := ascii "Subject: x\r\n\r\nx\r\n"

/-- The commit of the article in `body`, numbered `seq`. -/
def articleOf (seq : Nat) : Commit :=
  ⟨seq, ascii "<x@y>" ++ [BitVec.ofNat 8 seq], [⟨ascii "local.test", seq⟩], 14, body.length,
    (crc32c body).toNat⟩

def sampleConfig : Config := ⟨[ascii "local.test"], sampleKey⟩

theorem articleOf_ok (seq : Nat) (h1 : 1 ≤ seq) (h2 : seq < 2 ^ 31) :
    (Record.commit (articleOf seq)).ok = true := by
  have hb : body.length = 17 := by decide
  have hm : (ascii "<x@y>").length = 5 := by decide
  have hg : (ascii "local.test").length = 10 := by decide
  have hc := UInt32.toNat_lt (crc32c body)
  simp only [Record.ok, Commit.ok, articleOf, hb, List.length_append, hm,
    List.length_cons, List.length_nil, List.all_cons, List.all_nil, hg, List.map_cons,
    List.map_nil, Bool.and_eq_true, decide_eq_true_eq]
  have hn : [ascii "local.test"].Nodup := List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩,
    ⟨⟨⟨by omega, by omega⟩, h1⟩, h2⟩, trivial⟩, hn⟩, by omega⟩, by omega⟩, hc⟩

/-- A crash may leave fewer octets past those a file kept than a frame takes, and none of them
starts a frame. -/
theorem unforged_near (k : Bytes) (d : Data) (c : Bytes)
    (h : c.length < d.kept.length + headerLength + 1) : Unforged k d c := by
  intro o ho ht
  have := tagged_whole _ _ _ ht
  simp only [List.length_drop] at this
  omega

/-- The records of the examples' journal: a run's start and the commit of article 1. -/
def wRecords : List Record := [.start, .commit (articleOf 1)]

/-- The examples' journal with those records, all synced. -/
def jSynced : Data :=
  ((((Data.empty.append (journal sampleKey [])).sync.append
    (Record.start.encode sampleKey (journal sampleKey []).length)).sync).append
    ((Record.commit (articleOf 1)).encode sampleKey (journal sampleKey [.start]).length)).sync

/-- The commit of article 2, framed where the examples' records end. -/
def wCommit : Bytes :=
  (Record.commit (articleOf 2)).encode sampleKey (journal sampleKey wRecords).length

theorem jSynced_steady : Steady sampleKey wRecords (fun _ => False) jSynced ∧
    Fresh sampleKey wRecords jSynced ∧ jSynced.seen = journal sampleKey wRecords ∧
    jSynced.high = (journal sampleKey wRecords).length ∧ jSynced.trusted = true := by
  have hk := sampleKey_length
  have hf := format_journal sampleKey
  let d0 := Data.empty.append (journal sampleKey [])
  have hc0 : Creating d0 := by
    have := creating_append Data.empty creating_empty rfl sampleKey hk
      ((Record.format sampleKey).encode sampleKey 0).length
    rwa [List.take_length, ← hf] at this
  obtain ⟨h1, hfr1⟩ := creating_sync d0 hc0 rfl sampleKey hk (by simp [d0, Data.append, Data.empty])
  let x := (journal sampleKey []).length
  have h2 := steady_append sampleKey [] _ d0.sync h1 (by simp [seen_sync, d0, Data.append,
    Data.empty]) (by rw [high_sync _ rfl]; simp [d0, Data.append, Data.empty]) .start rfl rfl
    (Or.inl hfr1) (Record.start.encode sampleKey x).length
  rw [List.take_length] at h2
  have hj : journal sampleKey [.start] = journal sampleKey [] ++ Record.start.encode sampleKey x :=
    journal_append sampleKey [] Record.start
  obtain ⟨h3, hfr3⟩ := steady_sync sampleKey [] _ _ h2 rfl .start rfl rfl
    (by simp [d0, x, Data.append, Data.sync, Data.empty])
  rw [List.nil_append] at h3 hfr3
  let y := (journal sampleKey [.start]).length
  have h4 := steady_append sampleKey [.start] _ _ h3
    (by rw [seen_sync, hj]; simp [d0, x, Data.append, Data.sync, Data.empty])
    (by rw [high_sync _ rfl, hj]; simp [d0, x, Data.append, Data.sync, Data.empty])
    (.commit (articleOf 1)) (articleOf_ok 1 (by decide) (by decide)) rfl (Or.inl hfr3)
    ((Record.commit (articleOf 1)).encode sampleKey y).length
  rw [List.take_length] at h4
  have hj2 : journal sampleKey wRecords =
      journal sampleKey [.start] ++ (Record.commit (articleOf 1)).encode sampleKey y :=
    journal_append sampleKey [.start] (.commit (articleOf 1))
  have hseen : (((d0.sync.append (Record.start.encode sampleKey x)).sync).append
      ((Record.commit (articleOf 1)).encode sampleKey y)).seen = journal sampleKey wRecords := by
    rw [hj2, hj]; simp [d0, x, Data.append, Data.sync, Data.empty]
  obtain ⟨h5, hfr5⟩ := steady_sync sampleKey [.start] _ _ h4 rfl (.commit (articleOf 1))
    (articleOf_ok 1 (by decide) (by decide)) rfl (by rw [← hj2]; exact hseen)
  refine ⟨h5, hfr5, ?_, ?_, ?_⟩
  · simp only [jSynced, seen_sync]; exact hseen
  · simp only [jSynced]; rw [high_sync _ rfl, hseen]
  · simp [jSynced, Data.sync, Data.append, Data.empty]

theorem jSynced_ok : jSynced.Ok := by
  unfold jSynced
  exact FsModel.sync_ok _ (FsModel.append_ok _ (FsModel.sync_ok _ (FsModel.append_ok _
    (FsModel.sync_ok _ (FsModel.append_ok _ FsModel.empty_ok _)) _)) _)

/-- The examples' journal with the commit of article 2 appended after the records and not
synced. -/
def wJournal : Data := jSynced.append wCommit

/-- The file of an article, synced. -/
def wFile : Data := (Data.empty.append body).sync

/-- A spool of that journal and the files of articles 1 and 2, every name synced. -/
def wSpool : Fs :=
  ⟨[⟨journalName, some 0, []⟩, ⟨finalName 1, some 1, []⟩, ⟨finalName 2, some 2, []⟩],
    [(0, wJournal), (1, wFile), (2, wFile)], 3, true⟩

/-- What the store knows of it: article 1 answered, article 2 appended and not answered. -/
def wView : View := ⟨.steady sampleKey wRecords [.commit (articleOf 2)], [articleOf 1],
  [articleOf 1, articleOf 2], fun _ => body, 3⟩

theorem wJournal_steady : Steady sampleKey wRecords (· ∈ [.commit (articleOf 2)]) wJournal := by
  obtain ⟨hs, hfr, hseen, hhigh, _⟩ := jSynced_steady
  have h := steady_append sampleKey wRecords _ _ hs hseen hhigh (.commit (articleOf 2))
    (articleOf_ok 2 (by decide) (by decide)) rfl (Or.inl hfr)
    ((Record.commit (articleOf 2)).encode sampleKey (journal sampleKey wRecords).length).length
  rw [List.take_length] at h
  exact ⟨h.key, h.records, h.kept, h.high, h.written,
    fun w r hm hr hp hfit => by simp [h.back w r hm hr hp hfit]⟩

theorem wFile_eq : wFile = ⟨body, body, body.length, [(0, body)], true⟩ := by
  simp [wFile, Data.sync, Data.append, Data.empty]

theorem wRules (q : Nat) (hq : q = 1 ∨ q = 2) :
    Rules sampleConfig
      (commitsOf (wRecords ++ (if q = 1 then [] else [.commit (articleOf 2)]))) := by
  rcases hq with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

/-- The premise `Spool` can hold: of a journal with a run's start, the commit of an article answered
and synced, and the commit of another appended after it and not synced, with both articles' files
in place. -/
theorem spool_witness : Spool sampleConfig wSpool wView := by
  have hent : wSpool.entry journalName = some ⟨journalName, some 0, []⟩ := by decide
  have hlk : wSpool.lookup journalName = some 0 := by decide
  have hset : ¬ Unsettled wSpool := fun hu => hu _ hent ⟨rfl, rfl⟩
  have hok : wSpool.Ok := by
    refine ⟨by decide, by decide, by decide, fun q hq => ?_, fun e he i hi => ?_⟩
    · simp only [wSpool, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact FsModel.append_ok _ jSynced_ok _
      · exact FsModel.sync_ok _ (FsModel.append_ok _ FsModel.empty_ok _)
      · exact FsModel.sync_ok _ (FsModel.append_ok _ FsModel.empty_ok _)
    · simp only [wSpool, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> simp [Entry.Leaves] at hi <;> simp [wSpool, hi]
  have hplaced : ∀ q, q = 1 ∨ q = 2 → Placed wSpool (fun _ => body) (articleOf q) := by
    intro q hq
    have hfin : wSpool.entry (finalName q) = some ⟨finalName q, some q, []⟩ := by
      rcases hq with rfl | rfl <;> decide
    refine ⟨_, q, wFile, hfin, ⟨rfl, rfl⟩, rfl, by rcases hq with rfl | rfl <;> rfl,
      by rw [wFile_eq], by rw [wFile_eq], by rw [wFile_eq], by simp only [articleOf],
      by simp only [articleOf]⟩
  have hmem : ∀ c, c ∈ commitsOf (wView.phase.kept ++ wView.phase.back) →
      c = articleOf 1 ∨ c = articleOf 2 := by
    intro c hc
    simp [wView, wRecords, Phase.kept, Phase.back, commitsOf] at hc
    rcases hc with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨hok, fun e he => ?_, ⟨by decide, by decide⟩, (fun h => by cases h),
    fun _ => ⟨_, 0, wJournal, hent, hlk, fun b hb => ?_, rfl, wJournal_steady, ?_⟩, fun h => ?_,
    fun hu => absurd hu hset, fun c hc => ?_,
    ⟨wRules 1 (Or.inl rfl), fun r hr => ?_⟩, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · simp only [wSpool, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨.journal, parseName_bytes .journal rfl, fun q hq => by simp [seqOf] at hq⟩
    · exact ⟨.final 1, parseName_bytes (.final 1) (by decide), fun q hq => by
        simp only [seqOf, Option.some.injEq] at hq; subst hq; decide⟩
    · exact ⟨.final 2, parseName_bytes (.final 2) (by decide), fun q hq => by
        simp only [seqOf, Option.some.injEq] at hq; subst hq; decide⟩
  · rcases hb with rfl | hb
    · exact Or.inr rfl
    · simp at hb
  · intro e he hn hl
    simp only [wSpool, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact hn rfl
    · simp [Entry.Leaves] at hl
    · simp [Entry.Leaves] at hl
  · rcases h with h | h | h
    · cases h
    · cases h
    · exact absurd h hset
  · rcases hmem c hc with rfl | rfl
    · exact hplaced 1 (Or.inl rfl)
    · exact hplaced 2 (Or.inr rfl)
  · simp only [wView, Phase.back, List.mem_singleton] at hr
    subst hr
    exact wRules 2 (Or.inr rfl)
  · rcases hmem c hc with rfl | rfl <;> decide
  · simp only [wView, List.mem_singleton] at hc
    subst hc
    simp [wView, wRecords, Phase.kept, commitsOf]
  · rcases hmem c hc with rfl | rfl <;> simp [wView]

/-- The premise `Apart` can hold: of the journal's file in that spool. -/
theorem apart_witness : Apart wSpool 0 := by
  intro e he hn hl
  simp only [wSpool, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact hn rfl
  · simp [Entry.Leaves] at hl
  · simp [Entry.Leaves] at hl

/-- The premise `Placed` can hold: of article 1's file. -/
theorem placed_witness : Placed wSpool (fun _ => body) (articleOf 1) :=
  spool_witness.placed _ (by simp [wView, wRecords, Phase.kept, Phase.back, commitsOf])

/-- What a crash of that spool may leave of the journal: three octets of the commit not synced. -/
def wLeft : Bytes := jSynced.seen ++ wCommit.take 3

/-- A crash of that spool that leaves them. -/
def wCrash : Fs := wSpool.crashWith ⟨[some 0, some 1, some 2], [wLeft, body, body]⟩

theorem wCrash_crash : Crash wSpool wCrash := by
  obtain ⟨_, _, hseen, hhigh, _⟩ := jSynced_steady
  have he := encode_length (.commit (articleOf 2)) sampleKey (journal sampleKey wRecords).length
  have hk := (jSynced_steady.1).kept
  refine ⟨_, ⟨?_, ?_⟩, rfl⟩
  · simp only [wSpool, FsModel.Each]
    exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, trivial⟩
  · simp only [wSpool, FsModel.Each]
    have hf : wFile.Leaves body := by rw [wFile_eq]; exact ⟨List.prefix_refl _, Nat.le_refl _⟩
    refine ⟨⟨?_, ?_⟩, hf, hf, trivial⟩
    · simp only [wJournal, wLeft, Data.append]
      rw [hk, hseen]
      exact List.prefix_append _ _
    · simp only [wJournal, wLeft, wCommit, Data.append, List.length_append, List.length_take]
      omega

/-- The premise `Assumed` can hold: of that crash. -/
theorem assumed_witness : Assumed wView wSpool wCrash := by
  intro i d d' hl hd hd'
  have hl0 : wCrash.lookup journalName = some 0 := by decide
  rw [hl0] at hl
  cases hl
  have hd0 : wSpool.data 0 = some wJournal := rfl
  rw [hd0] at hd
  cases hd
  have hd'0 : wCrash.data 0 = some (wJournal.after wLeft) := rfl
  rw [hd'0] at hd'
  cases hd'
  refine unforged_near _ _ _ ?_
  obtain ⟨hs, _, hseen, _, _⟩ := jSynced_steady
  simp only [Data.after, wLeft, wJournal, Data.append, List.length_append, List.length_take,
    headerLength, hs.kept, hseen]
  omega

/-- A spool whose journal's append of the commit of article 2 failed after three octets. -/
def wFailed : Fs :=
  ⟨[⟨journalName, some 0, []⟩], [(0, jSynced.append (wCommit.take 3))], 1, true⟩

/-- The premise `RestartAssumed` can hold: of that spool, restarted. -/
theorem restartAssumed_witness : RestartAssumed wView wFailed := by
  intro i d hl hd
  have hl0 : wFailed.lookup journalName = some 0 := by decide
  rw [hl0] at hl
  cases hl
  have hd0 : wFailed.data 0 = some (jSynced.append (wCommit.take 3)) := rfl
  rw [hd0] at hd
  cases hd
  refine unforged_near _ _ _ ?_
  obtain ⟨hs, _, hseen, _, _⟩ := jSynced_steady
  simp only [Data.append, List.length_append, List.length_take, headerLength, hs.kept, hseen]
  omega

/-- A journal being created, its name not synced, with a temporary name made and removed. -/
def wCreating : Fs :=
  ⟨[⟨journalName, none, [some 0]⟩, ⟨tempName 1, none, [none]⟩], [(0, Data.empty)], 1, true⟩

/-- The premise `Unsettled` can hold: of that directory. -/
theorem unsettled_witness : Unsettled wCreating := by
  intro e he hset
  have : wCreating.entry journalName = some ⟨journalName, none, [some 0]⟩ := by decide
  rw [this] at he
  cases he
  exact absurd hset.1 (by simp)

/-- The premise `Alone` can hold: of that directory. -/
theorem alone_witness : Alone wCreating := by
  intro e he hn i hl
  simp only [wCreating, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact hn rfl
  · simp [Entry.Leaves] at hl

/-! ## Examples -/

/-- A journal created and synced, its name synced, and a run's start appended and synced. -/
def started : List FsModel.Op :=
  [.create journalName, .append 0 (journal sampleKey []), .sync 0, .syncDir,
    .append 0 (Record.start.encode sampleKey (journal sampleKey []).length), .sync 0]

/-- A POST of `body` numbered `seq` into file `i`, up to its commit appended where the journal of
`rs` ends. -/
def posted (seq : Nat) (i : Ino) (rs : List Record) : List FsModel.Op :=
  [.create (tempName seq), .append i body, .sync i, .rename (tempName seq) (finalName seq),
    .syncDir,
    .append 0 ((Record.commit (articleOf seq)).encode sampleKey (journal sampleKey rs).length)]

/-- What recovery finds of each crash `cuts` lists of `s`: the articles; or none if it fails, or if
an article's file is not `body`. -/
def recoveries (s : Fs) : List (Option (List Commit)) :=
  ((s.crashes Data.cuts).map fun t =>
    match recover sampleConfig (image t) with
    | .ok (st, _) =>
      if st.articles.all (fun c => (image t).lookup (finalName c.seq) == some body) then
        some st.articles
      else none
    | .error _ => none).eraseDups

/-- The states a run passes through, from the empty file system. -/
def points (ops : List FsModel.Op) : List Fs :=
  (List.range (ops.length + 1)).map fun n => Fs.empty.run (ops.take n)

/-- Whether every crash at every point of a run recovers, each article's file whole. -/
def everyPoint (ops : List FsModel.Op) : Bool :=
  (points ops).all fun s => (recoveries s).all (·.isSome)

/-- What recovery refuses for, at some crash `cuts` lists of `s`. -/
def faults (s : Fs) : List Fault :=
  ((s.crashes Data.cuts).filterMap fun t =>
    match recover sampleConfig (image t) with
    | .error f => some f
    | .ok _ => none).eraseDups

/-- A POST of `body` numbered 1 in a run's first commit, in the order the store keeps. -/
def postOne : List FsModel.Op := started ++ posted 1 1 [.start] ++ [.sync 0]

/-- A commit appended and not synced, then synced: every crash at every point recovers, the commit's
file whole; before the sync, with the commit or without it, and after it, with it always. -/
def regression_915 : Bool :=
  let s := Fs.empty.run (started ++ posted 1 1 [.start])
  let r := recoveries s
  everyPoint postOne && r.contains (some []) && r.contains (some [articleOf 1]) &&
    recoveries (s.run [.sync 0]) == [some [articleOf 1]]

/-- A second POST in flight, its file written but not renamed, after the first answered: every crash
at every point recovers, and once the first is answered, with the first article always. -/
def regression_916 : Bool :=
  let ops := postOne ++ [.create (tempName 2), .append 2 body]
  everyPoint ops && recoveries (Fs.empty.run ops) == [some [articleOf 1]]

/-- The journal created, its format synced and its name: every crash at every point recovers, with
no article. -/
def regression_917 : Bool :=
  let ops : List FsModel.Op := [.create journalName, .append 0 (journal sampleKey []), .sync 0,
    .syncDir]
  everyPoint ops && (points ops).all fun s => recoveries s == [some []]

/-- Why the order matters: once a commit is appended and synced before its file's rename, before the
directory is synced after it, or before the file is synced, a crash may lose the file or part of it;
and a file made before the journal's name is synced may be left with no journal. -/
def regression_918 : Bool :=
  let commit := FsModel.Op.append 0 ((Record.commit (articleOf 1)).encode sampleKey
    (journal sampleKey [.start]).length)
  let beforeRename := started ++ [.create (tempName 1), .append 1 body, .sync 1, commit, .sync 0]
  let beforeDirSync := started ++ [.create (tempName 1), .append 1 body, .sync 1,
    .rename (tempName 1) (finalName 1), commit, .sync 0]
  let beforeFileSync := started ++ [.create (tempName 1), .append 1 body,
    .rename (tempName 1) (finalName 1), .syncDir, commit, .sync 0]
  let beforeJournal : List FsModel.Op := [.create journalName, .append 0 (journal sampleKey []),
    .sync 0, .create (tempName 1)]
  (faults (Fs.empty.run beforeRename)).contains (.missingFile 1) &&
    (faults (Fs.empty.run beforeDirSync)).contains (.missingFile 1) &&
    (faults (Fs.empty.run beforeFileSync)).contains (.wrongSize 1) &&
    (faults (Fs.empty.run beforeJournal)).contains .noJournal

end DN.News.Spool
