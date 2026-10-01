-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.FrameSpec

/-!
# DN.News.FsModel

The file system the store runs on, as docs/decisions/0005-article-store.md ("What is proved")
models it: one directory whose names each hold a file, the files' data, the operations the host
carries out on them, what an operation that fails may have done, and what a crash may leave, in
the vocabulary of Pillai et al. (OSDI 2014) and Bornholt et al. (ASPLOS 2016).

Until a sync, what the program sees and what a crash keeps differ. A crash leaves each name,
independently, holding the file it held at the directory's last sync or any file it has held since
— nothing among them if it held nothing — and each file, independently, with the octets no
operation has touched since its last sync, then any octets at all, up to the most it has held
since; a file no name is left holding is freed. So synced data, and a name its directory has
synced, survive; anything else may survive whole, in part, as junk or not at all — more than file
systems are known to allow, so what holds after every crash here holds after theirs. An operation
that fails may have done any part of what it was asked: an append, any first part of its octets;
anything else, all of it or nothing; and once a sync of a file or of the directory has failed, no
later sync of it is trusted until power is lost, as Linux may have marked as clean what it could
not write, so that a process started again before then reads what was never written.

Proven: a crash may lose nothing (`crash_nothing_lost`); a sync, while trusted, is a barrier, after
which a crash leaves the file as it is (`leaves_sync`), and so is a sync of the directory for names
(`settle_leaves`); after a sync, a crash leaves an append as the octets before it and any after
them, no more than were appended (`leaves_append`), and a cut likewise (`leaves_truncate`); a crash
leaves each name and each file as their own rules say (`crash_lookup`, `crash_data`); with its names
and the files they hold settled, a crash only frees the files no name holds (`crash_prune`), and a
crash of what a crash left changes nothing (`crash_twice`); what the program finds under a name
after each operation (`lookup_create`, `lookup_rename`, `rename_same`, `lookup_remove`); no
operation but a sync of the directory, failing or not, takes away what a crash may leave a name
holding (`step_widens`, `fails_widens`); operations, failures and crashes keep the file system well
formed (`step_ok`, `fails_ok`, `crash_ok`); and the crashes `choices` lists are crashes
(`choices_allowed`).
-/

namespace DN.News.FsModel

open DN.News.FrameSpec (Byte)

abbrev Bytes := List Byte

/-- A file, by the number the file system gives it; names hold files. -/
abbrev Ino := Nat

/-! ## Files -/

/-- A file's data. -/
structure Data where
  /-- the octets the program reads -/
  seen : Bytes
  /-- the octets no operation has touched since the file's last sync -/
  kept : Bytes
  /-- the most octets the file has held since that sync -/
  high : Nat
  /-- every append ever made to the file, at the offset where it was made -/
  written : List (Nat × Bytes)
  /-- whether a sync still makes the file durable: not once one has failed, until power is lost -/
  trusted : Bool
  deriving DecidableEq

def Data.empty : Data := ⟨[], [], 0, [], true⟩

/-- Octets written at the end of the file. -/
def Data.append (d : Data) (bs : Bytes) : Data :=
  { d with seen := d.seen ++ bs, high := max d.high (d.seen.length + bs.length),
           written := d.written ++ [(d.seen.length, bs)] }

/-- The file cut to `n` octets, or extended to them with zeros. -/
def Data.truncate (d : Data) (n : Nat) : Data :=
  { d with seen := d.seen.take n ++ List.replicate (n - d.seen.length) 0, kept := d.kept.take n,
           high := max d.high n }

/-- `fsync` or `fdatasync`: both make the octets and the size durable, while syncs are trusted. -/
def Data.sync (d : Data) : Data :=
  if d.trusted then { d with kept := d.seen, high := d.seen.length } else d

/-- A sync that failed: it made nothing durable for certain, and no later one is trusted. -/
def Data.untrust (d : Data) : Data := { d with trusted := false }

/-- **What a crash may leave the file holding**: the octets kept, then any, up to the most it has
held since its last sync. -/
def Data.Leaves (d : Data) (c : Bytes) : Prop := d.kept <+: c ∧ c.length ≤ d.high

/-- `Leaves`, computed. -/
def Data.leaves (d : Data) (c : Bytes) : Bool := d.kept.isPrefixOf c && c.length ≤ d.high

/-- The file a crash left holding `c`, all of it now as good as synced. -/
def Data.after (d : Data) (c : Bytes) : Data := ⟨c, c, c.length, d.written, true⟩

/-- Whether the data is as operations leave it: what was kept is still there, and the file holds
no more than the most it has held. -/
def Data.Ok (d : Data) : Prop := d.kept <+: d.seen ∧ d.seen.length ≤ d.high

/-- Whether nothing has happened to the file since its last sync, and a sync is trusted. -/
def Data.Settled (d : Data) : Prop := d.kept = d.seen ∧ d.high = d.seen.length ∧ d.trusted = true

theorem leaves_iff (d : Data) (c : Bytes) : d.leaves c = true ↔ d.Leaves c := by
  simp [Data.leaves, Data.Leaves, List.isPrefixOf_iff_prefix]

theorem empty_ok : Data.empty.Ok := ⟨List.prefix_refl _, Nat.le_refl _⟩

theorem append_ok (d : Data) (h : d.Ok) (bs : Bytes) : (d.append bs).Ok := by
  obtain ⟨hp, hl⟩ := h
  refine ⟨hp.trans (List.prefix_append _ _), ?_⟩
  simp only [Data.append, List.length_append]
  omega

theorem prefix_take {xs ys : Bytes} (h : xs <+: ys) (n : Nat) : xs.take n <+: ys.take n := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append]
  exact List.prefix_append _ _

theorem truncate_ok (d : Data) (h : d.Ok) (n : Nat) : (d.truncate n).Ok := by
  obtain ⟨hp, _⟩ := h
  refine ⟨(prefix_take hp n).trans (List.prefix_append _ _), ?_⟩
  simp only [Data.truncate, List.length_append, List.length_take, List.length_replicate]
  omega

theorem sync_ok (d : Data) (h : d.Ok) : d.sync.Ok := by
  unfold Data.sync
  split
  · exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  · exact h

theorem untrust_ok (d : Data) (h : d.Ok) : d.untrust.Ok := h

theorem after_settled (d : Data) (c : Bytes) : (d.after c).Settled := ⟨rfl, rfl, rfl⟩

theorem settled_ok (d : Data) (h : d.Settled) : d.Ok := by
  obtain ⟨hk, hh, _⟩ := h
  exact ⟨hk ▸ List.prefix_refl _, Nat.le_of_eq hh.symm⟩

/-- A crash may leave the file as the program sees it. -/
theorem leaves_seen (d : Data) (h : d.Ok) : d.Leaves d.seen := h

theorem leaves_exact (d : Data) (hk : d.kept = d.seen) (hh : d.high = d.seen.length) (c : Bytes) :
    d.Leaves c ↔ c = d.seen := by
  constructor
  · rintro ⟨hp, hl⟩
    rw [hk] at hp
    have := hp.length_le
    exact (hp.eq_of_length (by omega)).symm
  · rintro rfl
    exact ⟨hk ▸ List.prefix_refl _, Nat.le_of_eq hh.symm⟩

/-- **A settled file is left as it is**: no other octets are possible. -/
theorem settled_leaves (d : Data) (h : d.Settled) (c : Bytes) : d.Leaves c ↔ c = d.seen :=
  leaves_exact d h.1 h.2.1 c

/-- **A sync is a barrier**, while trusted: after it, a crash leaves the file as the program sees
it. -/
theorem leaves_sync (d : Data) (h : d.trusted = true) (c : Bytes) :
    d.sync.Leaves c ↔ c = d.seen := by
  simp only [Data.sync, h, ↓reduceIte]
  exact leaves_exact _ rfl rfl c

/-- **An append after a sync** leaves, after a crash, the octets before it and any after them,
no more than were appended. -/
theorem leaves_append (d : Data) (h : d.Settled) (bs c : Bytes) :
    (d.append bs).Leaves c ↔ ∃ g, c = d.seen ++ g ∧ g.length ≤ bs.length := by
  obtain ⟨hk, hh, _⟩ := h
  simp only [Data.Leaves, Data.append, hk, hh]
  constructor
  · rintro ⟨⟨g, rfl⟩, hl⟩
    refine ⟨g, rfl, ?_⟩
    simp only [List.length_append] at hl
    omega
  · rintro ⟨g, rfl, hg⟩
    refine ⟨List.prefix_append _ _, ?_⟩
    simp only [List.length_append]
    omega

/-- **A cut after a sync** leaves, after a crash, the octets before the cut and any after them,
no more than the file held. -/
theorem leaves_truncate (d : Data) (h : d.Settled) (n : Nat) (hn : n ≤ d.seen.length)
    (c : Bytes) :
    (d.truncate n).Leaves c ↔ d.seen.take n <+: c ∧ c.length ≤ d.seen.length := by
  obtain ⟨hk, hh, _⟩ := h
  simp only [Data.Leaves, Data.truncate, hk, hh]
  rw [Nat.max_eq_left hn]

/-! ## Names -/

/-- A name in the directory. -/
structure Entry where
  name : Bytes
  /-- the file it held at the directory's last sync -/
  synced : Option Ino
  /-- every file it has held since, the latest first; `none` once removed -/
  held : List (Option Ino)
  deriving DecidableEq

/-- The file the program finds under the name. -/
def Entry.seen (e : Entry) : Option Ino := e.held.headD e.synced

/-- **What a crash may leave the name holding**: what it held at the directory's last sync, or
anything it has held since. -/
def Entry.Leaves (e : Entry) (b : Option Ino) : Prop := b = e.synced ∨ b ∈ e.held

/-- Whether nothing has happened to the name since the directory's last sync. -/
def Entry.Settled (e : Entry) : Prop := e.held = [] ∧ e.synced.isSome

/-- The name as a sync of the directory leaves it, if it holds a file. -/
def Entry.settle (e : Entry) : Option Entry := e.seen.map fun i => ⟨e.name, some i, []⟩

/-- Whether a crash may leave the name holding file `i`. -/
instance (e : Entry) (b : Option Ino) : Decidable (e.Leaves b) :=
  inferInstanceAs (Decidable (b = e.synced ∨ b ∈ e.held))

def Entry.holds (e : Entry) (i : Ino) : Bool := decide (e.Leaves (some i))

theorem holds_iff (e : Entry) (i : Ino) : e.holds i = true ↔ e.Leaves (some i) := by
  simp [Entry.holds]

/-- A crash may leave the name as the program sees it. -/
theorem entry_leaves_seen (e : Entry) : e.Leaves e.seen := by
  rcases e with ⟨name, synced, _ | ⟨b, bs⟩⟩
  · exact Or.inl rfl
  · exact Or.inr (List.mem_cons_self ..)

/-- **A sync of the directory is a barrier for names**: after it, a crash leaves each name as the
program sees it. -/
theorem settle_leaves (e e' : Entry) (h : e.settle = some e') (b : Option Ino) :
    e'.Leaves b ↔ b = e.seen := by
  simp only [Entry.settle, Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp [Entry.Leaves, hi]

/-! ## The file system -/

structure Fs where
  /-- the names -/
  dir : List Entry
  /-- each file's data -/
  files : List (Ino × Data)
  /-- the number the next file created gets -/
  next : Ino
  /-- whether a sync of the directory still makes its names durable: not once one has failed,
  until power is lost -/
  dirTrusted : Bool
  deriving DecidableEq

def Fs.empty : Fs := ⟨[], [], 0, true⟩

/-- The entry of a name. -/
def Fs.entry (s : Fs) (name : Bytes) : Option Entry := s.dir.find? (·.name == name)

/-- The file the program finds under a name. -/
def Fs.lookup (s : Fs) (name : Bytes) : Option Ino := (s.entry name).bind Entry.seen

/-- A file's data. -/
def Fs.data (s : Fs) (i : Ino) : Option Data := s.files.lookup i

/-- What a crash may leave a name holding, given its entry: what the entry allows, or nothing if it
has none. -/
def leavesOf : Option Entry → Option Ino → Prop
  | some e, b => e.Leaves b
  | none, b => b = none

/-- **What a crash may leave a name holding**. -/
def Fs.Leaves (s : Fs) (name : Bytes) (b : Option Ino) : Prop := leavesOf (s.entry name) b

/-- Whether a crash may leave some name holding file `i`. -/
def Fs.holds (s : Fs) (i : Ino) : Bool := s.dir.any (·.holds i)

/-- The directory with `name` now holding `b`. -/
def rebind (dir : List Entry) (name : Bytes) (b : Option Ino) : List Entry :=
  if dir.any (·.name == name) then
    dir.map fun e => if e.name == name then { e with held := b :: e.held } else e
  else dir ++ [⟨name, none, [b]⟩]

/-- The files with the data of `i` changed by `f`. -/
def change (files : List (Ino × Data)) (i : Ino) (f : Data → Data) : List (Ino × Data) :=
  files.map fun p => if p.1 == i then (p.1, f p.2) else p

/-- An operation the host carries out on the directory (0005, "File operations through the
host"). The store writes a file only at its end, so a write is an append. -/
inductive Op
  /-- a new, empty file under a name that holds none -/
  | create (name : Bytes)
  /-- the file a name holds -/
  | open_ (name : Bytes)
  /-- octets written at the end of a file -/
  | append (i : Ino) (bytes : Bytes)
  /-- a file cut, or extended with zeros, to a size -/
  | truncate (i : Ino) (size : Nat)
  /-- `fsync` or `fdatasync` of a file -/
  | sync (i : Ino)
  /-- `len` octets of a file from `offset` -/
  | read (i : Ino) (offset len : Nat)
  /-- a file's size -/
  | size (i : Ino)
  /-- the file one name holds moved to another, which loses any it held; nothing, as rename(2)
  says, if both already hold the same file -/
  | rename (src dst : Bytes)
  /-- a name removed -/
  | remove (name : Bytes)
  /-- `fsync` of the directory -/
  | syncDir
  /-- the names that hold a file -/
  | list
  deriving DecidableEq

/-- What an operation answers when it does not fail. -/
inductive Result
  | done
  | file (i : Ino)
  | bytes (bs : Bytes)
  | size (n : Nat)
  | names (ns : List Bytes)
  /-- the name holds a file already -/
  | exists_
  /-- no such name, or no such file -/
  | missing
  deriving DecidableEq

/-- An operation on a file's data. -/
def Fs.onData (s : Fs) (i : Ino) (f : Data → Data) : Fs × Result :=
  if (s.data i).isSome then ({ s with files := change s.files i f }, .done) else (s, .missing)

/-- **What an operation that succeeds does**, as the program sees it. -/
def Fs.step (s : Fs) : Op → Fs × Result
  | .create name =>
    if (s.lookup name).isSome then (s, .exists_)
    else (⟨rebind s.dir name (some s.next), s.files ++ [(s.next, .empty)], s.next + 1,
      s.dirTrusted⟩, .file s.next)
  | .open_ name =>
    match s.lookup name with
    | some i => (s, .file i)
    | none => (s, .missing)
  | .append i bs => s.onData i fun d => d.append bs
  | .truncate i n => s.onData i fun d => d.truncate n
  | .sync i => s.onData i Data.sync
  | .read i off len =>
    match s.data i with
    | some d => (s, .bytes ((d.seen.drop off).take len))
    | none => (s, .missing)
  | .size i =>
    match s.data i with
    | some d => (s, .size d.seen.length)
    | none => (s, .missing)
  | .rename src dst =>
    match s.lookup src with
    | some i =>
      if s.lookup dst == some i then (s, .done)
      else ({ s with dir := rebind (rebind s.dir dst (some i)) src none }, .done)
    | none => (s, .missing)
  | .remove name =>
    match s.lookup name with
    | some _ => ({ s with dir := rebind s.dir name none }, .done)
    | none => (s, .missing)
  | .syncDir =>
    if s.dirTrusted then ({ s with dir := s.dir.filterMap Entry.settle }, .done) else (s, .done)
  | .list => (s, .names ((s.dir.filter fun e => e.seen.isSome).map Entry.name))

/-- **What an operation that fails may have done**, as the program sees it afterwards: an append,
any first part of its octets; a sync of a file or of the directory, nothing for certain, and no
later sync of it is trusted; anything else, all it does or nothing. -/
def Fs.failures (s : Fs) : Op → List Fs
  | .append i bs => (List.range (bs.length + 1)).map fun k => (s.step (.append i (bs.take k))).1
  | .sync i => [(s.onData i Data.untrust).1]
  | .syncDir => [{ s with dirTrusted := false }]
  | op => [s, (s.step op).1]

/-- Whether `t` is what `op`, failing, may have left of `s`. -/
def Fs.Fails (s t : Fs) (op : Op) : Prop := t ∈ s.failures op

/-- The file system after operations that succeed, in order. -/
def Fs.run (s : Fs) : List Op → Fs
  | [] => s
  | op :: ops => (s.step op).1.run ops

/-- Whether the file system is as operations leave it: each name and each file once, files
numbered below the next, each file's data as operations leave it, and every file a crash may leave
a name holding still there. -/
def Fs.Ok (s : Fs) : Prop :=
  (s.dir.map Entry.name).Nodup ∧ (s.files.map Prod.fst).Nodup ∧
    (∀ p ∈ s.files, p.1 < s.next) ∧ (∀ p ∈ s.files, p.2.Ok) ∧
    ∀ e ∈ s.dir, ∀ i, e.Leaves (some i) → i ∈ s.files.map Prod.fst

/-- Whether nothing has happened since the last syncs, which are trusted, and every file has a
name. -/
def Fs.Settled (s : Fs) : Prop :=
  s.dirTrusted = true ∧ (∀ e ∈ s.dir, e.Settled) ∧ (∀ p ∈ s.files, p.2.Settled) ∧
    ∀ p ∈ s.files, s.holds p.1 = true

/-! ## What the program finds under a name -/

/-- The entry a name has once `name` holds `b`. -/
theorem entry_rebind (dir : List Entry) (name m : Bytes) (b : Option Ino) :
    (rebind dir name b).find? (·.name == m) =
      if m = name then
        some ((dir.find? (·.name == name)).elim ⟨name, none, [b]⟩
          fun e => { e with held := b :: e.held })
      else dir.find? (·.name == m) := by
  unfold rebind
  split
  · rename_i hany
    rw [List.find?_map]
    have hp : ((·.name == m) ∘ fun e : Entry =>
        if e.name == name then { e with held := b :: e.held } else e) = (·.name == m) := by
      funext e
      simp only [Function.comp]
      split <;> rfl
    rw [hp]
    split
    · rename_i hm
      subst hm
      obtain ⟨e, he⟩ : ∃ e, dir.find? (·.name == m) = some e := by
        cases h : dir.find? (·.name == m) with
        | none =>
          rw [List.find?_eq_none] at h
          simp only [List.any_eq_true] at hany
          obtain ⟨x, hx, hxn⟩ := hany
          exact absurd hxn (h x hx)
        | some e => exact ⟨e, rfl⟩
      have hen : e.name = m := by simpa using List.find?_some he
      simp [he, hen]
    · rename_i hm
      cases h : dir.find? (·.name == m) with
      | none => rfl
      | some e =>
        have hen : e.name = m := by simpa using List.find?_some h
        have : e.name ≠ name := by rw [hen]; exact hm
        simp [this]
  · rename_i hany
    rw [List.find?_append]
    have hnone : dir.find? (·.name == name) = none := by
      rw [List.find?_eq_none]
      intro x hx hxn
      exact hany (List.any_eq_true.mpr ⟨x, hx, hxn⟩)
    split
    · rename_i hm
      subst hm
      simp [hnone]
    · rename_i hm
      have : (name == m) = false := by
        simp only [beq_eq_false_iff_ne]
        exact fun h => hm h.symm
      simp [this]

/-- **What the program finds under a name after `name` holds `b`.** -/
theorem lookup_rebind (dir : List Entry) (name m : Bytes) (b : Option Ino) :
    ((rebind dir name b).find? (·.name == m)).bind Entry.seen =
      if m = name then b else (dir.find? (·.name == m)).bind Entry.seen := by
  rw [entry_rebind]
  split
  · cases dir.find? (·.name == name) <;> rfl
  · rfl

/-- **After a create**, the name holds the new file, and every other name what it held. -/
theorem lookup_create (s : Fs) (name m : Bytes) (h : s.lookup name = none) :
    (s.step (.create name)).1.lookup m = if m = name then some s.next else s.lookup m := by
  have hc : (s.lookup name).isSome = false := by rw [h]; rfl
  simp only [Fs.step, hc, Bool.false_eq_true, ↓reduceIte]
  simp only [Fs.lookup, Fs.entry]
  exact lookup_rebind _ _ _ _

/-- **After a rename**, the old name holds nothing, the new one the file the old one held, and every
other name what it held. -/
theorem lookup_rename (s : Fs) (src dst m : Bytes) (i : Ino) (h : s.lookup src = some i)
    (hd : s.lookup dst ≠ some i) :
    (s.step (.rename src dst)).1.lookup m =
      if m = src then none else if m = dst then some i else s.lookup m := by
  have hd' : (s.lookup dst == some i) = false := by simpa using hd
  simp only [Fs.step, h, hd', Bool.false_eq_true, ↓reduceIte]
  simp only [Fs.lookup, Fs.entry]
  rw [lookup_rebind, lookup_rebind]

/-- **A rename between names that hold the same file changes nothing**, as rename(2) says. -/
theorem rename_same (s : Fs) (src dst : Bytes) (i : Ino) (h : s.lookup src = some i)
    (hd : s.lookup dst = some i) : (s.step (.rename src dst)).1 = s := by
  simp [Fs.step, h, hd]

/-- **After a remove**, the name holds nothing, and every other name what it held. -/
theorem lookup_remove (s : Fs) (name m : Bytes) (h : (s.lookup name).isSome = true) :
    (s.step (.remove name)).1.lookup m = if m = name then none else s.lookup m := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  simp only [Fs.step, hi]
  simp only [Fs.lookup, Fs.entry]
  exact lookup_rebind _ _ _ _

/-- A name that comes to hold `b` may be left holding it, or anything it might before. -/
theorem leaves_rebind (dir : List Entry) (name m : Bytes) (b b' : Option Ino) :
    leavesOf ((rebind dir name b).find? (·.name == m)) b' ↔
      (m = name ∧ b' = b) ∨ leavesOf (dir.find? (·.name == m)) b' := by
  rw [entry_rebind]
  by_cases hm : m = name
  · subst hm
    simp only [↓reduceIte, true_and]
    cases dir.find? (·.name == m) with
    | none =>
      simp only [Option.elim, leavesOf, Entry.Leaves, List.mem_singleton]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    | some e =>
      simp only [Option.elim, leavesOf, Entry.Leaves, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  · simp [hm]

/-- What a crash may leave a name holding, once `name` holds `b`. -/
theorem fs_leaves_rebind (s : Fs) (name m : Bytes) (b b' : Option Ino) :
    ({ s with dir := rebind s.dir name b } : Fs).Leaves m b' ↔
      (m = name ∧ b' = b) ∨ s.Leaves m b' := by
  simp only [Fs.Leaves, Fs.entry]
  exact leaves_rebind _ _ _ _ _

theorem onData_dir (s : Fs) (i : Ino) (f : Data → Data) : (s.onData i f).1.dir = s.dir := by
  unfold Fs.onData
  split <;> rfl

theorem leaves_of_dir (s t : Fs) (h : t.dir = s.dir) (m : Bytes) (b : Option Ino) :
    t.Leaves m b ↔ s.Leaves m b := by
  simp only [Fs.Leaves, Fs.entry, h]

/-- **No operation but a sync of the directory takes away what a crash may leave a name
holding.** -/
theorem step_widens (s : Fs) (op : Op) (hop : op ≠ .syncDir) (m : Bytes) (b : Option Ino)
    (h : s.Leaves m b) : (s.step op).1.Leaves m b := by
  cases op with
  | create name =>
    simp only [Fs.step]
    split
    · exact h
    · exact (fs_leaves_rebind { s with files := s.files ++ [(s.next, .empty)], next := s.next + 1 }
        name m (some s.next) b).mpr (Or.inr ((leaves_of_dir s _ rfl m b).mpr h))
  | open_ _ => simp only [Fs.step]; split <;> exact h
  | append i bs => exact (leaves_of_dir s _ (onData_dir s i _) m b).mpr h
  | truncate i n => exact (leaves_of_dir s _ (onData_dir s i _) m b).mpr h
  | sync i => exact (leaves_of_dir s _ (onData_dir s i _) m b).mpr h
  | read _ _ _ => simp only [Fs.step]; split <;> exact h
  | size _ => simp only [Fs.step]; split <;> exact h
  | rename src dst =>
    simp only [Fs.step]
    split
    · rename_i i _
      split
      · exact h
      · have h1 := (fs_leaves_rebind s dst m (some i) b).mpr (Or.inr h)
        exact (fs_leaves_rebind { s with dir := rebind s.dir dst (some i) } src m none b).mpr
          (Or.inr h1)
    · exact h
  | remove name =>
    simp only [Fs.step]
    split
    · exact (fs_leaves_rebind s name m none b).mpr (Or.inr h)
    · exact h
  | syncDir => exact absurd rfl hop
  | list => exact h

/-- **No operation that fails takes away what a crash may leave a name holding** — a sync of the
directory that fails included. -/
theorem fails_widens (s t : Fs) (op : Op) (h : s.Fails t op) (m : Bytes) (b : Option Ino)
    (hb : s.Leaves m b) : t.Leaves m b := by
  cases op with
  | append i bs =>
    simp only [Fs.Fails, Fs.failures, List.mem_map] at h
    obtain ⟨k, _, rfl⟩ := h
    exact step_widens s _ (by intro h; cases h) m b hb
  | sync i =>
    simp only [Fs.Fails, Fs.failures, List.mem_singleton] at h
    subst h
    exact (leaves_of_dir s _ (onData_dir s i _) m b).mpr hb
  | syncDir =>
    simp only [Fs.Fails, Fs.failures, List.mem_singleton] at h
    subst h
    exact hb
  | create _ | open_ _ | truncate _ _ | read _ _ _ | size _ | rename _ _ | remove _ | list =>
    simp only [Fs.Fails, Fs.failures, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · rw [h]; exact hb
    · rw [h]; exact step_widens s _ (by intro h; cases h) m b hb

/-! ## Operations keep the file system well formed -/

theorem names_rebind (dir : List Entry) (name : Bytes) (b : Option Ino) :
    (rebind dir name b).map Entry.name =
      if dir.any (·.name == name) then dir.map Entry.name else dir.map Entry.name ++ [name] := by
  unfold rebind
  split
  · simp only [List.map_map]
    congr 1
    funext e
    simp only [Function.comp]
    split <;> rfl
  · simp

theorem rebind_nodup (dir : List Entry) (hn : (dir.map Entry.name).Nodup) (name : Bytes)
    (b : Option Ino) : ((rebind dir name b).map Entry.name).Nodup := by
  rw [names_rebind]
  split
  · exact hn
  · rename_i h
    simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at h
    rw [List.nodup_append]
    refine ⟨hn, by simp, ?_⟩
    intro a ha x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp only [List.mem_map] at ha
    obtain ⟨e, he, rfl⟩ := ha
    exact fun heq => h e he heq

/-- Every file a crash may leave a name holding, once `name` holds `b`, is one it might before, or
`b`'s. -/
theorem rebind_holds (dir : List Entry) (name : Bytes) (b : Option Ino) (keys : List Ino)
    (h : ∀ e ∈ dir, ∀ i, e.Leaves (some i) → i ∈ keys) (hb : ∀ i, b = some i → i ∈ keys) :
    ∀ e ∈ rebind dir name b, ∀ i, e.Leaves (some i) → i ∈ keys := by
  intro e he i hi
  unfold rebind at he
  split at he
  · simp only [List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    split at hi
    · simp only [Entry.Leaves, List.mem_cons] at hi
      rcases hi with hi | hi | hi
      · exact h x hx i (Or.inl hi)
      · exact hb i hi.symm
      · exact h x hx i (Or.inr hi)
    · exact h x hx i hi
  · simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact h e he i hi
    · simp only [Entry.Leaves, List.mem_singleton] at hi
      rcases hi with hi | hi
      · simp at hi
      · exact hb i hi.symm

theorem names_settle :
    ∀ dir : List Entry,
      List.Sublist ((dir.filterMap Entry.settle).map Entry.name) (dir.map Entry.name)
  | [] => by simp
  | e :: dir => by
    simp only [List.filterMap_cons, List.map_cons]
    cases h : e.settle with
    | none => exact (names_settle dir).cons _
    | some e' =>
      simp only [Entry.settle, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      exact (names_settle dir).cons_cons _

theorem settle_holds (dir : List Entry) (keys : List Ino)
    (h : ∀ e ∈ dir, ∀ i, e.Leaves (some i) → i ∈ keys) :
    ∀ e ∈ dir.filterMap Entry.settle, ∀ i, e.Leaves (some i) → i ∈ keys := by
  intro e he i hi
  simp only [List.mem_filterMap] at he
  obtain ⟨x, hx, hs⟩ := he
  have := (settle_leaves x e hs (some i)).mp hi
  exact h x hx i (this ▸ entry_leaves_seen x)

theorem keys_change (files : List (Ino × Data)) (i : Ino) (f : Data → Data) :
    (change files i f).map Prod.fst = files.map Prod.fst := by
  simp only [change, List.map_map]
  congr 1
  funext p
  simp only [Function.comp]
  split <;> rfl

theorem mem_change (files : List (Ino × Data)) (i : Ino) (f : Data → Data) (q : Ino × Data)
    (hq : q ∈ change files i f) : ∃ p ∈ files, q = p ∨ q = (p.1, f p.2) := by
  simp only [change, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact ⟨p, hp, by split <;> simp⟩

theorem onData_ok (s : Fs) (hs : s.Ok) (i : Ino) (f : Data → Data)
    (hf : ∀ d, d.Ok → (f d).Ok) : (s.onData i f).1.Ok := by
  unfold Fs.onData
  split
  · obtain ⟨hn, hk, hlt, hd, hh⟩ := hs
    refine ⟨hn, by rw [keys_change]; exact hk, ?_, ?_, by rw [keys_change]; exact hh⟩
    · intro q hq
      obtain ⟨p, hp, h1 | h1⟩ := mem_change _ _ _ q hq
      · rw [h1]; exact hlt p hp
      · rw [h1]; exact hlt p hp
    · intro q hq
      obtain ⟨p, hp, h1 | h1⟩ := mem_change _ _ _ q hq
      · rw [h1]; exact hd p hp
      · rw [h1]; exact hf _ (hd p hp)
  · exact hs

theorem lookup_held (s : Fs) (hs : s.Ok) (name : Bytes) (i : Ino) (h : s.lookup name = some i) :
    i ∈ s.files.map Prod.fst := by
  simp only [Fs.lookup, Fs.entry, Option.bind_eq_some_iff] at h
  obtain ⟨e, he, hi⟩ := h
  exact hs.2.2.2.2 e (List.mem_of_find?_eq_some he) i (hi ▸ entry_leaves_seen e)

theorem dir_ok (s : Fs) (hs : s.Ok) (dir : List Entry) (hn : (dir.map Entry.name).Nodup)
    (hh : ∀ e ∈ dir, ∀ i, e.Leaves (some i) → i ∈ s.files.map Prod.fst) :
    ({ s with dir := dir } : Fs).Ok :=
  ⟨hn, hs.2.1, hs.2.2.1, hs.2.2.2.1, hh⟩

/-- **Every operation that succeeds keeps the file system well formed.** -/
theorem step_ok (s : Fs) (hs : s.Ok) (op : Op) : (s.step op).1.Ok := by
  cases op with
  | create name =>
    simp only [Fs.step]
    split
    · exact hs
    · obtain ⟨hn, hk, hlt, hd, hh⟩ := hs
      refine ⟨rebind_nodup _ hn _ _, ?_, ?_, ?_, ?_⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hk, by simp, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        simp only [List.mem_map] at ha
        obtain ⟨p, hp, rfl⟩ := ha
        exact Nat.ne_of_lt (hlt p hp)
      · intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact Nat.lt_succ_of_lt (hlt p hp)
        · exact Nat.lt_succ_self _
      · intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hd p hp
        · exact empty_ok
      · refine rebind_holds _ _ _ _ (fun e he i hi => ?_) (fun i hi => ?_)
        · simp only [List.map_append, List.mem_append]
          exact Or.inl (hh e he i hi)
        · simp only [Option.some.injEq] at hi
          simp [hi]
  | open_ name => simp only [Fs.step]; split <;> exact hs
  | append i bs => exact onData_ok s hs i _ fun d hd => append_ok d hd bs
  | truncate i n => exact onData_ok s hs i _ fun d hd => truncate_ok d hd n
  | sync i => exact onData_ok s hs i _ fun d hd => sync_ok d hd
  | read i off len => simp only [Fs.step]; split <;> exact hs
  | size i => simp only [Fs.step]; split <;> exact hs
  | rename src dst =>
    simp only [Fs.step]
    split
    · rename_i i hi
      split
      · exact hs
      · have hk := lookup_held s hs src i hi
        refine dir_ok s hs _ (rebind_nodup _ (rebind_nodup _ hs.1 _ _) _ _) ?_
        refine rebind_holds _ _ _ _ ?_ (by simp)
        exact rebind_holds _ _ _ _ hs.2.2.2.2
          (fun j hj => by simp only [Option.some.injEq] at hj; exact hj ▸ hk)
    · exact hs
  | remove name =>
    simp only [Fs.step]
    split
    · exact dir_ok s hs _ (rebind_nodup _ hs.1 _ _) (rebind_holds _ _ _ _ hs.2.2.2.2 (by simp))
    · exact hs
  | syncDir =>
    simp only [Fs.step]
    split
    · exact dir_ok s hs _ (hs.1.sublist (names_settle _)) (settle_holds _ _ hs.2.2.2.2)
    · exact hs
  | list => exact hs

/-- **Every operation that fails keeps the file system well formed.** -/
theorem fails_ok (s t : Fs) (hs : s.Ok) (op : Op) (h : s.Fails t op) : t.Ok := by
  cases op with
  | append i bs =>
    simp only [Fs.Fails, Fs.failures, List.mem_map] at h
    obtain ⟨k, _, rfl⟩ := h
    exact step_ok s hs _
  | sync i =>
    simp only [Fs.Fails, Fs.failures, List.mem_singleton] at h
    subst h
    exact onData_ok s hs i _ fun d hd => untrust_ok d hd
  | syncDir =>
    simp only [Fs.Fails, Fs.failures, List.mem_singleton] at h
    subst h
    exact hs
  | create _ | open_ _ | truncate _ _ | read _ _ _ | size _ | rename _ _ | remove _ | list =>
    simp only [Fs.Fails, Fs.failures, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · rw [h]; exact hs
    · rw [h]; exact step_ok s hs _

theorem run_ok (s : Fs) (hs : s.Ok) : ∀ ops, (s.run ops).Ok
  | [] => hs
  | op :: ops => run_ok _ (step_ok s hs op) ops

theorem empty_fs_ok : Fs.empty.Ok := ⟨List.nodup_nil, List.nodup_nil, nofun, nofun, nofun⟩

/-! ## Crashes -/

/-- Each of `as` related by `R` to the one of `bs` at its place. -/
def Each {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Each R as bs
  | _, _ => False

/-- What a crash leaves: what each name holds, and each file's octets, in their order. -/
structure Choice where
  names : List (Option Ino)
  data : List Bytes
  deriving DecidableEq

/-- Whether a crash may leave what `c` says. -/
def Fs.Allows (s : Fs) (c : Choice) : Prop :=
  Each Entry.Leaves s.dir c.names ∧ Each (fun p bs => Data.Leaves p.2 bs) s.files c.data

/-- The names a crash leaves, as good as synced. -/
def crashDir : List Entry → List (Option Ino) → List Entry
  | e :: es, b :: bs =>
    match b with
    | some i => ⟨e.name, some i, []⟩ :: crashDir es bs
    | none => crashDir es bs
  | _, _ => []

/-- The files a crash leaves, as good as synced. -/
def crashFiles : List (Ino × Data) → List Bytes → List (Ino × Data)
  | p :: ps, c :: cs => (p.1, p.2.after c) :: crashFiles ps cs
  | _, _ => []

/-- The file system without the files no name may be left holding: what a file system frees when
it is mounted again. -/
def Fs.prune (s : Fs) : Fs := { s with files := s.files.filter fun p => s.holds p.1 }

/-- The file system a crash left as `c` says. -/
def Fs.crashWith (s : Fs) (c : Choice) : Fs :=
  Fs.prune ⟨crashDir s.dir c.names, crashFiles s.files c.data, s.next, true⟩

/-- **What a crash may leave of `s`.** -/
def Crash (s t : Fs) : Prop := ∃ c, s.Allows c ∧ t = s.crashWith c

/-- The crash that loses nothing. -/
def Fs.current (s : Fs) : Choice := ⟨s.dir.map Entry.seen, s.files.map fun p => p.2.seen⟩

theorem each_map {α β : Type} (R : α → β → Prop) (f : α → β) :
    ∀ l : List α, (∀ a ∈ l, R a (f a)) → Each R l (l.map f)
  | [], _ => trivial
  | a :: l, h =>
    ⟨h a (List.mem_cons_self ..), each_map R f l fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

/-- **A crash may lose nothing.** -/
theorem crash_nothing_lost (s : Fs) (h : s.Ok) : Crash s (s.crashWith s.current) :=
  ⟨_, ⟨each_map _ _ _ fun e _ => entry_leaves_seen e,
    each_map _ _ _ fun p hp => leaves_seen p.2 (h.2.2.2.1 p hp)⟩, rfl⟩

theorem each_length {α β : Type} (R : α → β → Prop) :
    ∀ (as : List α) (bs : List β), Each R as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by simp [each_length R as bs h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem crashDir_settled_eq :
    ∀ (es : List Entry) (bs : List (Option Ino)), (∀ e ∈ es, e.Settled) →
      Each Entry.Leaves es bs → crashDir es bs = es
  | [], [], _, _ => rfl
  | e :: es, b :: bs, hs, ⟨hb, hr⟩ => by
    obtain ⟨hh, hsome⟩ := hs e (List.mem_cons_self ..)
    have ih := crashDir_settled_eq es bs (fun x hx => hs x (List.mem_cons_of_mem _ hx)) hr
    rcases e with ⟨name, synced, held⟩
    simp only at hh hsome
    subst hh
    rcases hb with rfl | hb
    · obtain ⟨i, rfl⟩ := Option.isSome_iff_exists.mp hsome
      simp [crashDir, ih]
    · simp at hb
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem crashFiles_filter (q : Ino → Bool) :
    ∀ (ps : List (Ino × Data)) (cs : List Bytes), (∀ p ∈ ps, q p.1 = true → p.2.Settled) →
      Each (fun p bs => Data.Leaves p.2 bs) ps cs →
      (crashFiles ps cs).filter (fun p => q p.1) = ps.filter (fun p => q p.1)
  | [], [], _, _ => rfl
  | p :: ps, c :: cs, hs, ⟨hc, hr⟩ => by
    have ih := crashFiles_filter q ps cs (fun x hx => hs x (List.mem_cons_of_mem _ hx)) hr
    simp only [crashFiles, List.filter_cons]
    cases hq : q p.1
    · simp [ih]
    · have hp := hs p (List.mem_cons_self ..) hq
      have hc' := (settled_leaves p.2 hp c).mp hc
      obtain ⟨hk, hh, ht⟩ := hp
      rcases p with ⟨i, ⟨seen, kept, high, written, trusted⟩⟩
      simp only at hk hh ht hc'
      subst hc' hk hh ht
      simp [Data.after, ih]
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- **With its names and the files they hold settled, a crash only frees the files no name
holds.** -/
theorem crash_prune (s t : Fs) (hd : s.dirTrusted = true) (hn : ∀ e ∈ s.dir, e.Settled)
    (hf : ∀ p ∈ s.files, s.holds p.1 = true → p.2.Settled) (h : Crash s t) : t = s.prune := by
  obtain ⟨c, ⟨hdl, hfl⟩, rfl⟩ := h
  rcases s with ⟨dir, files, next, trusted⟩
  simp only [Fs.holds] at hd hn hf hdl hfl
  subst hd
  simp only [Fs.crashWith, Fs.prune, Fs.holds, crashDir_settled_eq _ _ hn hdl]
  congr 1
  exact crashFiles_filter (fun i => dir.any (·.holds i)) _ _ hf hfl

/-- **A crash of a settled file system changes nothing.** -/
theorem crash_settled (s t : Fs) (hs : s.Settled) (h : Crash s t) : t = s := by
  obtain ⟨hd, hn, hf, hh⟩ := hs
  rw [crash_prune s t hd hn (fun p hp _ => hf p hp) h]
  simp only [Fs.prune]
  rw [List.filter_eq_self.mpr (fun p hp => hh p hp)]

theorem crashDir_settled :
    ∀ (es : List Entry) (bs : List (Option Ino)), ∀ e ∈ crashDir es bs, e.Settled
  | e :: es, some i :: bs, x, hx => by
    simp only [crashDir, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨rfl, rfl⟩
    · exact crashDir_settled es bs x hx
  | _ :: es, none :: bs, x, hx => crashDir_settled es bs x (by simpa [crashDir] using hx)
  | [], _, _, hx => by simp [crashDir] at hx
  | _ :: _, [], _, hx => by simp [crashDir] at hx

theorem crashFiles_settled :
    ∀ (ps : List (Ino × Data)) (cs : List Bytes), ∀ p ∈ crashFiles ps cs, p.2.Settled
  | p :: ps, c :: cs, x, hx => by
    simp only [crashFiles, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact after_settled _ _
    · exact crashFiles_settled ps cs x hx
  | [], _, _, hx => by simp [crashFiles] at hx
  | _ :: _, [], _, hx => by simp [crashFiles] at hx

/-- What a crash leaves is settled. -/
theorem crash_settles (s t : Fs) (h : Crash s t) : t.Settled := by
  obtain ⟨c, _, rfl⟩ := h
  refine ⟨rfl, crashDir_settled _ _, fun p hp => ?_, fun p hp => ?_⟩
  · simp only [Fs.crashWith, Fs.prune, List.mem_filter] at hp
    exact crashFiles_settled _ _ p hp.1
  · simp only [Fs.crashWith, Fs.prune, List.mem_filter] at hp
    exact hp.2

/-- **A crash of what a crash left changes nothing.** -/
theorem crash_twice (s t u : Fs) (h : Crash s t) (h' : Crash t u) : u = t :=
  crash_settled t u (crash_settles s t h) h'

/-! ## What a crash leaves of each name and each file -/

theorem crashDir_names :
    ∀ (es : List Entry) (bs : List (Option Ino)),
      List.Sublist ((crashDir es bs).map Entry.name) (es.map Entry.name)
  | e :: es, some _ :: bs => by
    simp only [crashDir, List.map_cons]
    exact (crashDir_names es bs).cons_cons _
  | e :: es, none :: bs => by
    simp only [crashDir, List.map_cons]
    exact (crashDir_names es bs).cons _
  | [], _ => by simp [crashDir]
  | _ :: _, [] => by simp [crashDir]

/-- The file a crash leaves a name holding is what the crash chose for it. -/
theorem lookup_crashDir :
    ∀ (es : List Entry) (bs : List (Option Ino)), (es.map Entry.name).Nodup →
      es.length = bs.length → ∀ name,
      ((crashDir es bs).find? (·.name == name)).bind Entry.seen =
        ((es.zip bs).find? (·.1.name == name)).bind Prod.snd
  | [], [], _, _, _ => rfl
  | e :: es, b :: bs, hn, hl, name => by
    simp only [List.map_cons, List.nodup_cons] at hn
    have ih := lookup_crashDir es bs hn.2 (by simpa using hl) name
    by_cases he : e.name = name
    · subst he
      have hnone : (crashDir es bs).find? (·.name == e.name) = none := by
        rw [List.find?_eq_none]
        intro x hx hxn
        have := (crashDir_names es bs).subset (List.mem_map_of_mem hx)
        simp only [beq_iff_eq] at hxn
        exact hn.1 (hxn ▸ this)
      cases b with
      | some i => simp [crashDir, Entry.seen]
      | none => simp [crashDir, hnone]
    · have hne : (e.name == name) = false := by simpa using he
      cases b with
      | some i => simp [crashDir, hne, ih]
      | none => simp [crashDir, hne, ih]
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

theorem each_find {α β : Type} (R : α → β → Prop) (p : α → Bool) :
    ∀ (as : List α) (bs : List β), Each R as bs → ∀ a b, (as.zip bs).find? (p ·.1) = some (a, b) →
      a ∈ as ∧ R a b
  | a' :: as, b' :: bs, ⟨hr, h⟩, a, b, hf => by
    simp only [List.zip_cons_cons, List.find?_cons] at hf
    split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨List.mem_cons_self .., hr⟩
    · obtain ⟨ha, hb⟩ := each_find R p as bs h a b hf
      exact ⟨List.mem_cons_of_mem _ ha, hb⟩
  | [], _, _, _, _, hf => by simp at hf
  | _ :: _, [], _, _, _, hf => by simp at hf

theorem find_name (es : List Entry) (hn : (es.map Entry.name).Nodup) (e : Entry) (he : e ∈ es) :
    es.find? (·.name == e.name) = some e := by
  induction es with
  | nil => simp at he
  | cons x es ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · have hx : (x.name == e.name) = false := by
        simp only [beq_eq_false_iff_ne]
        intro hxe
        exact hn.1 (hxe ▸ List.mem_map_of_mem he)
      simp [List.find?, hx, ih hn.2 he]

theorem mem_zip_of_mem {α β : Type} :
    ∀ (as : List α) (bs : List β), as.length = bs.length → ∀ a ∈ as, ∃ b, (a, b) ∈ as.zip bs
  | a' :: as, b' :: bs, hl, a, ha => by
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact ⟨b', by simp⟩
    · obtain ⟨b, hb⟩ := mem_zip_of_mem as bs (by simpa using hl) a ha
      exact ⟨b, by simp [hb]⟩
  | [], _, _, a, ha => by simp at ha
  | _ :: _, [], hl, _, _ => by simp at hl

/-- **A crash leaves each name as its own rule says**: what a crash may leave it holding. -/
theorem crash_lookup (s t : Fs) (hs : s.Ok) (h : Crash s t) (name : Bytes) :
    s.Leaves name (t.lookup name) := by
  obtain ⟨c, ⟨hd, _⟩, rfl⟩ := h
  have hl := each_length _ _ _ hd
  have key : (s.crashWith c).lookup name =
      ((s.dir.zip c.names).find? (·.1.name == name)).bind Prod.snd := by
    simp only [Fs.lookup, Fs.entry, Fs.crashWith, Fs.prune]
    exact lookup_crashDir _ _ hs.1 hl name
  rw [key]
  simp only [Fs.Leaves, Fs.entry]
  cases he : s.dir.find? (·.name == name) with
  | some e =>
    have hen : e.name = name := by simpa using List.find?_some he
    cases hf : (s.dir.zip c.names).find? (·.1.name == name) with
    | none =>
      exfalso
      obtain ⟨b, hb⟩ := mem_zip_of_mem _ _ hl e (List.mem_of_find?_eq_some he)
      rw [List.find?_eq_none] at hf
      exact absurd (by simpa using hen) (hf _ hb)
    | some p =>
      obtain ⟨hm, hr⟩ := each_find Entry.Leaves (·.name == name) _ _ hd p.1 p.2 (by simpa using hf)
      have hpn : p.1.name = name := by simpa using List.find?_some hf
      have hfind := find_name _ hs.1 _ hm
      rw [hpn, he] at hfind
      cases hfind
      simpa using hr
  | none =>
    have : (s.dir.zip c.names).find? (·.1.name == name) = none := by
      rw [List.find?_eq_none] at he ⊢
      intro x hx
      exact he x.1 (List.of_mem_zip hx).1
    simp [this, leavesOf]

theorem lookup_eq_find (i : Ino) :
    ∀ ps : List (Ino × Data), ps.lookup i = (ps.find? (i == ·.1)).map Prod.snd
  | [] => rfl
  | p :: ps => by
    rw [List.lookup_cons, lookup_eq_find i ps]
    cases h : i == p.1 <;> simp [h, List.find?]

theorem lookup_filter (q : Ino → Bool) (i : Ino) :
    ∀ ps : List (Ino × Data),
      (ps.filter fun p => q p.1).lookup i = if q i then ps.lookup i else none
  | [] => by simp
  | (j, d) :: ps => by
    have ih := lookup_filter q i ps
    by_cases hi : i = j
    · subst hi
      cases hq : q i
      · simp [hq, ih]
      · simp [hq]
    · have hne : (i == j) = false := by simpa using hi
      have hl : ∀ l : List (Ino × Data), List.lookup i ((j, d) :: l) = List.lookup i l :=
        fun l => by simp [List.lookup_cons, hne]
      cases hq : q j
      · simp only [List.filter_cons, hq, Bool.false_eq_true, ↓reduceIte, hl, ih]
      · simp only [List.filter_cons, hq, ↓reduceIte, hl, ih]

theorem lookup_crashFiles :
    ∀ (ps : List (Ino × Data)) (cs : List Bytes), ps.length = cs.length → ∀ i,
      (crashFiles ps cs).lookup i = ((ps.zip cs).find? (i == ·.1.1)).map fun x => x.1.2.after x.2
  | [], [], _, _ => rfl
  | p :: ps, c :: cs, hl, i => by
    have ih := lookup_crashFiles ps cs (by simpa using hl) i
    simp only [crashFiles, List.lookup_cons, List.zip_cons_cons, List.find?_cons]
    cases h : i == p.1
    · simp [ih]
    · simp
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem find_key (ps : List (Ino × Data)) (hn : (ps.map Prod.fst).Nodup) (p : Ino × Data)
    (hp : p ∈ ps) : ps.find? (p.1 == ·.1) = some p := by
  induction ps with
  | nil => simp at hp
  | cons x ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · have hx : (p.1 == x.1) = false := by
        simp only [beq_eq_false_iff_ne]
        intro hxe
        exact hn.1 (hxe ▸ List.mem_map_of_mem hp)
      simp [List.find?, hx, ih hn.2 hp]

/-- **A crash leaves each file as its own rule says**: holding octets its rule allows, as good as
synced, or freed if no name holds it; a file that never was, nowhere. -/
theorem crash_data (s t : Fs) (hs : s.Ok) (h : Crash s t) (i : Ino) :
    (∀ d, s.data i = some d →
      ∃ c, d.Leaves c ∧ (t.data i = some (d.after c) ∨ t.data i = none)) ∧
      (s.data i = none → t.data i = none) := by
  obtain ⟨c, ⟨_, hf⟩, rfl⟩ := h
  have hl := each_length _ _ _ hf
  have key : (crashFiles s.files c.data).lookup i =
      ((s.files.zip c.data).find? (i == ·.1.1)).map fun x => x.1.2.after x.2 :=
    lookup_crashFiles _ _ hl i
  have hpr : (s.crashWith c).data i =
      if (crashDir s.dir c.names).any (·.holds i) then (crashFiles s.files c.data).lookup i
      else none := by
    simp only [Fs.data, Fs.crashWith, Fs.prune, Fs.holds]
    exact lookup_filter (fun j => (crashDir s.dir c.names).any (·.holds j)) i _
  constructor
  · intro d hd
    simp only [Fs.data, lookup_eq_find, Option.map_eq_some_iff] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    have hpi : p.1 = i := (by simpa using List.find?_some hp : i = p.1).symm
    cases hz : (s.files.zip c.data).find? (i == ·.1.1) with
    | none =>
      exfalso
      obtain ⟨b, hb⟩ := mem_zip_of_mem _ _ hl p (List.mem_of_find?_eq_some hp)
      rw [List.find?_eq_none] at hz
      exact absurd (by simp [hpi]) (hz _ hb)
    | some x =>
      obtain ⟨hm, hr⟩ := each_find (fun p bs => Data.Leaves p.2 bs) (i == ·.1) _ _ hf x.1 x.2
        (by simpa using hz)
      have hxi : x.1.1 = i := (by simpa using List.find?_some hz : i = x.1.1).symm
      have hfind := find_key _ hs.2.1 _ hm
      rw [hxi, hp] at hfind
      cases hfind
      refine ⟨x.2, hr, ?_⟩
      rw [hpr, key, hz]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
  · intro hd
    simp only [Fs.data, lookup_eq_find, Option.map_eq_none_iff] at hd
    have : (s.files.zip c.data).find? (i == ·.1.1) = none := by
      rw [List.find?_eq_none] at hd ⊢
      intro x hx
      exact hd x.1 (List.of_mem_zip hx).1
    rw [hpr, key, this]
    split <;> rfl

theorem keys_crashFiles :
    ∀ (ps : List (Ino × Data)) (cs : List Bytes), ps.length = cs.length →
      (crashFiles ps cs).map Prod.fst = ps.map Prod.fst
  | p :: ps, c :: cs, hl => by
    simp only [crashFiles, List.map_cons, keys_crashFiles ps cs (by simpa using hl)]
  | [], [], _ => rfl
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

theorem crashDir_leaves :
    ∀ (es : List Entry) (bs : List (Option Ino)), Each Entry.Leaves es bs →
      ∀ e ∈ crashDir es bs, ∃ x ∈ es, ∀ i, e.Leaves (some i) → x.Leaves (some i)
  | e :: es, b :: bs, ⟨hb, hr⟩, x, hx => by
    cases b with
    | some i =>
      simp only [crashDir, List.mem_cons] at hx
      rcases hx with rfl | hx
      · refine ⟨e, List.mem_cons_self .., fun j hj => ?_⟩
        simp only [Entry.Leaves, Option.some.injEq, List.not_mem_nil, or_false] at hj
        exact hj ▸ hb
      · obtain ⟨y, hy, h⟩ := crashDir_leaves es bs hr x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, h⟩
    | none =>
      obtain ⟨y, hy, h⟩ := crashDir_leaves es bs hr x (by simpa [crashDir] using hx)
      exact ⟨y, List.mem_cons_of_mem _ hy, h⟩
  | [], _, _, _, hx => by simp [crashDir] at hx
  | _ :: _, [], h, _, _ => h.elim

/-- **What a crash leaves is well formed.** -/
theorem crash_ok (s t : Fs) (hs : s.Ok) (h : Crash s t) : t.Ok := by
  obtain ⟨c, ⟨hd, hf⟩, rfl⟩ := h
  obtain ⟨hn, hk, hlt, _, hh⟩ := hs
  have hkeys := keys_crashFiles _ _ (each_length _ _ _ hf)
  refine ⟨hn.sublist (crashDir_names _ _), ?_, ?_, ?_, ?_⟩
  · simp only [Fs.crashWith, Fs.prune]
    exact (hkeys ▸ hk).sublist (List.Sublist.map _ List.filter_sublist)
  · intro p hp
    simp only [Fs.crashWith, Fs.prune, List.mem_filter] at hp
    have := List.mem_map_of_mem (f := Prod.fst) hp.1
    rw [hkeys, List.mem_map] at this
    obtain ⟨q, hq, hpq⟩ := this
    exact hpq ▸ hlt q hq
  · intro p hp
    simp only [Fs.crashWith, Fs.prune, List.mem_filter] at hp
    exact settled_ok _ (crashFiles_settled _ _ p hp.1)
  · intro e he i hi
    simp only [Fs.crashWith, Fs.prune] at he ⊢
    obtain ⟨x, hx, hxl⟩ := crashDir_leaves _ _ hd e he
    have hin : i ∈ (crashFiles s.files c.data).map Prod.fst := hkeys ▸ hh x hx i (hxl i hi)
    simp only [List.mem_map] at hin ⊢
    obtain ⟨p, hp, rfl⟩ := hin
    refine ⟨p, List.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
    simp only [Fs.holds, List.any_eq_true]
    exact ⟨e, he, (holds_iff e p.1).mpr hi⟩

/-! ## Listing crashes -/

/-- Each way of taking one member of each list, in order. -/
def product {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap fun x => (product xss).map (x :: ·)

theorem mem_product {α : Type} :
    ∀ (xss : List (List α)) (l : List α), l ∈ product xss → Each (fun xs x => x ∈ xs) xss l
  | [], l, h => by simp only [product, List.mem_singleton] at h; subst h; trivial
  | xs :: xss, l, h => by
    simp only [product, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, l', hl', rfl⟩ := h
    exact ⟨hx, mem_product xss l' hl'⟩

theorem each_map_left {α β γ : Type} (R : β → γ → Prop) (f : α → β) :
    ∀ (as : List α) (cs : List γ), Each R (as.map f) cs → Each (fun a c => R (f a) c) as cs
  | [], [], _ => trivial
  | _ :: as, _ :: cs, ⟨h, hr⟩ => ⟨h, each_map_left R f as cs hr⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem each_imp {α β : Type} (R S : α → β → Prop) (hrs : ∀ a b, R a b → S a b) :
    ∀ (as : List α) (bs : List β), Each R as bs → Each S as bs
  | [], [], _ => trivial
  | a :: as, b :: bs, ⟨h, hr⟩ => ⟨hrs a b h, each_imp R S hrs as bs hr⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- `base` with `bs` written over it from `off`, no longer than it was. -/
def overwrite (base : Bytes) (off : Nat) (bs : Bytes) : Bytes :=
  base.take off ++ bs.take (base.length - off) ++ base.drop (off + bs.length)

/-- The octets kept, then those the latest of all the file's appends wrote at each place, zeros
where none did: what a crash leaves when the file system kept the latest of each place and undid a
cut it had not made durable. -/
def Data.latest (d : Data) : Bytes :=
  d.kept ++ ((d.written.foldl (fun acc w => overwrite acc w.1 w.2) (List.replicate d.high 0)).drop
    d.kept.length)

/-- Octets a crash may leave a file holding, each once, at every length it may: what the program
sees, what was last written at each place, the octets kept followed by zeros, and the file at its
longest with what the program sees cut anywhere and zeros after. Not every crash: no junk, and
quadratic in the file's length, so for small runs only. -/
def Data.cuts (d : Data) : List Bytes :=
  ((List.range (d.high + 1 - d.kept.length)).flatMap fun k =>
    let n := d.kept.length + k
    [(d.seen ++ List.replicate d.high 0).take n, d.latest.take n, d.kept ++ List.replicate k 0,
      (d.seen.take n ++ List.replicate d.high 0).take d.high])
    |>.eraseDups

/-- **Crashes listed**: every choice for each name, once, and each of the octets `cuts` gives a
file that a crash may leave it holding. -/
def Fs.choices (s : Fs) (cuts : Data → List Bytes) : List Choice :=
  (product (s.dir.map fun e => (e.synced :: e.held).eraseDups)).flatMap fun names =>
    (product (s.files.map fun p => (cuts p.2).filter p.2.leaves)).map fun data => ⟨names, data⟩

/-- **Every crash listed is a crash.** -/
theorem choices_allowed (s : Fs) (cuts : Data → List Bytes) (c : Choice)
    (h : c ∈ s.choices cuts) : s.Allows c := by
  simp only [Fs.choices, List.mem_flatMap, List.mem_map] at h
  obtain ⟨names, hn, data, hd, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · refine each_imp _ _ ?_ _ _ (each_map_left _ _ _ _ (mem_product _ _ hn))
    intro e b hb
    simp only [List.mem_eraseDups, List.mem_cons] at hb
    exact hb
  · refine each_imp _ _ ?_ _ _ (each_map_left _ _ _ _ (mem_product _ _ hd))
    intro p bs hb
    simp only [List.mem_filter] at hb
    exact (leaves_iff _ _).mp hb.2

/-- What `s` may be after a crash, each once, with each file holding one of the octets `cuts`
gives it. -/
def Fs.crashes (s : Fs) (cuts : Data → List Bytes) : List Fs :=
  ((s.choices cuts).map s.crashWith).eraseDups

theorem crashes_crash (s : Fs) (cuts : Data → List Bytes) (t : Fs) (h : t ∈ s.crashes cuts) :
    Crash s t := by
  simp only [Fs.crashes, List.mem_eraseDups, List.mem_map] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, choices_allowed s cuts c hc, rfl⟩

/-! ## The premises can hold -/

/-- A file written and synced under a name the directory has synced. -/
def sampleFs : Fs := Fs.empty.run [.create [1], .append 0 [2, 3], .sync 0, .syncDir]

/-- The premise `Fs.Settled` can hold: of the file system just synced. -/
theorem sample_settled : sampleFs.Settled := by
  unfold Fs.Settled Entry.Settled Data.Settled
  decide

/-- The premise `Fs.Ok` can hold: of what operations leave. -/
theorem sample_ok : sampleFs.Ok := run_ok _ empty_fs_ok _

/-- The premise `Data.Settled` can hold: of a file just synced. -/
theorem sample_data_settled : ((Data.empty.append [2, 3]).sync).Settled := by
  unfold Data.Settled
  decide

/-- The premise `Entry.Settled` can hold: of a name just synced. -/
theorem entry_settled_witness : Entry.Settled ⟨[1], some 0, []⟩ := ⟨rfl, rfl⟩

/-- The premise `Each` can hold: of a name and what a crash may leave it holding. -/
theorem each_witness : Each Entry.Leaves [⟨[1], none, [some 0]⟩] [some 0] :=
  ⟨Or.inr (List.mem_cons_self ..), trivial⟩

/-- A file written under a name nothing has synced. -/
def unsyncedFs : Fs :=
  ⟨[⟨[1], none, [some 0]⟩], [(0, ⟨[2, 3], [], 2, [(0, [2, 3])], true⟩)], 1, true⟩

/-- The premise `Crash` can hold: of a crash of it that keeps the name and one octet. -/
theorem crash_witness : Crash unsyncedFs (unsyncedFs.crashWith ⟨[some 0], [[2]]⟩) := by
  refine ⟨⟨[some 0], [[2]]⟩, ⟨?_, ?_⟩, rfl⟩
  · simp only [unsyncedFs, Each, and_true]
    exact Or.inr (List.mem_cons_self ..)
  · simp only [unsyncedFs, Each, and_true]
    exact (leaves_iff _ _).mp (by decide)

/-- The premise `Entry.Leaves` can hold: of a name created and not synced. -/
theorem entry_leaves_witness : Entry.Leaves ⟨[1], none, [some 0]⟩ (some 0) :=
  Or.inr (List.mem_cons_self ..)

/-- The premise `Fs.Leaves` can hold: of that name, in its file system. -/
theorem fs_leaves_witness : unsyncedFs.Leaves [1] (some 0) := entry_leaves_witness

/-- The premise `Fs.Fails` can hold: of a sync that failed. -/
theorem fails_witness : sampleFs.Fails (sampleFs.onData 0 Data.untrust).1 (.sync 0) :=
  List.mem_singleton.mpr rfl

/-! ## Examples -/

def bytesOf (s : String) : Bytes := s.toUTF8.toList.map (BitVec.ofNat 8 ·.toNat)

/-- A file created and written, nothing synced: a crash may leave the name or not, and the file
with any octets up to three, but never more. -/
def regression_893 : Bool :=
  let s := Fs.empty.run [.create (bytesOf "t"), .append 0 (bytesOf "abc")]
  let ts := s.crashes Data.cuts
  ts.any (·.lookup (bytesOf "t") == none) &&
    ts.any (fun t => t.lookup (bytesOf "t") == some 0 && (t.data 0).map (·.seen) == some []) &&
    ts.any (fun t => (t.data 0).map (·.seen) == some (bytesOf "abc")) &&
    ts.any (fun t => (t.data 0).map (·.seen) == some [0, 0]) &&
    ts.all (fun t => ((t.data 0).map (·.seen.length)).getD 0 ≤ 3)

/-- Synced and the directory synced: a crash leaves exactly what was there. -/
def regression_894 : Bool := sampleFs.crashes Data.cuts == [sampleFs]

/-- A rename the directory has not synced: a crash may leave either name, both or neither. -/
def regression_895 : Bool :=
  let t := bytesOf "t"
  let a := bytesOf "a"
  let s := Fs.empty.run [.create t, .sync 0, .syncDir, .rename t a]
  let ts := s.crashes Data.cuts
  let has (x y : Option Ino) := ts.any fun u => u.lookup t == x && u.lookup a == y
  has (some 0) none && has none (some 0) && has (some 0) (some 0) && has none none

/-- A synced file cut without a sync: a crash keeps the octets before the cut, and the file is
never longer than it was. -/
def regression_896 : Bool :=
  let s := Fs.empty.run [.create (bytesOf "j"), .append 0 (bytesOf "abcd"), .sync 0, .syncDir,
    .truncate 0 2]
  let ts := s.crashes Data.cuts
  ts.all (fun t => ((t.data 0).map fun d => (bytesOf "ab").isPrefixOf d.seen &&
      d.seen.length ≤ 4).getD false) &&
    ts.any (fun t => (t.data 0).map (·.seen) == some (bytesOf "ab")) &&
    ts.any (fun t => (t.data 0).map (·.seen) == some (bytesOf "abcd"))

/-- A crash of what a crash left changes nothing. -/
def regression_897 : Bool :=
  let s := Fs.empty.run [.create (bytesOf "t"), .append 0 (bytesOf "ab"), .create (bytesOf "u")]
  (s.crashes Data.cuts).all fun t => t.crashes Data.cuts == [t]

/-- What the program sees: a create under a name that holds a file answers so and changes
nothing; a rename onto itself, or between names of one file, changes nothing; a list leaves out
removed names; a read starts at its offset; a cut past the end adds zeros. -/
def regression_898 : Bool :=
  let a := bytesOf "a"
  let t := bytesOf "t"
  let s := Fs.empty.run [.create a, .append 0 (bytesOf "abcd"), .create t, .remove t]
  let both : Fs := ⟨[⟨a, some 0, []⟩, ⟨t, some 0, []⟩], s.files, s.next, true⟩
  s.step (.create a) == (s, .exists_) && (s.step (.rename a a)).1 == s &&
    (both.step (.rename t a)).1 == both &&
    (s.step .list).2 == .names [a] &&
    (s.step (.read 0 1 2)).2 == .bytes (bytesOf "bc") &&
    ((s.run [.truncate 0 6]).data 0).map (·.seen) == some (bytesOf "abcd" ++ [0, 0])

/-- A name keeps every file it held since the directory's last sync: created, removed and created
again, or renamed away and back, a crash may leave it holding any of them. -/
def regression_899 : Bool :=
  let a := bytesOf "a"
  let t := bytesOf "t"
  let s := Fs.empty.run [.create a, .sync 0, .syncDir, .remove a, .create a]
  let held := (s.crashes Data.cuts).map (·.lookup a)
  let r := Fs.empty.run [.create t, .sync 0, .syncDir, .rename t a, .rename a t]
  let both := (r.crashes Data.cuts).map fun u => (u.lookup t, u.lookup a)
  held.contains (some 0) && held.contains none && held.contains (some 1) &&
    both.contains (some 0, none) && both.contains (none, some 0) && both.contains (none, none)

/-- What a failure may have done: an append that fails, any first part of its octets; once a sync
has failed, a later one is no barrier, for a file or for the directory. -/
def regression_900 : Bool :=
  let a := bytesOf "a"
  let s := Fs.empty.run [.create a, .sync 0, .syncDir]
  let parts := (s.failures (.append 0 (bytesOf "ab"))).map fun u => (u.data 0).map (·.seen)
  let w := s.run [.append 0 (bytesOf "ab")]
  let afterFailedSync := ((w.failures (.sync 0)).map fun u => u.run [.sync 0]).flatMap
    fun u => (u.crashes Data.cuts).map fun v => (v.data 0).map (·.seen)
  let afterFailedDirSync := ((Fs.empty.run [.create a]).failures .syncDir).flatMap
    fun u => ((u.run [.syncDir]).crashes Data.cuts).map (·.lookup a)
  parts == [some [], some (bytesOf "a"), some (bytesOf "ab")] &&
    afterFailedSync.contains (some []) && afterFailedDirSync.contains none

/-- A crash frees a file no name holds. -/
def regression_901 : Bool :=
  let s := Fs.empty.run [.create (bytesOf "t"), .append 0 (bytesOf "ab"), .remove (bytesOf "t"),
    .syncDir]
  (s.crashes Data.cuts).all (·.files == [])

/-- Crashes listed include an append cut short and filled with zeros to its length. -/
def regression_902 : Bool :=
  let s := Fs.empty.run [.create (bytesOf "j"), .sync 0, .syncDir, .append 0 (bytesOf "abcd")]
  (s.crashes Data.cuts).any fun t => (t.data 0).map (·.seen) == some (bytesOf "ab" ++ [0, 0])

end DN.News.FsModel
