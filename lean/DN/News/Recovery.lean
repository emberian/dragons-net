-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Journal

/-!
# DN.News.Recovery

How the store recovers at start, as docs/decisions/0005-article-store.md ("On disk") fixes it. After
syncing the journal and the directory it reads each name with its file's octets and finds either the
corruption that keeps the store from starting, more articles than the store holds (`capacity`; not
corruption: a build with more room wrote them), or the store it starts with — the journal's key, its
articles as the commits give them, the files set aside, the next sequence number, where the journal
ends — and its actions: a torn tail's octets kept under a number of their own and the directory
synced; the tail truncated and the truncation synced; then names tidied — temporary files removed,
and a final file no record names set aside, or removed when set aside already or when the journal
ended cleanly and no kept tail is numbered above it, so no cut tail can have held its record. A
failed action stops recovery, and the store does not start.

Proven: what recovery starts with is sound — every article's file in the directory with its size, no
sequence number twice, article numbers rising in every group, every group carried (`recover_sound`);
its articles are the journal's commits (`recover_articles`); its next sequence number is above every
number a record or a name carries (`recover_next`); it takes files only from temporary names and
final names no record has, and gives only names no file holds (`recover_safe`); it changes the
journal only by cutting its torn tail or making again one with no record (`recover_journal`); it
takes no file before the cut (`recover_order`), and removes a final file no record names only when
no cut tail can have held its record (`recover_removes`); afterwards the journal ends where the next
record goes (`recover_journalEnd`); whatever a crash leaves of its actions — of each nothing or all,
a file renamed under both its names or neither, a tail kept with any of its octets — the next start
finds the same articles, under any key of sixteen octets and the same groups while a number is left
(`recover_partly`), and so does a start after all of them (`recover_again`). A cut or creation of
the journal a crash leaves in part is reasoned about with the frames written in it.
-/

namespace DN.News.Recovery

open DN.News.Journal
open DN.News.CommandSpec (ascii)

/-- The spool directory as recovery reads it: each name with the octets its file holds. -/
abbrev Image := List (Bytes × Bytes)

/-- What the store is given when it starts. -/
structure Config where
  /-- the groups the store carries -/
  groups : List Bytes
  /-- sixteen random octets, the key of a journal recovery creates -/
  key : Bytes

/-- The most articles the store holds (docs/decisions/0005-article-store.md, "Bounds"): recovery
counts commits against it; the program, accepting, the files set aside too. -/
def capacity : Nat := 4096

/-- Why the store does not start: it is corrupt, past a bound, or given a bad key. -/
inductive Fault
  /-- a name of no shape the store gives -/
  | badName (name : Bytes)
  /-- files and no journal, or a journal without its format among other files -/
  | noJournal
  /-- a journal that does not read back: where, and why -/
  | journal (at_ : Nat) (why : Why)
  /-- a sequence number in two records -/
  | seqTwice (seq : Nat)
  /-- an article number in a group not above the one an earlier record gave it there -/
  | numberNotAbove (group : Bytes) (number : Nat)
  /-- a group the configuration lacks -/
  | unknownGroup (group : Bytes)
  /-- a record naming a file that is missing -/
  | missingFile (seq : Nat)
  /-- a record naming a file of another size -/
  | wrongSize (seq : Nat)
  /-- no sequence number left to give -/
  | exhausted
  /-- a key for a new journal that is not of sixteen octets -/
  | badKey
  /-- more articles than `capacity`, as many as this -/
  | tooMany (count : Nat)
  deriving DecidableEq

/-- What recovery does to the directory. -/
inductive Action
  /-- a new file under a name no file holds, holding these octets, synced -/
  | keep (name octets : Bytes)
  /-- a file moved to another name -/
  | rename (src dst : Bytes)
  /-- a name removed -/
  | remove (name : Bytes)
  /-- the directory synced -/
  | syncDir
  /-- the journal cut to a length, and synced -/
  | cut (n : Nat)
  /-- the journal created, or made again, holding its format under a key, and synced -/
  | create (key : Bytes)
  deriving DecidableEq

/-- The store recovery starts. -/
structure Store where
  /-- the key of the journal -/
  key : Bytes
  /-- the commits of the journal, in its order -/
  articles : List Commit
  /-- the sequence numbers of the files set aside: articles quarantined and tails kept -/
  setAside : List Nat
  /-- the sequence number the next article gets -/
  next : Nat
  /-- where the journal ends, and the next record goes -/
  journalEnd : Nat
  deriving DecidableEq

/-! ## The rules -/

/-- The sequence number a name carries. -/
def seqOf : Name → Option Nat
  | .journal => none
  | .final s | .temp s | .quarantine s | .tail s => some s

/-- The commits among records. -/
def commitsOf (rs : List Record) : List Commit :=
  rs.filterMap fun r => match r with
    | .commit c => some c
    | _ => none

/-- A sequence number two commits carry. -/
def seqTwice? : List Commit → Option Nat
  | [] => none
  | c :: cs => if cs.any (·.seq == c.seq) then some c.seq else seqTwice? cs

/-- The highest article number groups give one of them. -/
def highOf : List Group → Bytes → Nat
  | [], _ => 0
  | g :: gs, name => max (if g.name == name then g.number else 0) (highOf gs name)

/-- The highest article number commits gave a group. -/
def highIn : List Commit → Bytes → Nat
  | [], _ => 0
  | c :: cs, name => max (highOf c.groups name) (highIn cs name)

/-- A group and an article number a commit gave it that is not above the highest the commits
`before` it gave the group. -/
def notAbove? (before : List Commit) : List Commit → Option (Bytes × Nat)
  | [] => none
  | c :: cs =>
    match c.groups.find? (fun g => g.number ≤ highIn before g.name) with
    | some g => some (g.name, g.number)
    | none => notAbove? (before ++ [c]) cs

/-- A group of a commit the configuration lacks. -/
def unknownGroup? (cfg : Config) (cs : List Commit) : Option Bytes :=
  ((cs.flatMap (·.groups)).find? fun g => !cfg.groups.contains g.name).map (·.name)

/-- The fault of the first commit whose file is missing or of another size. -/
def fileFault? (img : Image) : List Commit → Option Fault
  | [] => none
  | c :: cs =>
    match img.lookup (finalName c.seq) with
    | none => some (.missingFile c.seq)
    | some f => if f.length = c.fileSize then fileFault? img cs else some (.wrongSize c.seq)

/-- The store a new journal starts. -/
def fresh (cfg : Config) : Store := ⟨cfg.key, [], [], 1, firstFrame⟩

/-- One more than the highest sequence number the commits and the names carry. -/
def nextSeq (cs : List Commit) (names : List Name) : Nat :=
  (cs.map (·.seq) ++ names.filterMap seqOf).foldl max 0 + 1

/-- Whether a final file no record names, numbered `s`, is set aside: when the journal ends in a
torn tail, or a tail kept before is numbered above it — numbers are given in order, so a file
numbered above every tail kept was made after them, and no tail can have held its record. -/
def setsAside (names : List Name) (torn : Bool) (s : Nat) : Bool :=
  torn || names.any fun n => match n with
    | .tail m => decide (s < m)
    | _ => false

/-- What recovery does to a name, `recorded` the names of the records' files: a temporary file
removed; a final file no record names set aside, or removed when it is set aside already or is not
to be. -/
def tidyName (recorded : List Bytes) (names : List Name) (torn : Bool) : Name → Option Action
  | .temp s => some (.remove (tempName s))
  | .final s =>
    if recorded.contains (finalName s) then none
    else if names.contains (.quarantine s) || !setsAside names torn s then
      some (.remove (finalName s))
    else some (.rename (finalName s) (quarantineName s))
  | _ => none

/-- The sequence number a name keeps among the files set aside, once recovery is done. -/
def asideOf (recorded : List Bytes) (names : List Name) (torn : Bool) : Name → Option Nat
  | .final s =>
    if !recorded.contains (finalName s) && !names.contains (.quarantine s) &&
        setsAside names torn s then some s
    else none
  | .quarantine s | .tail s => some s
  | _ => none

/-- Recovery once the journal's format and commits are read: the number of articles, the rules
across records, the files the records name, and what is done to the directory, given where a torn
tail starts, if any. -/
def recoverRecords (cfg : Config) (img : Image) (names : List Name) (content key : Bytes)
    (cs : List Commit) (cut : Option Nat) : Except Fault (Store × List Action) :=
  if capacity < cs.length then .error (.tooMany cs.length) else
  match seqTwice? cs, notAbove? [] cs, unknownGroup? cfg cs, fileFault? img cs with
  | some s, _, _, _ => .error (.seqTwice s)
  | none, some (g, n), _, _ => .error (.numberNotAbove g n)
  | none, none, some g, _ => .error (.unknownGroup g)
  | none, none, none, some f => .error f
  | none, none, none, none =>
    let next0 := nextSeq cs names
    let next := if cut.isSome then next0 + 1 else next0
    if 2 ^ 64 ≤ next then .error .exhausted
    else
      let recorded := cs.map (finalName ·.seq)
      let tidy := names.filterMap (tidyName recorded names cut.isSome)
      let ops :=
        (match cut with
          | some x => [Action.keep (tailName next0) (le 8 x ++ content.drop x), .syncDir, .cut x]
          | none => []) ++
        tidy ++ (if tidy.isEmpty then [] else [.syncDir])
      let setAside := names.filterMap (asideOf recorded names cut.isSome) ++
        (if cut.isSome then [next0] else [])
      .ok (⟨key, cs, setAside, next, cut.getD content.length⟩, ops)

/-- Where a journal's torn tail starts, if it ends in one. -/
def cutOf : End → Option Nat
  | .torn x => some x
  | _ => none

/-- The name of a file in the directory, or why it is none. -/
def nameOf (p : Bytes × Bytes) : Except Fault Name :=
  (parseName p.1).elim (.error (.badName p.1)) .ok

/-- Recovery with a key of the right length. -/
def recoverWith (cfg : Config) (img : Image) : Except Fault (Store × List Action) :=
  match img.mapM nameOf with
  | .error f => .error f
  | .ok names =>
    match img.lookup journalName with
    | none =>
      if img.isEmpty then .ok (fresh cfg, [.create cfg.key, .syncDir]) else .error .noJournal
    | some content =>
      let sc := scan content
      match sc.ending, sc.records with
      | .corrupt at_ w, _ => .error (.journal at_ w)
      | _, [] => if img.length = 1 then .ok (fresh cfg, [.create cfg.key]) else .error .noJournal
      | ending, .format key :: rest =>
        recoverRecords cfg img names content key (commitsOf rest) (cutOf ending)
      | _, _ => .error (.journal 0 .notARecord)

/-- **How the store recovers**: the corruption that keeps it from starting, or the store it starts
with and what it does to the directory first. -/
def recover (cfg : Config) (img : Image) : Except Fault (Store × List Action) :=
  if cfg.key.length = keyLength then recoverWith cfg img else .error .badKey

/-! ## What recovery's actions do -/

/-- The directory with `name` holding `octets`. -/
def setName (img : Image) (name octets : Bytes) : Image :=
  img.filter (·.1 != name) ++ [(name, octets)]

/-- The directory without `name`. -/
def dropName (img : Image) (name : Bytes) : Image := img.filter (·.1 != name)

/-- What an action does to the directory, once done and durable. -/
def apply (img : Image) : Action → Image
  | .keep name octets => setName img name octets
  | .rename src dst =>
    match img.lookup src with
    | some f => setName (dropName img src) dst f
    | none => img
  | .remove name => dropName img name
  | .syncDir => img
  | .cut n => img.map fun p => if p.1 == journalName then (p.1, p.2.take n) else p
  | .create key => setName img journalName ((Record.format key).encode key 0)

/-- What actions do to the directory, in order. -/
def applyAll (img : Image) (ops : List Action) : Image := ops.foldl apply img

/-! ## What is proven of the rules -/

theorem mapM_nameOf : ∀ (img : Image) (names : List Name), img.mapM nameOf = .ok names →
    (∀ p ∈ img, (parseName p.1).isSome) ∧ names = img.filterMap (parseName ·.1)
  | [], names, h => by simp [pure, Except.pure] at h; subst h; simp
  | p :: img, names, h => by
    simp only [List.mapM_cons, bind, Except.bind, nameOf] at h
    cases hp : parseName p.1 with
    | none => simp [hp] at h
    | some n =>
      simp only [hp, Option.elim] at h
      cases hm : img.mapM nameOf with
      | error f => simp [hm] at h
      | ok ns =>
        simp only [hm, pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨hall, rfl⟩ := mapM_nameOf img ns hm
        subst h
        refine ⟨?_, by simp [hp]⟩
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · simp [hp]
        · exact hall q hq

theorem mapM_nameOf_ok : ∀ (img : Image), (∀ p ∈ img, (parseName p.1).isSome) →
    img.mapM nameOf = .ok (img.filterMap (parseName ·.1))
  | [], _ => rfl
  | p :: img, h => by
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h p (List.mem_cons_self ..))
    have ih := mapM_nameOf_ok img fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp [List.mapM_cons, bind, Except.bind, nameOf, hn, ih, pure, Except.pure]

theorem mem_names (img : Image) (n : Name) :
    n ∈ img.filterMap (parseName ·.1) ↔ ∃ p ∈ img, parseName p.1 = some n := by
  simp [List.mem_filterMap]

theorem seqTwice_none : ∀ cs : List Commit, seqTwice? cs = none → (cs.map (·.seq)).Nodup
  | [], _ => List.nodup_nil
  | c :: cs, h => by
    simp only [seqTwice?] at h
    split at h
    · simp at h
    · rename_i hany
      refine List.nodup_cons.mpr ⟨?_, seqTwice_none cs h⟩
      intro hm
      simp only [List.mem_map] at hm
      obtain ⟨c', hc', he⟩ := hm
      exact hany (List.any_eq_true.mpr ⟨c', hc', by simp [he]⟩)

theorem le_highOf : ∀ (gs : List Group) (g : Group), g ∈ gs → g.number ≤ highOf gs g.name
  | x :: gs, g, hg => by
    simp only [List.mem_cons] at hg
    simp only [highOf]
    rcases hg with rfl | hg
    · simp only [beq_self_eq_true, ↓reduceIte]
      omega
    · have := le_highOf gs g hg
      omega
  | [], _, hg => by simp at hg

theorem le_highIn : ∀ (cs : List Commit) (c : Commit) (g : Group), c ∈ cs → g ∈ c.groups →
    g.number ≤ highIn cs g.name
  | x :: cs, c, g, hc, hg => by
    simp only [List.mem_cons] at hc
    simp only [highIn]
    rcases hc with rfl | hc
    · have := le_highOf c.groups g hg
      omega
    · have := le_highIn cs c g hc hg
      omega
  | [], _, _, hc, _ => by simp at hc

/-- Article numbers rise in every group: a commit gives a group a number above any an earlier
commit gave it. -/
def Rising (cs : List Commit) : Prop :=
  ∀ c c', List.Sublist [c, c'] cs → ∀ g ∈ c.groups, ∀ g' ∈ c'.groups, g.name = g'.name →
    g.number < g'.number

theorem notAbove_none : ∀ (before cs : List Commit), notAbove? before cs = none →
    (∀ c ∈ cs, ∀ g ∈ c.groups, highIn before g.name < g.number) ∧ Rising cs
  | _, [], _ => ⟨by simp, fun c c' h => by simp at h⟩
  | before, c :: cs, h => by
    simp only [notAbove?] at h
    split at h
    · simp at h
    · rename_i hf
      obtain ⟨ih1, ih2⟩ := notAbove_none (before ++ [c]) cs h
      have hc : ∀ g ∈ c.groups, highIn before g.name < g.number := by
        intro g hg
        rw [List.find?_eq_none] at hf
        have := hf g hg
        simp only [decide_eq_true_eq] at this
        omega
      have hmono : ∀ name, highIn before name ≤ highIn (before ++ [c]) name := by
        intro name
        clear ih1 ih2 hc hf h
        induction before with
        | nil => simp [highIn]
        | cons x xs ihx => simp only [List.cons_append, highIn]; have := ihx; omega
      refine ⟨?_, ?_⟩
      · intro x hx g hg
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hc g hg
        · have := ih1 x hx g hg
          have := hmono g.name
          omega
      · intro x y hxy g hg g' hg' hn
        rcases List.sublist_cons_iff.mp hxy with hxy | ⟨r, hr, hxy⟩
        · exact ih2 x y hxy g hg g' hg' hn
        · simp only [List.cons.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          have hy : y ∈ cs := hxy.subset (List.mem_singleton_self _)
          have := ih1 y hy g' hg'
          have := le_highIn (before ++ [x]) x g (by simp) hg
          rw [hn] at this
          omega

theorem unknownGroup_none (cfg : Config) (cs : List Commit) (h : unknownGroup? cfg cs = none) :
    ∀ c ∈ cs, ∀ g ∈ c.groups, g.name ∈ cfg.groups := by
  intro c hc g hg
  simp only [unknownGroup?, Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h g (List.mem_flatMap.mpr ⟨c, hc, hg⟩)
  simpa using this

theorem fileFault_none (img : Image) : ∀ cs : List Commit, fileFault? img cs = none →
    ∀ c ∈ cs, ∃ f, img.lookup (finalName c.seq) = some f ∧ f.length = c.fileSize
  | [], _ => by simp
  | c :: cs, h => by
    simp only [fileFault?] at h
    split at h
    · simp at h
    · rename_i f hf
      split at h
      · rename_i hl
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨f, hf, hl⟩
        · exact fileFault_none img cs h x hx
      · simp at h

theorem fileFault_congr (img img' : Image) : ∀ cs : List Commit,
    (∀ c ∈ cs, img'.lookup (finalName c.seq) = img.lookup (finalName c.seq)) →
      fileFault? img' cs = fileFault? img cs
  | [], _ => rfl
  | c :: cs, h => by
    simp only [fileFault?, h c (List.mem_cons_self ..),
      fileFault_congr img img' cs fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- What `recoverRecords` gives when it gives a store. -/
theorem recoverRecords_ok (cfg : Config) (img : Image) (names : List Name) (content key : Bytes)
    (cs : List Commit) (cut : Option Nat) (st : Store) (ops : List Action)
    (h : recoverRecords cfg img names content key cs cut = .ok (st, ops)) :
    seqTwice? cs = none ∧ notAbove? [] cs = none ∧ unknownGroup? cfg cs = none ∧
      fileFault? img cs = none ∧ st.key = key ∧ st.articles = cs ∧
      st.next = (if cut.isSome then nextSeq cs names + 1 else nextSeq cs names) ∧
      st.next < 2 ^ 64 ∧ st.journalEnd = cut.getD content.length := by
  unfold recoverRecords at h
  split at h
  · cases h
  split at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rename_i h1 h2 h3 h4
    dsimp only at h
    by_cases hlt : 2 ^ 64 ≤ (if cut.isSome then nextSeq cs names + 1 else nextSeq cs names)
    · rw [if_pos hlt] at h
      simp at h
    · rw [if_neg hlt] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨h1, h2, h3, h4, rfl, rfl, rfl, by dsimp only; omega, rfl⟩

theorem recoverWith_cases (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recoverWith cfg img = .ok (st, ops)) :
    (∀ p ∈ img, (parseName p.1).isSome) ∧
      ((img = [] ∧ st = fresh cfg ∧ ops = [.create cfg.key, .syncDir]) ∨
       (∃ content, img.lookup journalName = some content ∧
         (((scan content).records = [] ∧ (∀ x w, (scan content).ending ≠ .corrupt x w) ∧
            img.length = 1 ∧ st = fresh cfg ∧ ops = [.create cfg.key]) ∨
          ∃ key rest, (scan content).records = .format key :: rest ∧
            (∀ x w, (scan content).ending ≠ .corrupt x w) ∧
            recoverRecords cfg img (img.filterMap (parseName ·.1)) content key (commitsOf rest)
              (cutOf (scan content).ending) = .ok (st, ops)))) := by
  unfold recoverWith at h
  cases hm : img.mapM nameOf with
  | error f => simp [hm] at h
  | ok names =>
    obtain ⟨hall, rfl⟩ := mapM_nameOf img names hm
    simp only [hm] at h
    refine ⟨hall, ?_⟩
    cases hj : img.lookup journalName with
    | none =>
      simp only [hj] at h
      split at h
      · rename_i he
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact Or.inl ⟨List.isEmpty_iff.mp he, h.1.symm, h.2.symm⟩
      · simp at h
    | some content =>
      simp only [hj] at h
      refine Or.inr ⟨content, rfl, ?_⟩
      generalize hs : scan content = sc at h
      rcases sc with ⟨rs, ending⟩
      simp only at h ⊢
      cases ending with
      | corrupt x w => simp at h
      | clean | torn x =>
        cases rs with
        | nil =>
          simp only at h
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            exact Or.inl ⟨rfl, by simp, by assumption, h.1.symm, h.2.symm⟩
          · simp at h
        | cons r rest =>
          cases r with
          | format key => exact Or.inr ⟨key, rest, rfl, by simp, h⟩
          | commit c => simp at h
          | start => simp at h

/-- The actions `recoverRecords` plans, when it gives a store. -/
theorem recoverRecords_ops (cfg : Config) (img : Image) (names : List Name) (content key : Bytes)
    (cs : List Commit) (cut : Option Nat) (st : Store) (ops : List Action)
    (h : recoverRecords cfg img names content key cs cut = .ok (st, ops)) :
    ops = (match cut with
        | some x => [Action.keep (tailName (nextSeq cs names)) (le 8 x ++ content.drop x),
            .syncDir, .cut x]
        | none => []) ++
      names.filterMap (tidyName (cs.map (finalName ·.seq)) names cut.isSome) ++
      (if (names.filterMap (tidyName (cs.map (finalName ·.seq)) names cut.isSome)).isEmpty then []
        else [.syncDir]) := by
  unfold recoverRecords at h
  split at h
  · cases h
  split at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · dsimp only at h
    by_cases hlt : 2 ^ 64 ≤ (if cut.isSome then nextSeq cs names + 1 else nextSeq cs names)
    · rw [if_pos hlt] at h
      simp at h
    · rw [if_neg hlt] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm

/-- The journal recovery reads, when it gives a store from one with records. -/
theorem recover_cases (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) :
    cfg.key.length = keyLength ∧ (∀ p ∈ img, (parseName p.1).isSome) ∧
      ((img = [] ∧ st = fresh cfg ∧ ops = [.create cfg.key, .syncDir]) ∨
       (∃ content, img.lookup journalName = some content ∧
         (((scan content).records = [] ∧ (∀ x w, (scan content).ending ≠ .corrupt x w) ∧
            img.length = 1 ∧ st = fresh cfg ∧ ops = [.create cfg.key]) ∨
          ∃ key rest, (scan content).records = .format key :: rest ∧
            (∀ x w, (scan content).ending ≠ .corrupt x w) ∧
            recoverRecords cfg img (img.filterMap (parseName ·.1)) content key (commitsOf rest)
              (cutOf (scan content).ending) = .ok (st, ops)))) := by
  by_cases hk : cfg.key.length = keyLength
  · rw [recover, if_pos hk] at h
    exact ⟨hk, recoverWith_cases cfg img st ops h⟩
  · rw [recover, if_neg hk] at h
    simp at h

/-- **What recovery starts with is sound**: every article's file is in the directory it read, of the
size its record gives; no sequence number twice; article numbers rising in every group; every group
carried; and a sequence number left to give. -/
theorem recover_sound (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) :
    (∀ c ∈ st.articles, ∃ f, img.lookup (finalName c.seq) = some f ∧ f.length = c.fileSize) ∧
      (st.articles.map (·.seq)).Nodup ∧ Rising st.articles ∧
      (∀ c ∈ st.articles, ∀ g ∈ c.groups, g.name ∈ cfg.groups) ∧ st.next < 2 ^ 64 := by
  obtain ⟨_, _, hc⟩ := recover_cases cfg img st ops h
  rcases hc with ⟨_, rfl, _⟩ | ⟨content, _, ⟨_, _, _, rfl, _⟩ | ⟨key, rest, _, _, hr⟩⟩
  · exact ⟨by simp [fresh], by simp [fresh], fun c c' h => by simp [fresh] at h, by simp [fresh],
      by simp [fresh]⟩
  · exact ⟨by simp [fresh], by simp [fresh], fun c c' h => by simp [fresh] at h, by simp [fresh],
      by simp [fresh]⟩
  · obtain ⟨h1, h2, h3, h4, _, harts, _, hnext, _⟩ := recoverRecords_ok _ _ _ _ _ _ _ _ _ hr
    rw [harts]
    exact ⟨fileFault_none img _ h4, seqTwice_none _ h1, (notAbove_none [] _ h2).2,
      unknownGroup_none cfg _ h3, hnext⟩

/-- **Recovery's articles are the journal's commits**, in its order. -/
theorem recover_articles (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) (content : Bytes)
    (hj : img.lookup journalName = some content) :
    st.articles = commitsOf (scan content).records.tail := by
  obtain ⟨_, _, hc⟩ := recover_cases cfg img st ops h
  rcases hc with ⟨rfl, _, _⟩ | ⟨content', hj', hc⟩
  · simp at hj
  · rw [hj] at hj'
    cases hj'
    rcases hc with ⟨hrs, _, _, rfl, _⟩ | ⟨key, rest, hrs, _, hr⟩
    · simp [hrs, fresh, commitsOf]
    · obtain ⟨_, _, _, _, _, harts, _⟩ := recoverRecords_ok _ _ _ _ _ _ _ _ _ hr
      simp [hrs, harts]

/-! ## What recovery's actions touch -/

theorem final_ne_journal (x : Nat) : finalName x ≠ journalName := by
  intro h; have := congrArg List.length h
  simp [finalName, journalName, ascii, hex16, hexOf_length] at this

theorem temp_ne_journal (x : Nat) : tempName x ≠ journalName := by
  intro h; have := congrArg List.length h
  simp [tempName, journalName, ascii, hex16, hexOf_length] at this

theorem quarantine_ne_journal (x : Nat) : quarantineName x ≠ journalName := by
  intro h; have := congrArg List.length h
  simp [quarantineName, journalName, ascii, hex16, hexOf_length] at this

theorem tail_ne_journal (x : Nat) : tailName x ≠ journalName := by
  intro h; have := congrArg List.length h
  simp [tailName, journalName, ascii, hex16, hexOf_length] at this

theorem final_ne_temp (x y : Nat) : finalName x ≠ tempName y := by
  intro h; have := congrArg List.head? h; simp [finalName, tempName, ascii] at this

theorem final_ne_quarantine (x y : Nat) : finalName x ≠ quarantineName y := by
  intro h; have := congrArg List.head? h; simp [finalName, quarantineName, ascii] at this

theorem final_ne_tail (x y : Nat) : finalName x ≠ tailName y := by
  intro h; have := congrArg List.head? h; simp [finalName, tailName, ascii] at this

theorem lookup_filter_ne (img : Image) (n k : Bytes) :
    (img.filter (·.1 != n)).lookup k = if k = n then none else img.lookup k := by
  induction img with
  | nil => split <;> rfl
  | cons p img ih =>
    rcases p with ⟨m, o⟩
    by_cases hkn : k = n
    · subst hkn
      rw [if_pos rfl] at ih ⊢
      by_cases hm : m = k
      · subst hm
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih]
      · have hb : (m != k) = true := by simpa using hm
        have hkm : (k == m) = false := by
          simp only [beq_eq_false_iff_ne]; exact fun e => hm e.symm
        simp only [List.filter_cons, hb, ↓reduceIte, List.lookup_cons, hkm, ih]
    · rw [if_neg hkn] at ih ⊢
      by_cases hm : m = n
      · subst hm
        have hkm : (k == m) = false := by simpa using hkn
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.lookup_cons, hkm, ih]
      · have hb : (m != n) = true := by simpa using hm
        simp only [List.filter_cons, hb, ↓reduceIte, List.lookup_cons, ih]

theorem lookup_setName (img : Image) (n o k : Bytes) :
    (setName img n o).lookup k = if k = n then some o else img.lookup k := by
  unfold setName
  rw [List.lookup_append, lookup_filter_ne]
  split
  · rename_i hk
    subst hk
    simp
  · rename_i hk
    cases img.lookup k with
    | some _ => rfl
    | none =>
      have : (k == n) = false := by simpa using hk
      simp [List.lookup_cons, this]

theorem lookup_dropName (img : Image) (n k : Bytes) :
    (dropName img n).lookup k = if k = n then none else img.lookup k :=
  lookup_filter_ne img n k

theorem lookup_cut (img : Image) (x : Nat) (k : Bytes) :
    (apply img (.cut x)).lookup k =
      if k = journalName then (img.lookup k).map (·.take x) else img.lookup k := by
  simp only [apply]
  induction img with
  | nil => split <;> rfl
  | cons p img ih =>
    rcases p with ⟨m, o⟩
    by_cases hkj : k = journalName
    · subst hkj
      rw [if_pos rfl] at ih ⊢
      by_cases hm : m = journalName
      · subst hm
        simp only [List.map_cons, beq_self_eq_true, ↓reduceIte, List.lookup_cons, Option.map_some]
      · have hmb : (m == journalName) = false := by simpa using hm
        have hkm : (journalName == m) = false := by
          simp only [beq_eq_false_iff_ne]; exact fun e => hm e.symm
        simp only [List.map_cons, hmb, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, hkm, ih]
    · rw [if_neg hkj] at ih ⊢
      by_cases hm : m = journalName
      · subst hm
        have hkm : (k == journalName) = false := by simpa using hkj
        simp only [List.map_cons, beq_self_eq_true, ↓reduceIte, List.lookup_cons, hkm, ih]
      · have hmb : (m == journalName) = false := by simpa using hm
        simp only [List.map_cons, hmb, Bool.false_eq_true, ↓reduceIte, List.lookup_cons, ih]

theorem mem_setName (img : Image) (n o : Bytes) (p : Bytes × Bytes) (h : p ∈ setName img n o) :
    p ∈ img ∨ p = (n, o) := by
  simp only [setName, List.mem_append, List.mem_filter, List.mem_singleton] at h
  rcases h with ⟨h, _⟩ | h
  · exact Or.inl h
  · exact Or.inr h

theorem mem_dropName (img : Image) (n : Bytes) (p : Bytes × Bytes) (h : p ∈ dropName img n) :
    p ∈ img := (List.mem_filter.mp h).1

theorem mem_cut (img : Image) (x : Nat) (p : Bytes × Bytes) (h : p ∈ apply img (.cut x)) :
    ∃ q ∈ img, q.1 = p.1 := by
  simp only [apply, List.mem_map] at h
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨q, hq, by split <;> rfl⟩

theorem foldl_max_ge : ∀ (l : List Nat) (acc : Nat),
    acc ≤ l.foldl max acc ∧ ∀ x ∈ l, x ≤ l.foldl max acc
  | [], _ => ⟨Nat.le_refl _, by simp⟩
  | y :: l, acc => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max acc y)
    refine ⟨by simp only [List.foldl_cons]; omega, ?_⟩
    intro x hx
    simp only [List.mem_cons] at hx
    simp only [List.foldl_cons]
    rcases hx with rfl | hx
    · omega
    · exact h2 x hx

theorem foldl_max_le (m : Nat) : ∀ (l : List Nat) (acc : Nat), acc ≤ m → (∀ x ∈ l, x ≤ m) →
    l.foldl max acc ≤ m
  | [], _, h, _ => h
  | y :: l, acc, h, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le m l _ (by have := hl y (List.mem_cons_self ..); omega)
      fun x hx => hl x (List.mem_cons_of_mem _ hx)

theorem lt_nextSeq_name (cs : List Commit) (names : List Name) (n : Name) (hn : n ∈ names)
    (s : Nat) (hs : seqOf n = some s) : s < nextSeq cs names := by
  have := (foldl_max_ge (cs.map (·.seq) ++ names.filterMap seqOf) 0).2 s
    (List.mem_append_right _ (List.mem_filterMap.mpr ⟨n, hn, hs⟩))
  simp only [nextSeq]
  omega

theorem lt_nextSeq_commit (cs : List Commit) (names : List Name) (c : Commit) (hc : c ∈ cs) :
    c.seq < nextSeq cs names := by
  have := (foldl_max_ge (cs.map (·.seq) ++ names.filterMap seqOf) 0).2 c.seq
    (List.mem_append_left _ (List.mem_map_of_mem hc))
  simp only [nextSeq]
  omega

theorem nextSeq_le (cs : List Commit) (names : List Name) (m : Nat) (hc : ∀ c ∈ cs, c.seq ≤ m)
    (hn : ∀ n ∈ names, ∀ s, seqOf n = some s → s ≤ m) : nextSeq cs names ≤ m + 1 := by
  have := foldl_max_le m (cs.map (·.seq) ++ names.filterMap seqOf) 0 (Nat.zero_le _) (by
    intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_filterMap] at hx
    rcases hx with ⟨c, hc', rfl⟩ | ⟨n, hn', hs⟩
    · exact hc c hc'
    · exact hn n hn' x hs)
  simp only [nextSeq]
  omega

/-- An action recovery plans, from the journal's octets `content`, its commits `cs`, where its torn
tail starts `cut`, the names `names` and the number `next0` for a tail kept. -/
inductive Planned (content : Bytes) (cs : List Commit) (names : List Name) (cut : Option Nat)
    (next0 : Nat) : Action → Prop
  | keep (x : Nat) : cut = some x →
      Planned content cs names cut next0 (.keep (tailName next0) (le 8 x ++ content.drop x))
  | syncDir : Planned content cs names cut next0 .syncDir
  | cut (x : Nat) : cut = some x → Planned content cs names cut next0 (.cut x)
  | removeTemp (s : Nat) : .temp s ∈ names →
      Planned content cs names cut next0 (.remove (tempName s))
  | removeFinal (s : Nat) : .final s ∈ names → finalName s ∉ cs.map (finalName ·.seq) →
      (.quarantine s ∈ names ∨ setsAside names cut.isSome s = false) →
      Planned content cs names cut next0 (.remove (finalName s))
  | setAside (s : Nat) : .final s ∈ names → finalName s ∉ cs.map (finalName ·.seq) →
      .quarantine s ∉ names → setsAside names cut.isSome s = true →
      Planned content cs names cut next0 (.rename (finalName s) (quarantineName s))

theorem tidyName_planned (content : Bytes) (cs : List Commit) (names : List Name)
    (cut : Option Nat) (next0 : Nat) (n : Name) (hn : n ∈ names) (a : Action)
    (h : tidyName (cs.map (finalName ·.seq)) names cut.isSome n = some a) :
    Planned content cs names cut next0 a := by
  cases n with
  | temp s =>
    simp only [tidyName, Option.some.injEq] at h
    subst h
    exact .removeTemp s hn
  | final s =>
    simp only [tidyName] at h
    split at h
    · simp at h
    · rename_i hr
      have hr' : finalName s ∉ cs.map (finalName ·.seq) := by simpa using hr
      split at h
      · rename_i hq
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hq
        exact .removeFinal s hn hr' hq
      · rename_i hq
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem, not_or,
          Bool.not_eq_false] at hq
        exact .setAside s hn hr' hq.1 hq.2
  | journal => simp [tidyName] at h
  | quarantine s => simp [tidyName] at h
  | tail s => simp [tidyName] at h

/-- **Recovery plans only these actions.** -/
theorem recoverRecords_planned (cfg : Config) (img : Image) (names : List Name)
    (content key : Bytes) (cs : List Commit) (cut : Option Nat) (st : Store) (ops : List Action)
    (h : recoverRecords cfg img names content key cs cut = .ok (st, ops)) :
    ∀ a ∈ ops, Planned content cs names cut (nextSeq cs names) a := by
  unfold recoverRecords at h
  split at h
  · cases h
  split at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · dsimp only at h
    by_cases hlt : 2 ^ 64 ≤ (if cut.isSome then nextSeq cs names + 1 else nextSeq cs names)
    · rw [if_pos hlt] at h
      simp at h
    · rw [if_neg hlt] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro a ha
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · cases hc : cut with
        | none => simp [hc] at ha
        | some x =>
          simp only [hc, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · exact .keep x rfl
          · exact .syncDir
          · exact .cut x rfl
      · simp only [List.mem_filterMap] at ha
        obtain ⟨n, hn, hna⟩ := ha
        exact tidyName_planned content cs names cut _ n hn a hna
      · split at ha
        · simp at ha
        · simp only [List.mem_singleton] at ha
          subst ha
          exact .syncDir

/-- What a crash may leave of an action recovery had begun, taken whole: nothing of it, all of it, a
file renamed under both its names or under neither, or a file kept with any of its octets. -/
inductive Left : Image → Action → Image → Prop
  | none (img : Image) (a : Action) : Left img a img
  | all (img : Image) (a : Action) : Left img a (apply img a)
  | both (img : Image) (src dst f : Bytes) : img.lookup src = some f →
      Left img (.rename src dst) (setName img dst f)
  | lost (img : Image) (src dst : Bytes) : Left img (.rename src dst) (dropName img src)
  | some (img : Image) (name octets o : Bytes) : Left img (.keep name octets) (setName img name o)

/-- What a crash may leave of actions recovery had begun, in their order. -/
inductive Partly : Image → List Action → Image → Prop
  | nil (img : Image) : Partly img [] img
  | cons (img img' img'' : Image) (a : Action) (ops : List Action) :
      Left img a img' → Partly img' ops img'' → Partly img (a :: ops) img''

/-- What recovery's actions keep, done in part or in all: every name of a shape the store gives,
with a number no higher than `top`; the journal as it was, or cut where its torn tail starts; and
the file of every record as it was. -/
def Keeps (img : Image) (content : Bytes) (cs : List Commit) (cut : Option Nat) (top : Nat)
    (img' : Image) : Prop :=
  (∀ p ∈ img', ∃ n, parseName p.1 = some n ∧ ∀ s, seqOf n = some s → s ≤ top) ∧
    (img'.lookup journalName = some content ∨
      ∃ x, cut = some x ∧ img'.lookup journalName = some (content.take x)) ∧
    ∀ c ∈ cs, img'.lookup (finalName c.seq) = img.lookup (finalName c.seq)

theorem name_seq_valid (n : Name) (hv : n.valid = true) (s : Nat) (hs : seqOf n = some s) :
    s < 2 ^ 64 := by
  cases n <;> simp_all [seqOf, Name.valid]

/-- Each planned action keeps what recovery's actions keep. -/
theorem left_keeps (img : Image) (content : Bytes) (cs : List Commit) (names : List Name)
    (cut : Option Nat) (next0 : Nat) (hnext : next0 < 2 ^ 64)
    (hnames : ∀ n ∈ names, (n.valid = true) ∧ ∀ s, seqOf n = some s → s < next0)
    (J J' : Image) (a : Action) (hp : Planned content cs names cut next0 a)
    (hk : Keeps img content cs cut next0 J) (hl : Left J a J') :
    Keeps img content cs cut next0 J' := by
  obtain ⟨k1, k2, k3⟩ := hk
  -- an image with one name set, the journal and the records' files untouched
  have set_ok : ∀ (n : Name) (o : Bytes), n.valid = true → (∀ s, seqOf n = some s → s ≤ next0) →
      n.bytes ≠ journalName → (∀ c ∈ cs, n.bytes ≠ finalName c.seq) →
      Keeps img content cs cut next0 (setName J n.bytes o) := by
    intro n o hv hs hj hf
    refine ⟨fun q hq => ?_, ?_, fun c hc => ?_⟩
    · rcases mem_setName J _ _ q hq with hq | rfl
      · exact k1 q hq
      · exact ⟨n, parseName_bytes n hv, hs⟩
    · rw [lookup_setName, if_neg (Ne.symm hj)]
      exact k2
    · rw [lookup_setName, if_neg (fun e => hf c hc e.symm)]
      exact k3 c hc
  have drop_ok : ∀ (m : Bytes), m ≠ journalName → (∀ c ∈ cs, m ≠ finalName c.seq) →
      ∀ J'', (∀ q ∈ J'', q ∈ J) → (∀ k, k ≠ m → J''.lookup k = J.lookup k) →
      Keeps img content cs cut next0 J'' := by
    intro m hj hf J'' hmem hlk
    refine ⟨fun q hq => k1 q (hmem q hq), ?_, fun c hc => ?_⟩
    · rw [hlk _ (Ne.symm hj)]; exact k2
    · rw [hlk _ (fun e => hf c hc e.symm)]; exact k3 c hc
  cases hl with
  | none => exact ⟨k1, k2, k3⟩
  | all =>
    cases hp with
    | keep x hx =>
      exact set_ok (.tail next0) _ (by simp [Name.valid, hnext]) (by simp [seqOf])
        (tail_ne_journal _) (fun c _ e => final_ne_tail _ _ e.symm)
    | syncDir => exact ⟨k1, k2, k3⟩
    | cut x hx =>
      refine ⟨fun q hq => ?_, ?_, fun c hc => ?_⟩
      · obtain ⟨q', hq', he⟩ := mem_cut J x q hq
        obtain ⟨n, hn, hs⟩ := k1 q' hq'
        exact ⟨n, he ▸ hn, hs⟩
      · rw [lookup_cut, if_pos rfl]
        rcases k2 with h2 | ⟨y, hy, h2⟩
        · exact Or.inr ⟨x, hx, by rw [h2]; rfl⟩
        · rw [hx] at hy
          cases hy
          refine Or.inr ⟨x, hx, ?_⟩
          rw [h2]
          simp [List.take_take]
      · rw [lookup_cut, if_neg (final_ne_journal _)]
        exact k3 c hc
    | removeTemp s hs =>
      exact drop_ok _ (temp_ne_journal s) (fun c _ e => final_ne_temp _ _ e.symm) _
        (fun q hq => mem_dropName J _ q hq)
        (fun k hk => by rw [apply, lookup_dropName, if_neg hk])
    | removeFinal s hs hr =>
      exact drop_ok _ (final_ne_journal s)
        (fun c hc e => hr (List.mem_map.mpr ⟨c, hc, e.symm⟩)) _
        (fun q hq => mem_dropName J _ q hq)
        (fun k hk => by rw [apply, lookup_dropName, if_neg hk])
    | setAside s hs hr hq =>
      obtain ⟨hv, hlt⟩ := hnames _ hs
      have hsv : s < 2 ^ 64 := name_seq_valid _ hv s rfl
      simp only [apply]
      cases hf : J.lookup (finalName s) with
      | none => exact ⟨k1, k2, k3⟩
      | some f =>
        have hd := drop_ok (finalName s) (final_ne_journal s)
          (fun c hc e => hr (List.mem_map.mpr ⟨c, hc, e.symm⟩)) (dropName J (finalName s))
          (fun q hq => mem_dropName J _ q hq) (fun k hk => by rw [lookup_dropName, if_neg hk])
        obtain ⟨d1, d2, d3⟩ := hd
        refine ⟨fun q hq' => ?_, ?_, fun c hc => ?_⟩
        · rcases mem_setName _ _ _ q hq' with hq' | rfl
          · exact d1 q hq'
          · exact ⟨.quarantine s, parseName_bytes (.quarantine s) (by simp [Name.valid, hsv]),
              fun t ht => by
                simp only [seqOf, Option.some.injEq] at ht
                have := hlt s rfl
                omega⟩
        · rw [lookup_setName, if_neg (Ne.symm (quarantine_ne_journal s))]; exact d2
        · rw [lookup_setName, if_neg (fun e => final_ne_quarantine _ _ e)]; exact d3 c hc
  | both src dst f hf =>
    cases hp with
    | setAside s hs hr hq =>
      obtain ⟨hv, hlt⟩ := hnames _ hs
      have hsv : s < 2 ^ 64 := name_seq_valid _ hv s rfl
      exact set_ok (.quarantine s) f (by simp [Name.valid, hsv])
        (fun t ht => by
          simp only [seqOf, Option.some.injEq] at ht
          have := hlt s rfl
          omega) (quarantine_ne_journal s)
        (fun c _ e => final_ne_quarantine _ _ e.symm)
  | some name octets o =>
    cases hp with
    | keep x hx =>
      exact set_ok (.tail next0) o (by simp [Name.valid, hnext]) (by simp [seqOf])
        (tail_ne_journal _) (fun c _ e => final_ne_tail _ _ e.symm)
  | lost src dst =>
    cases hp with
    | setAside s hs hr hq =>
      exact drop_ok _ (final_ne_journal s)
        (fun c hc e => hr (List.mem_map.mpr ⟨c, hc, e.symm⟩)) _
        (fun q hq => mem_dropName J _ q hq)
        (fun k hk => by rw [lookup_dropName, if_neg hk])

theorem partly_keeps (img : Image) (content : Bytes) (cs : List Commit) (names : List Name)
    (cut : Option Nat) (next0 : Nat) (hnext : next0 < 2 ^ 64)
    (hnames : ∀ n ∈ names, (n.valid = true) ∧ ∀ s, seqOf n = some s → s < next0) :
    ∀ (ops : List Action) (J J' : Image), (∀ a ∈ ops, Planned content cs names cut next0 a) →
      Keeps img content cs cut next0 J → Partly J ops J' → Keeps img content cs cut next0 J'
  | [], J, J', _, hk, hp => by cases hp; exact hk
  | a :: ops, J, J', ha, hk, hp => by
    cases hp with
    | cons _ J1 _ _ _ hl hp' =>
      exact partly_keeps img content cs names cut next0 hnext hnames ops J1 J'
        (fun b hb => ha b (List.mem_cons_of_mem _ hb))
        (left_keeps img content cs names cut next0 hnext hnames J J1 a
          (ha a (List.mem_cons_self ..)) hk hl) hp'

/-- Recovery gives a store only of `capacity` articles or fewer. -/
theorem recoverRecords_fits (cfg : Config) (img : Image) (names : List Name) (content key : Bytes)
    (cs : List Commit) (cut : Option Nat) (st : Store) (ops : List Action)
    (h : recoverRecords cfg img names content key cs cut = .ok (st, ops)) :
    cs.length ≤ capacity := by
  unfold recoverRecords at h
  split at h
  · cases h
  · omega

theorem recoverRecords_of (cfg : Config) (img : Image) (names : List Name) (content key : Bytes)
    (cs : List Commit) (cut : Option Nat) (h0 : cs.length ≤ capacity)
    (h1 : seqTwice? cs = none) (h2 : notAbove? [] cs = none)
    (h3 : unknownGroup? cfg cs = none) (h4 : fileFault? img cs = none)
    (hn : (if cut.isSome then nextSeq cs names + 1 else nextSeq cs names) < 2 ^ 64) :
    ∃ st ops, recoverRecords cfg img names content key cs cut = .ok (st, ops) ∧ st.articles = cs ∧
      st.key = key := by
  unfold recoverRecords
  rw [if_neg (by omega)]
  simp only [h1, h2, h3, h4]
  rw [if_neg (by omega)]
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem recover_of (cfg : Config) (hkey : cfg.key.length = keyLength) (J : Image)
    (content key : Bytes) (rest : List Record) (e : End)
    (hall : ∀ p ∈ J, (parseName p.1).isSome) (hj : J.lookup journalName = some content)
    (hs : scan content = ⟨.format key :: rest, e⟩) (he : ∀ x w, e ≠ .corrupt x w) :
    recover cfg J = recoverRecords cfg J (J.filterMap (parseName ·.1)) content key (commitsOf rest)
      (cutOf e) := by
  rw [recover, if_pos hkey]
  unfold recoverWith
  rw [mapM_nameOf_ok J hall]
  cases e with
  | clean => simp only [hj, hs]
  | torn x => simp only [hj, hs]
  | corrupt x w => exact absurd rfl (he x w)

theorem format_journal (k : Bytes) : journal k [] = (Record.format k).encode k 0 := by
  simp [journal, encodeFrom]

/-- A directory with a new journal alone recovers to a new store under that journal's key. -/
theorem recover_new (cfg : Config) (hkey : cfg.key.length = keyLength) (k : Bytes)
    (hk : k.length = keyLength) :
    ∃ st ops, recover cfg [(journalName, (Record.format k).encode k 0)] =
      .ok (st, ops) ∧ st.articles = [] ∧ st.key = k := by
  have hs := scan_encoded k hk [] (fun _ h => by simp at h)
  rw [format_journal] at hs
  rw [recover_of cfg hkey _ _ k [] .clean
    (by intro p hp; simp only [List.mem_singleton] at hp; subst hp
        rw [show journalName = Name.journal.bytes from rfl, parseName_bytes _ rfl]; rfl)
    (by simp) hs (by simp)]
  exact recoverRecords_of cfg _ _ _ _ [] none (Nat.zero_le _) rfl rfl rfl rfl
    (by simp [nextSeq, List.filterMap]; decide)

theorem parse_journal : parseName journalName = some .journal := by
  rw [show journalName = Name.journal.bytes from rfl, parseName_bytes _ rfl]

/-- An empty directory recovers to a new store, its journal to be created. -/
theorem recover_empty (cfg : Config) (hkey : cfg.key.length = keyLength) :
    recover cfg [] = .ok (fresh cfg, [.create cfg.key, .syncDir]) := by
  rw [recover, if_pos hkey]
  rfl

/-- A journal alone that holds no record recovers to a new store, the journal to be made again. -/
theorem recover_unformatted (cfg : Config) (hkey : cfg.key.length = keyLength) (content : Bytes)
    (hr : (scan content).records = []) (he : ∀ x w, (scan content).ending ≠ .corrupt x w) :
    recover cfg [(journalName, content)] = .ok (fresh cfg, [.create cfg.key]) := by
  have hall : ∀ p ∈ [(journalName, content)], (parseName p.1).isSome := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    simp [parse_journal]
  rw [recover, if_pos hkey]
  unfold recoverWith
  rw [mapM_nameOf_ok _ hall]
  simp only [List.lookup_cons, beq_self_eq_true]
  generalize hs : scan content = sc at hr he
  rcases sc with ⟨rs, ending⟩
  simp only at hr he
  subst hr
  cases ending with
  | corrupt x w => exact absurd rfl (he x w)
  | clean => rfl
  | torn x => rfl

/-- **Whatever a crash leaves of recovery's actions, taken whole, the next start finds the same
articles**: each action left undone, done, a file renamed under both its names or under neither, or
a tail kept with any of its octets — whatever key the host gives that start, and under the same
journal's key unless recovery was to create the journal; as long as a sequence number is left for
one more kept tail. A cut or a creation of the journal the crash left in part is reasoned about with
the frames written in the journal. -/
theorem recover_partly (cfg cfg' : Config) (hgroups : cfg'.groups = cfg.groups)
    (hkey' : cfg'.key.length = keyLength) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) (hroom : st.next + 1 < 2 ^ 64) (img' : Image)
    (hp : Partly img ops img') :
    ∃ st' ops', recover cfg' img' = .ok (st', ops') ∧ st'.articles = st.articles ∧
      (.create cfg.key ∉ ops → st'.key = st.key) := by
  obtain ⟨hkey, hall, hc⟩ := recover_cases cfg img st ops h
  rcases hc with ⟨rfl, rfl, rfl⟩ |
    ⟨content, hj, ⟨hrs, hcor0, hlen, rfl, rfl⟩ | ⟨key, rest, hrs, hcor, hr⟩⟩
  · -- an empty directory, and a journal created
    cases hp with
    | cons _ J1 _ _ _ hl hp' =>
      cases hp' with
      | cons _ J2 _ _ _ hl' hp'' =>
        cases hp''
        have hJ1 : J1 = [] ∨ J1 = [(journalName, (Record.format cfg.key).encode cfg.key 0)] := by
          cases hl with
          | none => exact Or.inl rfl
          | all => exact Or.inr rfl
        have hJ2 : img' = J1 := by cases hl' <;> rfl
        subst hJ2
        rcases hJ1 with rfl | rfl
        · exact ⟨_, _, recover_empty cfg' hkey', rfl, fun h => absurd (by simp) h⟩
        · obtain ⟨st', ops', h', ha, _⟩ := recover_new cfg' hkey' cfg.key hkey
          exact ⟨st', ops', h', by simp [ha, fresh], fun h => absurd (by simp) h⟩
  · -- a journal without its format, alone, and made again
    have himg : img = [(journalName, content)] := by
      match img, hlen with
      | [(n, o)], _ =>
        simp only [List.lookup_cons] at hj
        split at hj
        · rename_i hq
          simp only [beq_iff_eq] at hq
          simp only [Option.some.injEq] at hj
          rw [hq, hj]
        · simp at hj
    subst himg
    cases hp with
    | cons _ J1 _ _ _ hl hp' =>
      cases hp'
      cases hl with
      | none =>
        exact ⟨_, _, recover_unformatted cfg' hkey' content hrs hcor0, rfl,
          fun h => absurd (by simp) h⟩
      | all =>
        obtain ⟨st', ops', h', ha, _⟩ := recover_new cfg' hkey' cfg.key hkey
        refine ⟨st', ops', ?_, by simp [ha, fresh], fun h => absurd (by simp) h⟩
        simpa [apply, setName] using h'
  · -- a journal with records
    obtain ⟨h1, h2, h3, h4, hkeyst, harts, hnext, hlt, -⟩ := recoverRecords_ok _ _ _ _ _ _ _ _ _ hr
    have h0 := recoverRecords_fits _ _ _ _ _ _ _ _ _ hr
    have h3' : unknownGroup? cfg' (commitsOf rest) = none := by
      rw [← h3]; simp [unknownGroup?, hgroups]
    have hplan := recoverRecords_planned _ _ _ _ _ _ _ _ _ hr
    obtain ⟨e, he⟩ : ∃ e, (scan content).ending = e := ⟨_, rfl⟩
    have hsc : scan content = ⟨.format key :: rest, e⟩ := by rw [← hrs, ← he]
    rw [he] at hcor hnext hplan
    generalize hnamesdef : img.filterMap (parseName ·.1) = names at hnext hplan
    generalize hcsdef : commitsOf rest = cs at h0 h1 h2 h3 h3' h4 harts hnext hplan
    generalize hcutdef : cutOf e = cut at hnext hplan
    have hmem : ∀ n, n ∈ names ↔ ∃ q ∈ img, parseName q.1 = some n := by
      intro n; rw [← hnamesdef]; exact mem_names img n
    have hnext0 : nextSeq cs names < 2 ^ 64 := by
      split at hnext <;> omega
    have hnames : ∀ n ∈ names, (n.valid = true) ∧ ∀ s, seqOf n = some s → s < nextSeq cs names :=
      by
        intro n hn
        obtain ⟨q, _, hq⟩ := (hmem n).mp hn
        exact ⟨parseName_valid _ _ hq, fun s hs => lt_nextSeq_name cs names n hn s hs⟩
    have hk0 : Keeps img content cs cut (nextSeq cs names) img := by
      refine ⟨fun q hq => ?_, Or.inl hj, fun _ _ => rfl⟩
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hall q hq)
      refine ⟨n, hn, fun s hs => ?_⟩
      have := lt_nextSeq_name cs names n ((hmem n).mpr ⟨q, hq, hn⟩) s hs
      omega
    obtain ⟨k1, k2, k3⟩ := partly_keeps img content cs names cut _ hnext0 hnames ops img img'
      hplan hk0 hp
    have hall' : ∀ q ∈ img', (parseName q.1).isSome := by
      intro q hq
      obtain ⟨n, hn, _⟩ := k1 q hq
      simp [hn]
    have hseq' : ∀ n ∈ img'.filterMap (parseName ·.1), ∀ s, seqOf n = some s →
        s ≤ nextSeq cs names := by
      intro n hn s hs
      obtain ⟨q, hq, hqn⟩ := (mem_names img' n).mp hn
      obtain ⟨n', hn', hs'⟩ := k1 q hq
      rw [hqn] at hn'
      cases hn'
      exact hs' s hs
    have hcs : ∀ c ∈ cs, c.seq ≤ nextSeq cs names := fun c hc =>
      Nat.le_of_lt (lt_nextSeq_commit cs names c hc)
    have hbound := nextSeq_le cs (img'.filterMap (parseName ·.1)) _ hcs hseq'
    have h4' : fileFault? img' cs = none := by rw [fileFault_congr img img' cs k3]; exact h4
    have finish : ∀ (content' : Bytes) (e' : End) (cut' : Option Nat),
        img'.lookup journalName = some content' →
        scan content' = ⟨.format key :: rest, e'⟩ → (∀ x w, e' ≠ .corrupt x w) →
        cutOf e' = cut' →
        (if cut'.isSome then nextSeq cs (img'.filterMap (parseName ·.1)) + 1
          else nextSeq cs (img'.filterMap (parseName ·.1))) < 2 ^ 64 →
        ∃ st' ops', recover cfg' img' = .ok (st', ops') ∧ st'.articles = st.articles ∧
          (.create cfg.key ∉ ops → st'.key = st.key) := by
      intro content' e' cut' hj' hs' hc' hcut' hn'
      rw [recover_of cfg' hkey' img' content' key rest e' hall' hj' hs' hc', hcut', hcsdef]
      obtain ⟨st', ops', h', ha, hk⟩ := recoverRecords_of cfg' img' _ content' key cs cut' h0 h1 h2
        h3' h4' hn'
      exact ⟨st', ops', h', by rw [ha, harts], fun _ => by rw [hk, hkeyst]⟩
    rcases k2 with hj' | ⟨x, hx, hj'⟩
    · -- the journal as it was
      refine finish content e cut hj' hsc hcor hcutdef ?_
      cases hc : cut.isSome <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hnext ⊢ <;> omega
    · -- the journal cut where its torn tail started
      cases e with
      | corrupt y w => exact absurd rfl (hcor y w)
      | clean => rw [← hcutdef] at hx; simp [cutOf] at hx
      | torn y =>
        rw [← hcutdef] at hx
        simp only [cutOf, Option.some.injEq] at hx
        subst hx
        refine finish (content.take y) .clean none hj' (scan_take content _ y hsc) (by simp) rfl ?_
        rw [← hcutdef] at hnext
        simp only [cutOf, Option.isSome_some, ↓reduceIte] at hnext
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        omega

/-- **After all of recovery's actions, recovering again finds the same articles.** -/
theorem recover_again (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) (hroom : st.next + 1 < 2 ^ 64) :
    ∃ st' ops', recover cfg (applyAll img ops) = .ok (st', ops') ∧ st'.articles = st.articles := by
  have hall : ∀ (ops : List Action) (J : Image), Partly J ops (applyAll J ops) := by
    intro ops
    induction ops with
    | nil => intro J; exact .nil J
    | cons a ops ih => intro J; exact .cons J _ _ a ops (.all J a) (ih _)
  obtain ⟨st', ops', h', ha, -⟩ :=
    recover_partly cfg cfg rfl (recover_cases cfg img st ops h).1 img st ops h hroom _
      (hall ops img)
  exact ⟨st', ops', h', ha⟩

/-- The name an action takes a file from, if any. -/
def Action.takes : Action → Option Bytes
  | .rename src _ => some src
  | .remove name => some name
  | _ => none

/-- The name an action gives a file, if any. -/
def Action.gives : Action → Option Bytes
  | .keep name _ => some name
  | .rename _ dst => some dst
  | _ => none

theorem lookup_none_of_name (img : Image) (n : Name) (hv : n.valid = true)
    (h : n ∉ img.filterMap (parseName ·.1)) : img.lookup n.bytes = none := by
  rw [List.mem_filterMap] at h
  induction img with
  | nil => rfl
  | cons p img ih =>
    rcases p with ⟨m, o⟩
    have hm : m ≠ n.bytes := by
      intro e
      exact h ⟨(m, o), List.mem_cons_self .., by simp only; rw [e]; exact parseName_bytes n hv⟩
    have hb : (n.bytes == m) = false := by
      simp only [beq_eq_false_iff_ne]; exact fun e => hm e.symm
    simp only [List.lookup_cons, hb]
    exact ih fun ⟨q, hq, hqn⟩ => h ⟨q, List.mem_cons_of_mem _ hq, hqn⟩

/-- **Recovery takes files only from temporary names and from final names no record has**, never
from an article or a file set aside, and gives files only names no file holds; what it does to the
journal, `recover_journal` says. -/
theorem recover_safe (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) (a : Action) (ha : a ∈ ops) :
    (∀ n, a.takes = some n →
      (∃ s, n = tempName s) ∨ (∃ s, n = finalName s ∧ n ∉ st.articles.map (finalName ·.seq))) ∧
    (∀ n, a.gives = some n → img.lookup n = none) := by
  obtain ⟨hkey, hall, hc⟩ := recover_cases cfg img st ops h
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨content, hj, ⟨_, _, _, rfl, rfl⟩ | ⟨key, rest, _, _, hr⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [Action.takes, Action.gives]
  · simp only [List.mem_singleton] at ha
    subst ha
    simp [Action.takes, Action.gives]
  · obtain ⟨_, _, _, _, _, harts, hnext, _, _⟩ := recoverRecords_ok _ _ _ _ _ _ _ _ _ hr
    have hnext0 : nextSeq (commitsOf rest) (img.filterMap (parseName ·.1)) < 2 ^ 64 := by
      split at hnext <;> omega
    have hp := recoverRecords_planned _ _ _ _ _ _ _ _ _ hr a ha
    rw [harts]
    cases hp with
    | keep x _ =>
      refine ⟨by simp [Action.takes], fun n hn => ?_⟩
      simp only [Action.gives, Option.some.injEq] at hn
      subst hn
      refine lookup_none_of_name img (.tail _) (by simp [Name.valid, hnext0]) fun hm => ?_
      have := lt_nextSeq_name (commitsOf rest) (img.filterMap (parseName ·.1)) (.tail _) hm _ rfl
      omega
    | syncDir => simp [Action.takes, Action.gives]
    | cut x _ => simp [Action.takes, Action.gives]
    | removeTemp s _ =>
      refine ⟨fun n hn => ?_, by simp [Action.gives]⟩
      simp only [Action.takes, Option.some.injEq] at hn
      exact Or.inl ⟨s, hn.symm⟩
    | removeFinal s _ hr' =>
      refine ⟨fun n hn => ?_, by simp [Action.gives]⟩
      simp only [Action.takes, Option.some.injEq] at hn
      subst hn
      exact Or.inr ⟨s, rfl, hr'⟩
    | setAside s hs hr' hq =>
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · simp only [Action.takes, Option.some.injEq] at hn
        subst hn
        exact Or.inr ⟨s, rfl, hr'⟩
      · simp only [Action.gives, Option.some.injEq] at hn
        subst hn
        obtain ⟨q, _, hq'⟩ := (mem_names img _).mp hs
        have hv := parseName_valid _ _ hq'
        exact lookup_none_of_name img (.quarantine s) (by simpa [Name.valid] using hv) hq

/-- **Recovery changes the journal only by cutting it where its torn tail starts, or by making
again a journal that holds no record**, or creating one in an empty directory. -/
theorem recover_journal (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) (a : Action) (ha : a ∈ ops) :
    (∀ x, a = .cut x →
      ∃ content, img.lookup journalName = some content ∧ (scan content).ending = .torn x) ∧
    (∀ k, a = .create k → k = cfg.key ∧ st = fresh cfg ∧
      ∀ content, img.lookup journalName = some content → (scan content).records = []) := by
  obtain ⟨_, _, hc⟩ := recover_cases cfg img st ops h
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨content, hj, ⟨hrs, _, _, rfl, rfl⟩ | ⟨key, rest, _, _, hr⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨by simp, fun k hk => by simp at hk; exact ⟨hk.symm, rfl, by simp⟩⟩
    · simp
  · simp only [List.mem_singleton] at ha
    subst ha
    refine ⟨by simp, fun k hk => ?_⟩
    simp only [Action.create.injEq] at hk
    refine ⟨hk.symm, rfl, fun c hc => ?_⟩
    rw [hj] at hc
    cases hc
    exact hrs
  · have hp := recoverRecords_planned _ _ _ _ _ _ _ _ _ hr a ha
    refine ⟨fun x hx => ?_, fun k hk => ?_⟩
    · subst hx
      cases hp with
      | cut _ hcut =>
        refine ⟨content, hj, ?_⟩
        generalize hs : scan content = sc at hcut
        rcases sc with ⟨rs, ending⟩
        cases ending <;> simp_all [cutOf]
    · subst hk
      cases hp

theorem tidy_no_cut (recorded : List Bytes) (names : List Name) (torn : Bool) (x : Nat) :
    Action.cut x ∉ names.filterMap (tidyName recorded names torn) := by
  intro hm
  simp only [List.mem_filterMap] at hm
  obtain ⟨n, _, hn⟩ := hm
  cases n with
  | temp s => simp [tidyName] at hn
  | final s =>
    simp only [tidyName] at hn
    split at hn
    · simp at hn
    · split at hn <;> simp at hn
  | journal => simp [tidyName] at hn
  | quarantine s => simp [tidyName] at hn
  | tail s => simp [tidyName] at hn

/-- **Recovery takes no file before the torn tail is cut and the cut synced**: every action before
the cut takes no file, so a record a crash brings back from a tail whose cut is not yet durable
still has its file. -/
theorem recover_order (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) (x : Nat) (hx : Action.cut x ∈ ops) :
    ∃ pre post, ops = pre ++ .cut x :: post ∧ ∀ a ∈ pre, a.takes = none := by
  obtain ⟨_, _, hc⟩ := recover_cases cfg img st ops h
  rcases hc with ⟨_, _, rfl⟩ | ⟨content, _, ⟨_, _, _, _, rfl⟩ | ⟨key, rest, _, _, hr⟩⟩
  · simp at hx
  · simp at hx
  · have hops := recoverRecords_ops _ _ _ _ _ _ _ _ _ hr
    generalize cutOf (scan content).ending = cut at hops
    cases cut with
    | none =>
      rw [hops] at hx
      simp only [List.nil_append, List.mem_append] at hx
      rcases hx with hx | hx
      · exact absurd hx (tidy_no_cut _ _ _ x)
      · split at hx <;> simp at hx
    | some y =>
      have hxy : x = y := by
        rw [hops] at hx
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with ((hx | hx | hx) | hx) | hx
        · simp at hx
        · simp at hx
        · simpa using hx
        · exact absurd hx (tidy_no_cut _ _ _ x)
        · split at hx <;> simp at hx
      subst hxy
      rw [hops]
      exact ⟨[_, _], _, rfl, by simp [Action.takes]⟩

/-- **A final file no record names is removed only when no cut tail can have held its record**:
when it is set aside already, or when the journal ended cleanly and no tail kept is numbered above
it. -/
theorem recover_removes (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) (n : Bytes) (hn : Action.remove n ∈ ops) :
    (∃ s, n = tempName s) ∨
      ∃ s, n = finalName s ∧ ((∃ q ∈ img, parseName q.1 = some (.quarantine s)) ∨
        ((∀ x, Action.cut x ∉ ops) ∧
          ∀ m, (∃ q ∈ img, parseName q.1 = some (.tail m)) → m ≤ s)) := by
  obtain ⟨_, _, hc⟩ := recover_cases cfg img st ops h
  rcases hc with ⟨_, _, rfl⟩ | ⟨content, _, ⟨_, _, _, _, rfl⟩ | ⟨key, rest, _, _, hr⟩⟩
  · simp at hn
  · simp at hn
  · have hp := recoverRecords_planned _ _ _ _ _ _ _ _ _ hr
    cases hp _ hn with
    | removeTemp s _ => exact Or.inl ⟨s, rfl⟩
    | removeFinal s _ _ hq =>
      refine Or.inr ⟨s, rfl, ?_⟩
      rcases hq with hq | hq
      · exact Or.inl ((mem_names img _).mp hq)
      · simp only [setsAside, Bool.or_eq_false_iff, List.any_eq_false] at hq
        obtain ⟨hcut, htail⟩ := hq
        refine Or.inr ⟨fun x hx => ?_, fun m hm => ?_⟩
        · cases hp _ hx with
          | cut y hy => rw [hy] at hcut; simp at hcut
        · have := htail (.tail m) ((mem_names img _).mpr hm)
          simp only [decide_eq_true_eq] at this
          omega

theorem apply_planned_journal (content : Bytes) (cs : List Commit) (names : List Name)
    (cut : Option Nat) (next0 : Nat) (J : Image) (a : Action)
    (hp : Planned content cs names cut next0 a) (hc : ∀ y, a ≠ .cut y) :
    (apply J a).lookup journalName = J.lookup journalName := by
  cases hp with
  | keep x _ => rw [apply, lookup_setName, if_neg (Ne.symm (tail_ne_journal _))]
  | syncDir => rfl
  | cut x _ => exact absurd rfl (hc x)
  | removeTemp s _ => rw [apply, lookup_dropName, if_neg (Ne.symm (temp_ne_journal _))]
  | removeFinal s _ _ _ => rw [apply, lookup_dropName, if_neg (Ne.symm (final_ne_journal _))]
  | setAside s _ _ _ _ =>
    simp only [apply]
    split
    · rw [lookup_setName, if_neg (Ne.symm (quarantine_ne_journal _)), lookup_dropName,
        if_neg (Ne.symm (final_ne_journal _))]
    · rfl

theorem applyAll_planned_journal (content : Bytes) (cs : List Commit) (names : List Name)
    (cut : Option Nat) (next0 : Nat) :
    ∀ (ops : List Action) (J : Image), (∀ a ∈ ops, Planned content cs names cut next0 a) →
      (∀ y, Action.cut y ∉ ops) → (applyAll J ops).lookup journalName = J.lookup journalName
  | [], _, _, _ => rfl
  | a :: ops, J, hp, hc => by
    simp only [applyAll, List.foldl_cons] at *
    rw [show ops.foldl apply (apply J a) = applyAll (apply J a) ops from rfl,
      applyAll_planned_journal content cs names cut next0 ops (apply J a)
        (fun b hb => hp b (List.mem_cons_of_mem _ hb))
        (fun y hy => hc y (List.mem_cons_of_mem _ hy))]
    exact apply_planned_journal content cs names cut next0 J a (hp a (List.mem_cons_self ..))
      (fun y e => hc y (e ▸ List.mem_cons_self ..))

theorem applyAll_planned_cut (content : Bytes) (cs : List Commit) (names : List Name)
    (next0 x : Nat) :
    ∀ (ops : List Action) (J : Image) (c : Bytes),
      (∀ a ∈ ops, Planned content cs names (some x) next0 a) → J.lookup journalName = some c →
      (applyAll J ops).lookup journalName = some (if Action.cut x ∈ ops then c.take x else c)
  | [], _, c, _, hj => by simpa [applyAll] using hj
  | a :: ops, J, c, hp, hj => by
    simp only [applyAll, List.foldl_cons]
    rw [show ops.foldl apply (apply J a) = applyAll (apply J a) ops from rfl]
    by_cases ha : a = .cut x
    · subst ha
      have hj' : (apply J (.cut x)).lookup journalName = some (c.take x) := by
        rw [lookup_cut, if_pos rfl, hj]; rfl
      rw [applyAll_planned_cut content cs names next0 x ops _ _
        (fun b hb => hp b (List.mem_cons_of_mem _ hb)) hj']
      simp [List.take_take]
    · have hj' : (apply J a).lookup journalName = some c := by
        rw [apply_planned_journal content cs names (some x) next0 J a (hp a (List.mem_cons_self ..))
          (fun y e => by
            subst e
            cases hp (.cut y) (List.mem_cons_self ..) with
            | cut _ hy => simp only [Option.some.injEq] at hy; exact ha (by rw [hy])), hj]
      rw [applyAll_planned_cut content cs names next0 x ops _ _
        (fun b hb => hp b (List.mem_cons_of_mem _ hb)) hj']
      have hne : ¬ Action.cut x = a := fun e => ha e.symm
      simp only [List.mem_cons, hne, false_or]

/-- **Once recovery's actions are done, the journal ends where the store puts its next record.** -/
theorem recover_journalEnd (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) :
    ∃ j, (applyAll img ops).lookup journalName = some j ∧ j.length = st.journalEnd := by
  obtain ⟨hkey, _, hc⟩ := recover_cases cfg img st ops h
  have hf : ((Record.format cfg.key).encode cfg.key 0).length = (fresh cfg).journalEnd := by
    rw [format_encode_length cfg.key hkey 0]; rfl
  rcases hc with ⟨rfl, rfl, rfl⟩ |
    ⟨content, hj, ⟨_, _, hlen, rfl, rfl⟩ | ⟨key, rest, hrs, hcor, hr⟩⟩
  · refine ⟨_, ?_, hf⟩
    simp only [applyAll, List.foldl_cons, List.foldl_nil, apply]
    rw [lookup_setName, if_pos rfl]
  · refine ⟨_, ?_, hf⟩
    simp only [applyAll, List.foldl_cons, List.foldl_nil, apply]
    rw [lookup_setName, if_pos rfl]
  · obtain ⟨_, _, _, _, _, _, _, _, hend⟩ := recoverRecords_ok _ _ _ _ _ _ _ _ _ hr
    have hops := recoverRecords_ops _ _ _ _ _ _ _ _ _ hr
    have hplan := recoverRecords_planned _ _ _ _ _ _ _ _ _ hr
    generalize hs : scan content = sc at hend hops hplan hcor
    rcases sc with ⟨rs, ending⟩
    cases ending with
    | corrupt y w => exact absurd rfl (hcor y w)
    | clean =>
      refine ⟨content, ?_, by rw [hend]; rfl⟩
      rw [applyAll_planned_journal content _ _ _ _ ops img hplan (fun y hy => by
        cases hplan _ hy with
        | cut _ hc => simp [cutOf] at hc), hj]
    | torn x =>
      have hin : Action.cut x ∈ ops := by rw [hops]; simp [cutOf]
      refine ⟨content.take x, ?_, ?_⟩
      · rw [applyAll_planned_cut content _ _ _ x ops img content hplan hj, if_pos hin]
      · rw [hend]
        simp only [cutOf, Option.getD_some, List.length_take]
        have := scan_torn_le content rs x hs
        omega

/-- **The next sequence number is above every number a record or a name in the directory carries**,
so it is never one a file may hold. -/
theorem recover_next (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) :
    (∀ c ∈ st.articles, c.seq < st.next) ∧
      ∀ q ∈ img, ∀ n s, parseName q.1 = some n → seqOf n = some s → s < st.next := by
  obtain ⟨_, _, hc⟩ := recover_cases cfg img st ops h
  rcases hc with ⟨rfl, rfl, _⟩ | ⟨content, hj, ⟨_, _, hlen, rfl, _⟩ | ⟨key, rest, _, _, hr⟩⟩
  · exact ⟨by simp [fresh], by simp⟩
  · refine ⟨by simp [fresh], fun q hq n s hn hs => ?_⟩
    match img, hlen, hq with
    | [(m, o)], _, hq =>
      simp only [List.mem_singleton] at hq
      subst hq
      simp only [List.lookup_cons] at hj
      split at hj
      · rename_i hm
        simp only [beq_iff_eq] at hm
        subst hm
        simp only at hn
        rw [parse_journal] at hn
        cases hn
        simp [seqOf] at hs
      · simp at hj
  · obtain ⟨_, _, _, _, _, harts, hnext, _, _⟩ := recoverRecords_ok _ _ _ _ _ _ _ _ _ hr
    have hat : nextSeq (commitsOf rest) (img.filterMap (parseName ·.1)) ≤ st.next := by
      split at hnext <;> omega
    refine ⟨fun c hc => ?_, fun q hq n s hn hs => ?_⟩
    · rw [harts] at hc
      have := lt_nextSeq_commit _ (img.filterMap (parseName ·.1)) c hc
      omega
    · have := lt_nextSeq_name (commitsOf rest) _ n ((mem_names img n).mpr ⟨q, hq, hn⟩) s hs
      omega

/-! ## The premises can hold -/

/-- The premise `Left` can hold: of a file renamed under both its names. -/
theorem left_witness :
    Left [(finalName 4, [1])] (.rename (finalName 4) (quarantineName 4))
      (setName [(finalName 4, [1])] (quarantineName 4) [1]) :=
  .both _ _ _ _ (by simp)

/-- The premise `Partly` can hold: of that rename. -/
theorem partly_witness :
    Partly [(finalName 4, [1])] [.rename (finalName 4) (quarantineName 4)]
      (setName [(finalName 4, [1])] (quarantineName 4) [1]) :=
  .cons _ _ _ _ _ left_witness (.nil _)

/-- The premise `Planned` can hold: of a temporary file removed. -/
theorem planned_witness : Planned [] [] [.temp 3] none 0 (.remove (tempName 3)) :=
  .removeTemp 3 (by simp)

/-- The premise `Keeps` can hold: of a journal and an article's file. -/
theorem keeps_witness :
    Keeps [(journalName, []), (finalName 1, [0])] [] [] none 1
      [(journalName, []), (finalName 1, [0])] := by
  refine ⟨fun q hq => ?_, Or.inl (by simp), fun c hc => by simp at hc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨.journal, parse_journal, fun s hs => by simp [seqOf] at hs⟩
  · exact ⟨.final 1, parseName_bytes (.final 1) (by decide),
      fun s hs => by simp only [seqOf, Option.some.injEq] at hs; omega⟩

/-! ## Examples -/

/-- Every list of some of a list's members, in their order. -/
def subs {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => (subs l).flatMap fun s => [s, a :: s]

def cfgOf (groups : List String) : Config := ⟨groups.map ascii, sampleKey⟩

/-- A commit of the sample's shape: its sequence number, its group's article number, the size of
its file. -/
def commitOf (seq number size : Nat) : Commit :=
  ⟨seq, ascii "<a@b.example>" ++ [BitVec.ofNat 8 seq], [⟨ascii "local.test", number⟩], 0, size,
    0⟩

/-- A journal of two commits, the files they name, a temporary file and a final file no record
names. -/
def sampleImage (tail : Bytes) : Image :=
  [(journalName, journal sampleKey [.start, .commit (commitOf 1 1 3), .commit (commitOf 2 2 4)] ++
      tail),
    (finalName 1, List.replicate 3 0), (finalName 2, List.replicate 4 0), (tempName 3, []),
    (finalName 4, [1])]

def articlesOf (r : Except Fault (Store × List Action)) : Option (List Commit) :=
  match r with
  | .ok (st, _) => some st.articles
  | .error _ => none

def actionsOf (r : Except Fault (Store × List Action)) : Option (List Action) :=
  match r with
  | .ok (_, ops) => some ops
  | .error _ => none

/-- An empty directory gets a journal, and recovering again finds nothing to do. -/
def regression_903 : Bool :=
  let cfg := cfgOf ["local.test"]
  actionsOf (recover cfg []) == some [.create sampleKey, .syncDir] &&
    actionsOf (recover cfg (applyAll [] [.create sampleKey, .syncDir])) == some []

/-- A journal that ended cleanly: its articles, the temporary file and the final file no record
names removed; recovering again finds nothing to do. -/
def regression_904 : Bool :=
  let cfg := cfgOf ["local.test"]
  let img := sampleImage []
  let r := recover cfg img
  articlesOf r == some [commitOf 1 1 3, commitOf 2 2 4] &&
    actionsOf r == some [.remove (tempName 3), .remove (finalName 4), .syncDir] &&
    actionsOf (recover cfg (applyAll img ((actionsOf r).getD []))) == some []

/-- A torn tail: its octets kept under the next number and the directory synced, the tail cut, and
only then the temporary file removed and the final file no record names set aside; recovering again
finds the same articles and nothing to do. -/
def regression_905 : Bool :=
  let cfg := cfgOf ["local.test"]
  let j := journal sampleKey [.start, .commit (commitOf 1 1 3), .commit (commitOf 2 2 4)]
  let img := sampleImage [7, 7, 7]
  let r := recover cfg img
  let ops := (actionsOf r).getD []
  ops == [.keep (tailName 5) (le 8 j.length ++ [7, 7, 7]), .syncDir, .cut j.length,
      .remove (tempName 3), .rename (finalName 4) (quarantineName 4), .syncDir] &&
    articlesOf (recover cfg (applyAll img ops)) == articlesOf r &&
    actionsOf (recover cfg (applyAll img ops)) == some []

/-- Each corruption 0005 lists keeps the store from starting. -/
def regression_906 : Bool :=
  let cfg := cfgOf ["local.test"]
  let img := sampleImage []
  let fails (img : Image) (f : Fault) : Bool := match recover cfg img with
    | .error g => g == f
    | .ok _ => false
  fails (img ++ [(ascii "lost+found", [])]) (.badName (ascii "lost+found")) &&
    fails (img.filter (·.1 != journalName)) .noJournal &&
    fails (img.filter (·.1 != finalName 2)) (.missingFile 2) &&
    fails ((img.filter (·.1 != finalName 2)) ++ [(finalName 2, [])]) (.wrongSize 2) &&
    fails ((journalName, journal sampleKey [.commit (commitOf 1 1 3), .commit (commitOf 1 2 3)]) ::
      img.filter (·.1 != journalName)) (.seqTwice 1) &&
    fails ((journalName, journal sampleKey [.commit (commitOf 1 2 3), .commit (commitOf 2 2 4)]) ::
      img.filter (·.1 != journalName)) (.numberNotAbove (ascii "local.test") 2) &&
    fails ((journalName,
        (journal sampleKey [.commit (commitOf 1 1 3), .commit (commitOf 2 2 4)]).set 60 0) ::
      img.filter (·.1 != journalName)) (.journal firstFrame .tag) &&
    fails [(journalName, journal sampleKey []), (tempName (2 ^ 64 - 1), [])] .exhausted &&
    (match recover ⟨[ascii "local.test"], [1, 2, 3]⟩ [] with
      | .error .badKey => true
      | _ => false) &&
    match recover (cfgOf ["other"]) img with
    | .error (.unknownGroup _) => true
    | _ => false

/-- A final file no record names is removed if it is set aside already, and set aside, not
removed, while a kept tail shows a record may have been cut, even from a journal that ended
cleanly. -/
def regression_907 : Bool :=
  let cfg := cfgOf ["local.test"]
  (actionsOf (recover cfg (sampleImage [7] ++ [(quarantineName 4, [1])]))).any
      (·.contains (.remove (finalName 4))) &&
    (actionsOf (recover cfg (sampleImage [] ++ [(tailName 9, [])]))).any
      (·.contains (.rename (finalName 4) (quarantineName 4)))

/-- A journal with nothing but a format cut short is made again if nothing else is there, and is
corruption otherwise. -/
def regression_908 : Bool :=
  let cfg := cfgOf ["local.test"]
  let cutShort := ((Record.format sampleKey).encode sampleKey 0).take 9
  actionsOf (recover cfg [(journalName, cutShort)]) == some [.create sampleKey] &&
    actionsOf (recover cfg [(journalName, [])]) == some [.create sampleKey] &&
    (match recover cfg [(journalName, cutShort), (tempName 1, [])] with
      | .error .noJournal => true
      | _ => false)

/-- Every part of recovery's actions, each whole or not at all, recovers the same articles. -/
def regression_909 : Bool :=
  let cfg := cfgOf ["local.test"]
  let img := sampleImage [7, 7, 7]
  let r := recover cfg img
  let ops := (actionsOf r).getD []
  (subs ops).all fun sub => articlesOf (recover cfg (applyAll img sub)) == articlesOf r

def storeOf (r : Except Fault (Store × List Action)) : Option Store :=
  match r with
  | .ok (st, _) => some st
  | .error _ => none

/-- What a store starts with: the files set aside, where the journal ends and the next sequence
number — after a journal that ended cleanly; after a torn tail, whose octets and the final file no
record names are set aside; and with files set aside before, counted again. -/
def regression_910 : Bool :=
  let cfg := cfgOf ["local.test"]
  let j := journal sampleKey [.start, .commit (commitOf 1 1 3), .commit (commitOf 2 2 4)]
  let summary (img : Image) := (storeOf (recover cfg img)).map fun st =>
    (st.setAside, st.journalEnd, st.next)
  summary (sampleImage []) == some ([], j.length, 5) &&
    summary (sampleImage [7, 7, 7]) == some ([4, 5], j.length, 6) &&
    summary (sampleImage [] ++ [(quarantineName 7, [1]), (tailName 6, [])]) ==
      some ([4, 7, 6], j.length, 8)

/-- A final file no record names, from a journal that ended cleanly, is set aside if a tail kept is
numbered above it, and removed if it was made after every tail kept. -/
def regression_911 : Bool :=
  let img := sampleImage [] ++ [(tailName 9, []), (finalName 20, [1])]
  (actionsOf (recover (cfgOf ["local.test"]) img)).any fun ops =>
    ops.contains (.rename (finalName 4) (quarantineName 4)) && ops.contains (.remove (finalName 20))

/-- More articles than the store holds keep it from starting, before the rules across them; as many
as it holds go on to the rules. -/
def regression_912 : Bool :=
  let cs (k : Nat) := List.replicate k (commitOf 1 1 3)
  (match recoverRecords (cfgOf ["local.test"]) [] [] [] sampleKey (cs (capacity + 1)) none with
    | .error (.tooMany n) => n == capacity + 1
    | _ => false) &&
    match recoverRecords (cfgOf ["local.test"]) [] [] [] sampleKey (cs capacity) none with
    | .error (.seqTwice 1) => true
    | _ => false

end DN.News.Recovery
