-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.Spool

/-!
# DN.News.SpoolOps

The host's operations on the spool of `DN.News.Spool`, each with what has to hold before it for the
spool to stay one — the preconditions recovery's plan and the store's POST are to meet, as PoWER
(LeBlanc et al., OSDI 2025) states a store's crash safety: whatever it does, a crash then recovers
as `spool_crash` says.

Proven, each operation keeping a spool: a name removed or a file moved to another name, neither the
journal's nor a placed commit's, the new one of a shape recovery reads (`spool_remove`,
`spool_rename`); a new file under a name, once the journal has its format and its name is settled
(`spool_create`), and the journal created where there is none (`spool_create_journal`); the
directory synced, and a sync of it that failed (`spool_syncDir`, `spool_untrustDir`); an operation
on a file that is not the journal's — an append, a cut or a sync is one — when the files of the
commits stay placed, as they do through a sync, a failed sync, or an operation on another file
(`spool_file`, `placed_settled`, `placed_other`); an operation on the journal's file that leaves it
in a phase whose rules the spool keeps (`spool_journal`); opening, reading, a size and the list of
names, which change nothing (`step_pure`); every failure an operation may have (`failures_cases`,
`spool_whole`, `spool_file_untrust`, `spool_journal_untrust`, `spool_untrustDir`); and what the
store learns: the octets a POST writes, a commit appended, an article answered once its commit is
kept, a journal read cleanly after a crash (`spool_files`, `spool_appended`, `spool_answer`,
`spool_found_clean`). A file synced under a commit's final name is placed once the directory is
synced (`placed_syncDir`), and a file just created is neither the journal's nor a placed commit's
(`fresh_apart`). Under them, a change keeps a spool when it keeps what the spool asks of the
journal, the other names and the placed files (`spool_frame`).
-/

namespace DN.News.SpoolOps

open DN.News.Journal
open DN.News.FsModel (Data Entry Fs Ino rebind)
open DN.News.Recovery
open DN.News.JournalCrash
open DN.News.Spool
open DN.News.CommandSpec (ascii)

/-! ## What an operation has to keep -/

/-- The commits whose files are in place in a spool. -/
def placedSet (v : View) : List Commit := commitsOf (v.phase.kept ++ v.phase.back)

/-- **A spool stays one** through a change that keeps its names of a shape recovery reads, the
journal's name holding what it held and its file, no other name taking that file, no other file
while there should be none, and the files of its commits in place. -/
theorem spool_frame (cfg : Config) (s s' : Fs) (v : View) (h : Spool cfg s v) (hok : s'.Ok)
    (hnames : ∀ e ∈ s'.dir, ∃ n, parseName e.name = some n ∧ ∀ q, seqOf n = some q → q < v.next)
    (hempty : v.phase = .none → ∀ e ∈ s'.dir, ∀ i, ¬ e.Leaves (some i))
    (hjl : s'.lookup journalName = s.lookup journalName)
    (hjleaves : ∀ e', s'.entry journalName = some e' →
      ∃ e, s.entry journalName = some e ∧ ∀ b, e'.Leaves b → e.Leaves b)
    (hjunset : Unsettled s' → Unsettled s)
    (hjdata : ∀ i, s.lookup journalName = some i → s'.data i = s.data i)
    (hapart : ∀ i, s.lookup journalName = some i → Apart s i → Apart s' i)
    (halone : v.phase = .creating ∨ v.phase = .unformatted ∨ Unsettled s → Alone s')
    (hplaced : ∀ c ∈ placedSet v, Placed s v.files c → Placed s' v.files c) :
    Spool cfg s' v := by
  refine ⟨hok, hnames, h.room, hempty, fun hne => ?_, fun hor => halone ?_,
    fun hu => h.quiet (hjunset hu), fun c hc => hplaced c hc (h.placed c hc), h.rules, h.seqs,
    h.answered, h.appended⟩
  · obtain ⟨e, ij, d, he, hl, hb, hd, hholds, hap⟩ := h.journal hne
    obtain ⟨e', he'⟩ : ∃ e', s'.entry journalName = some e' := by
      have : s'.lookup journalName = some ij := by rw [hjl]; exact hl
      simp only [Fs.lookup, Option.bind_eq_some_iff] at this
      obtain ⟨e', he', _⟩ := this
      exact ⟨e', he'⟩
    obtain ⟨e₀, he₀, hsub⟩ := hjleaves e' he'
    rw [he] at he₀
    cases he₀
    exact ⟨e', ij, d, he', by rw [hjl]; exact hl, fun b hb' => hb b (hsub b hb'),
      by rw [hjdata ij hl]; exact hd, hholds, hapart ij hl hap⟩
  · rcases hor with hor | hor | hor
    · exact Or.inl hor
    · exact Or.inr (Or.inl hor)
    · exact Or.inr (Or.inr (hjunset hor))

/-! ## Names -/

/-- A name of the directory after a rebind is the name rebound, or one it had. -/
theorem rebind_names (dir : List Entry) (name : Bytes) (b : Option Ino) (e' : Entry)
    (he : e' ∈ rebind dir name b) : e'.name = name ∨ ∃ e ∈ dir, e.name = e'.name := by
  unfold rebind at he
  split at he
  · obtain ⟨e, hm, rfl⟩ := List.mem_map.mp he
    by_cases hn : e.name = name
    · left; simp [hn]
    · right; exact ⟨e, hm, by simp [hn]⟩
  · rcases List.mem_append.mp he with he | he
    · exact Or.inr ⟨e', he, rfl⟩
    · simp only [List.mem_singleton] at he; subst he; exact Or.inl rfl

/-- What a name may be left holding after a rebind: what it is rebound to, or what a name of the
same shape could be left holding before. -/
theorem rebind_leaves (dir : List Entry) (name : Bytes) (b : Option Ino) (e' : Entry)
    (he : e' ∈ rebind dir name b) (i : Ino) (hl : e'.Leaves (some i)) :
    e'.name = name ∧ some i = b ∨ ∃ e ∈ dir, e.name = e'.name ∧ e.Leaves (some i) := by
  unfold rebind at he
  split at he
  · obtain ⟨e, hm, rfl⟩ := List.mem_map.mp he
    by_cases hn : e.name = name
    · have hb : (e.name == name) = true := by simp [hn]
      simp only [hb, ↓reduceIte, Entry.Leaves, List.mem_cons] at hl
      rcases hl with hl | hl | hl
      · exact Or.inr ⟨e, hm, by simp [hb], Or.inl hl⟩
      · exact Or.inl ⟨by simp [hn], hl⟩
      · exact Or.inr ⟨e, hm, by simp [hb], Or.inr hl⟩
    · have hb : (e.name == name) = false := by simp [hn]
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hl ⊢
      exact Or.inr ⟨e, hm, rfl, hl⟩
  · rcases List.mem_append.mp he with he | he
    · exact Or.inr ⟨e', he, rfl, hl⟩
    · simp only [List.mem_singleton] at he
      subst he
      simp only [Entry.Leaves, List.mem_singleton] at hl
      rcases hl with hl | hl
      · cases hl
      · exact Or.inl ⟨rfl, hl⟩

/-- The names of a spool after a rebind of a name of a shape recovery reads, numbered below the
bound. -/
theorem names_rebind_spool (dir : List Entry) (name : Bytes) (b : Option Ino) (bound : Nat)
    (hdir : ∀ e ∈ dir, ∃ n, parseName e.name = some n ∧ ∀ q, seqOf n = some q → q < bound)
    (hname : ∃ n, parseName name = some n ∧ ∀ q, seqOf n = some q → q < bound) :
    ∀ e ∈ rebind dir name b,
      ∃ n, parseName e.name = some n ∧ ∀ q, seqOf n = some q → q < bound := by
  intro e' he
  rcases rebind_names dir name b e' he with hn | ⟨e, hm, hn⟩
  · rw [hn]; exact hname
  · rw [← hn]; exact hdir e hm

theorem entry_other (s : Fs) (name m : Bytes) (b : Option Ino) (hm : m ≠ name) :
    ({ s with dir := rebind s.dir name b } : Fs).entry m = s.entry m := by
  simp only [Fs.entry, FsModel.entry_rebind, if_neg hm]

theorem lookup_other (s : Fs) (name m : Bytes) (b : Option Ino) (hm : m ≠ name) :
    ({ s with dir := rebind s.dir name b } : Fs).lookup m = s.lookup m := by
  simp only [Fs.lookup, entry_other s name m b hm]

/-- A placed file stays placed when another name is rebound and no file changes. -/
theorem placed_rebind (s : Fs) (files : Nat → Bytes) (c : Commit) (name : Bytes) (b : Option Ino)
    (hn : finalName c.seq ≠ name) (hp : Placed s files c) :
    Placed { s with dir := rebind s.dir name b } files c := by
  obtain ⟨e, i, d, he, hset, hsyn, hd, hk, hh, hseen, hlen, hcrc⟩ := hp
  exact ⟨e, i, d, by rw [entry_other s name _ b hn]; exact he, hset, hsyn, hd, hk, hh, hseen, hlen,
    hcrc⟩

/-- **A name removed** that is not the journal's nor holds the file of a commit placed. -/
theorem spool_remove (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (name : Bytes)
    (hj : name ≠ journalName) (hp : ∀ c ∈ placedSet v, finalName c.seq ≠ name) :
    Spool cfg (s.step (.remove name)).1 v := by
  simp only [Fs.step]
  split
  · have hok := FsModel.step_ok s h.ok (.remove name)
    simp only [Fs.step] at hok
    rename_i hl
    rw [hl] at hok
    refine spool_frame cfg s _ v h hok
      (names_rebind_spool _ _ _ _ h.names (by
        obtain ⟨e, he, _⟩ : ∃ e, s.entry name = some e ∧ _ := by
          simp only [Fs.lookup, Option.bind_eq_some_iff] at hl; exact hl
        have := List.find?_some he
        simp only [beq_iff_eq] at this
        rw [← this]; exact h.names e (List.mem_of_find?_eq_some he)))
      (fun hph e he i hl' => ?_) (lookup_other s name _ none hj.symm)
      (fun e' he' => ⟨e', by rw [← entry_other s name _ none hj.symm]; exact he', fun _ h => h⟩)
      (fun hu e he hset => hu e (by rw [entry_other s name _ none hj.symm]; exact he) hset)
      (fun _ _ => rfl) (fun i _ hap e he hn hl' => ?_) (fun hor e he hn i hl' => ?_)
      (fun c hc hpl => placed_rebind s v.files c name none (hp c hc) hpl)
    · rcases rebind_leaves _ _ _ e he i hl' with ⟨_, hb⟩ | ⟨e₀, he₀, _, hl₀⟩
      · cases hb
      · exact h.empty hph e₀ he₀ i hl₀
    · rcases rebind_leaves _ _ _ e he i hl' with ⟨_, hb⟩ | ⟨e₀, he₀, hn₀, hl₀⟩
      · cases hb
      · exact hap e₀ he₀ (by rw [hn₀]; exact hn) hl₀
    · rcases rebind_leaves _ _ _ e he i hl' with ⟨_, hb⟩ | ⟨e₀, he₀, hn₀, hl₀⟩
      · cases hb
      · exact h.alone hor e₀ he₀ (by rw [hn₀]; exact hn) i hl₀
  · exact h

/-- A name holding a file can be left holding it. -/
theorem lookup_leaves (s : Fs) (name : Bytes) (i : Ino) (hl : s.lookup name = some i) :
    ∃ e, s.entry name = some e ∧ e.Leaves (some i) := by
  simp only [Fs.lookup, Option.bind_eq_some_iff] at hl
  obtain ⟨e, he, hs⟩ := hl
  exact ⟨e, he, hs ▸ FsModel.entry_leaves_seen e⟩

theorem entry_name (s : Fs) (name : Bytes) (e : Entry) (he : s.entry name = some e) :
    e.name = name := by
  have := List.find?_some he
  simpa using this

/-- **A file moved to another name**, neither the journal's nor holding the file of a commit placed,
the new one of a shape recovery reads and numbered below the bound. -/
theorem spool_rename (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (src dst : Bytes)
    (hsj : src ≠ journalName) (hdj : dst ≠ journalName)
    (hps : ∀ c ∈ placedSet v, finalName c.seq ≠ src)
    (hpd : ∀ c ∈ placedSet v, finalName c.seq ≠ dst)
    (hdn : ∃ n, parseName dst = some n ∧ ∀ q, seqOf n = some q → q < v.next) :
    Spool cfg (s.step (.rename src dst)).1 v := by
  have hok := FsModel.step_ok s h.ok (.rename src dst)
  simp only [Fs.step] at hok ⊢
  split
  · rename_i i hl
    split
    · exact h
    · rename_i hne
      rw [hl] at hok
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hok
      obtain ⟨es, hes, hles⟩ := lookup_leaves s src i hl
      have hesn := entry_name s src es hes
      have hesm := List.mem_of_find?_eq_some hes
      -- no name could hold the file moved while the journal had no format or its name was loose
      have hnot : ¬ (v.phase = .creating ∨ v.phase = .unformatted ∨ Unsettled s) := fun hor =>
        h.alone hor es hesm (by rw [hesn]; exact hsj) i hles
      have hnone : v.phase ≠ .none := fun hn => h.empty hn es hesm i hles
      let s₁ : Fs := { s with dir := rebind s.dir dst (some i) }
      have hent : ∀ m, m ≠ src → m ≠ dst →
          ({ s₁ with dir := rebind s₁.dir src none } : Fs).entry m = s.entry m := by
        intro m h1 h2
        rw [entry_other s₁ src m none h1, entry_other s dst m _ h2]
      have hleaves : ∀ e ∈ rebind (rebind s.dir dst (some i)) src none, ∀ j, e.Leaves (some j) →
          j = i ∨ ∃ e₀ ∈ s.dir, e₀.name = e.name ∧ e₀.Leaves (some j) := by
        intro e he j hl'
        rcases rebind_leaves _ _ _ e he j hl' with ⟨_, hb⟩ | ⟨e₁, he₁, hn₁, hl₁⟩
        · cases hb
        · rcases rebind_leaves _ _ _ e₁ he₁ j hl₁ with ⟨_, hb⟩ | ⟨e₀, he₀, hn₀, hl₀⟩
          · exact Or.inl (Option.some.inj hb)
          · exact Or.inr ⟨e₀, he₀, by rw [hn₀, hn₁], hl₀⟩
      refine spool_frame cfg s _ v h hok ?_ (fun hn => absurd hn hnone)
        (by simp only [Fs.lookup]; rw [hent _ hsj.symm hdj.symm])
        (fun e' he' => ⟨e', by rw [← hent _ hsj.symm hdj.symm]; exact he', fun _ h => h⟩)
        (fun hu e he hset => hu e (by rw [hent _ hsj.symm hdj.symm]; exact he) hset)
        (fun _ _ => rfl) (fun j _ hap e he hn hl' => ?_) (fun hor => absurd hor hnot)
        (fun c hc hpl => ?_)
      · exact names_rebind_spool _ _ _ _ (names_rebind_spool _ _ _ _ h.names hdn)
          (by rw [← hesn]; exact h.names es hesm)
      · rcases hleaves e he j hl' with rfl | ⟨e₀, he₀, hn₀, hl₀⟩
        · exact hap es hesm (by rw [hesn]; exact hsj) hles
        · exact hap e₀ he₀ (by rw [hn₀]; exact hn) hl₀
      · exact placed_rebind s₁ v.files c src none (hps c hc)
          (placed_rebind s v.files c dst (some i) (hpd c hc) hpl)
  · exact h

theorem find_settle (name : Bytes) : ∀ es : List Entry, (es.map Entry.name).Nodup →
    (es.filterMap Entry.settle).find? (·.name == name) =
      (es.find? (·.name == name)).bind Entry.settle
  | [], _ => rfl
  | e :: es, hn => by
    simp only [List.map_cons, List.nodup_cons] at hn
    have ih := find_settle name es hn.2
    simp only [List.filterMap_cons, List.find?_cons]
    cases hse : Entry.settle e with
    | none =>
      simp only
      rw [ih]
      by_cases hname : e.name = name
      · subst hname
        have hnone : es.find? (·.name == e.name) = none := by
          rw [List.find?_eq_none]
          intro x hx hb
          simp only [beq_iff_eq] at hb
          exact hn.1 (hb ▸ List.mem_map_of_mem hx)
        simp [hnone, hse]
      · have hb : (e.name == name) = false := by simp [hname]
        simp [hb]
    | some e' =>
      have hn' : e'.name = e.name := by
        simp only [Entry.settle, Option.map_eq_some_iff] at hse
        obtain ⟨_, _, rfl⟩ := hse; rfl
      by_cases hname : e.name = name
      · have hb : (e'.name == name) = true := by simp [hn', hname]
        have hb' : (e.name == name) = true := by simp [hname]
        simp [hb, hb', hse]
      · have hb : (e'.name == name) = false := by simp [hn', hname]
        have hb' : (e.name == name) = false := by simp [hname]
        rw [List.find?_cons, hb]
        simp only [hb']
        exact ih

/-- The entry a sync of the directory leaves under a name: the name's, settled. -/
theorem entry_settle (s : Fs) (hs : s.Ok) (name : Bytes) :
    (s.dir.filterMap Entry.settle).find? (·.name == name) = (s.entry name).bind Entry.settle :=
  find_settle name s.dir hs.1

/-- **The directory synced.** -/
theorem spool_syncDir (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) :
    Spool cfg (s.step .syncDir).1 v := by
  have hok := FsModel.step_ok s h.ok .syncDir
  simp only [Fs.step] at hok ⊢
  split
  · rename_i ht
    simp only [ht, ↓reduceIte] at hok
    have hent : ∀ name, ({ s with dir := s.dir.filterMap Entry.settle } : Fs).entry name =
        (s.entry name).bind Entry.settle := fun name => entry_settle s h.ok name
    have hmem : ∀ e' ∈ s.dir.filterMap Entry.settle, ∃ e ∈ s.dir, e.name = e'.name ∧
        e'.Leaves = (· = e.seen) ∧ e.seen.isSome := by
      intro e' he'
      obtain ⟨e, he, hse⟩ := List.mem_filterMap.mp he'
      simp only [Entry.settle, Option.map_eq_some_iff] at hse
      obtain ⟨i, hi, rfl⟩ := hse
      refine ⟨e, he, rfl, ?_, by simp [hi]⟩
      funext b
      simp [Entry.Leaves, hi]
    have hlk : ∀ name, ({ s with dir := s.dir.filterMap Entry.settle } : Fs).lookup name =
        s.lookup name := by
      intro name
      simp only [Fs.lookup, hent]
      cases s.entry name with
      | none => rfl
      | some e =>
        simp only [Option.bind_some, Entry.settle]
        cases e.seen <;> rfl
    have hsettled : ∀ name e, s.entry name = some e → e.Settled →
        ({ s with dir := s.dir.filterMap Entry.settle } : Fs).entry name = some e := by
      intro name e he hset
      rw [hent, he, Option.bind_some]
      obtain ⟨hheld, hsome⟩ := hset
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨name', synced, held⟩ := e
      simp only at hheld hi
      subst hheld hi
      rfl
    refine spool_frame cfg s _ v h hok (fun e' he' => ?_) (fun hph e' he' i hl => ?_) (hlk _)
      (fun e' he' => ?_) (fun hu e he hset => hu e (hsettled _ e he hset) hset) (fun _ _ => rfl)
      (fun i _ hap e' he' hn hl => ?_) (fun hor e' he' hn i hl => ?_) (fun c _ hpl => ?_)
    · obtain ⟨e, he, hn, _⟩ := hmem e' he'
      rw [← hn]; exact h.names e he
    · obtain ⟨e, he, _, hL, _⟩ := hmem e' he'
      rw [hL] at hl
      exact h.empty hph e he i (hl ▸ FsModel.entry_leaves_seen e)
    · rw [hent] at he'
      cases he₀ : s.entry journalName with
      | none => rw [he₀] at he'; cases he'
      | some e =>
        rw [he₀, Option.bind_some] at he'
        refine ⟨e, rfl, fun b hb => ?_⟩
        simp only [Entry.settle, Option.map_eq_some_iff] at he'
        obtain ⟨i, hi, rfl⟩ := he'
        simp only [Entry.Leaves, List.not_mem_nil, or_false] at hb
        rw [hb, ← hi]
        exact FsModel.entry_leaves_seen e
    · obtain ⟨e, he, hn', hL, _⟩ := hmem e' he'
      rw [hL] at hl
      exact hap e he (by rw [hn']; exact hn) (hl ▸ FsModel.entry_leaves_seen e)
    · obtain ⟨e, he, hn', hL, _⟩ := hmem e' he'
      rw [hL] at hl
      exact h.alone hor e he (by rw [hn']; exact hn) i (hl ▸ FsModel.entry_leaves_seen e)
    · obtain ⟨e, i, d, he, hset, hsyn, hd, hk, hh, hseen, hlen, hcrc⟩ := hpl
      exact ⟨e, i, d, hsettled _ e he hset, hset, hsyn, hd, hk, hh, hseen, hlen, hcrc⟩
  · exact h

/-- A sync of the directory that failed: no later one is trusted, and the spool is as it was. -/
theorem spool_untrustDir (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) :
    Spool cfg { s with dirTrusted := false } v :=
  ⟨h.ok, h.names, h.room, h.empty, h.journal, h.alone, h.quiet, h.placed, h.rules, h.seqs,
    h.answered, h.appended⟩

/-- A file there keeps its data when a new one is added. -/
theorem lookup_append_new (ps : List (Ino × Data)) (i k : Ino) (d : Data)
    (hi : ps.lookup i = some d) :
    (ps ++ [(k, Data.empty)]).lookup i = some d := by
  induction ps with
  | nil => cases hi
  | cons p ps ih =>
    obtain ⟨j, dj⟩ := p
    simp only [List.cons_append, List.lookup_cons] at hi ⊢
    split at hi
    · exact hi
    · exact ih hi

theorem lookup_append_fresh (k : Ino) (d : Data) : ∀ ps : List (Ino × Data),
    (∀ p ∈ ps, p.1 ≠ k) → (ps ++ [(k, d)]).lookup k = some d
  | [], _ => by simp
  | (j, dj) :: ps, h => by
    have hj : (k == j) = false := by
      have := h (j, dj) (List.mem_cons_self ..)
      simp only [beq_eq_false_iff_ne]
      exact fun e => this e.symm
    simp only [List.cons_append, List.lookup_cons, hj]
    exact lookup_append_fresh k d ps fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- Every file a name holds is numbered below the next. -/
theorem held_below (s : Fs) (hs : s.Ok) (name : Bytes) (i : Ino) (hl : s.lookup name = some i) :
    i < s.next := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (FsModel.lookup_held s hs name i hl)
  exact hs.2.2.1 p hp

/-- A spool whose journal's name is settled has a journal. -/
theorem phase_some (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (hset : ¬ Unsettled s) :
    v.phase ≠ .none := by
  intro hn
  apply hset
  intro e he hs
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs.2
  exact h.empty hn e (List.mem_of_find?_eq_some he) i (Or.inl hi.symm)

/-- **A new file under a new name**, not the journal's, of a shape recovery reads and numbered
below the bound, once the journal has its format and its name is settled. -/
theorem spool_create (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (name : Bytes)
    (hj : name ≠ journalName)
    (hn : ∃ n, parseName name = some n ∧ ∀ q, seqOf n = some q → q < v.next)
    (hph : v.phase ≠ .creating ∧ v.phase ≠ .unformatted) (hset : ¬ Unsettled s) :
    Spool cfg (s.step (.create name)).1 v := by
  cases hfree : s.lookup name with
  | some i =>
    have : (s.step (.create name)).1 = s := by simp [Fs.step, hfree]
    rw [this]; exact h
  | none =>
  have hok := FsModel.step_ok s h.ok (.create name)
  have hstep : (s.step (.create name)).1 = ⟨rebind s.dir name (some s.next),
      s.files ++ [(s.next, .empty)], s.next + 1, s.dirTrusted⟩ := by
    simp [Fs.step, hfree]
  rw [hstep] at hok ⊢
  have hent : ∀ m, m ≠ name →
      (Fs.mk (rebind s.dir name (some s.next)) (s.files ++ [(s.next, .empty)]) (s.next + 1)
        s.dirTrusted).entry m = s.entry m := fun m hm => entry_other s name m _ hm
  refine spool_frame cfg s _ v h hok (names_rebind_spool _ _ _ _ h.names hn)
    (fun hn' => absurd hn' (phase_some cfg s v h hset))
    (by simp only [Fs.lookup]; rw [hent _ hj.symm])
    (fun e' he' => ⟨e', by rw [← hent _ hj.symm]; exact he', fun _ h => h⟩)
    (fun hu e he hs => hu e (by rw [hent _ hj.symm]; exact he) hs)
    (fun i hl => ?_) (fun i hl hap e he hne hl' => ?_) (fun hor => ?_) (fun c hc hpl => ?_)
  · obtain ⟨d, hd⟩ := data_some s h.ok _ i hl
    show (s.files ++ _).lookup i = s.files.lookup i
    rw [lookup_append_new _ _ _ _ hd]
    exact hd.symm
  · rcases rebind_leaves _ _ _ e he i hl' with ⟨_, hb⟩ | ⟨e₀, he₀, hn₀, hl₀⟩
    · have hlt := held_below s h.ok _ i hl
      rw [Option.some.inj hb] at hlt
      exact Nat.lt_irrefl _ hlt
    · exact hap e₀ he₀ (by rw [hn₀]; exact hne) hl₀
  · rcases hor with hor | hor | hor
    · exact absurd hor hph.1
    · exact absurd hor hph.2
    · exact absurd hor hset
  · obtain ⟨e, i, d, he, hset', hsyn, hd, hk, hh, hseen, hlen, hcrc⟩ := hpl
    have hne : finalName c.seq ≠ name := by
      intro heq
      rw [← heq] at hfree
      simp [Fs.lookup, he, Entry.seen, hset'.1, hsyn] at hfree
    exact ⟨e, i, d, by rw [hent _ hne]; exact he, hset', hsyn,
      lookup_append_new _ _ _ _ hd, hk, hh, hseen, hlen, hcrc⟩

/-- **The journal created** in a spool with no journal: it is being written. -/
theorem spool_create_journal (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v)
    (hph : v.phase = .none) :
    Spool cfg (s.step (.create journalName)).1 { v with phase := .creating } := by
  have hfree : s.lookup journalName = none := by
    cases hl : s.lookup journalName with
    | none => rfl
    | some i =>
      obtain ⟨e, he, hle⟩ := lookup_leaves s _ i hl
      exact absurd hle (h.empty hph e (List.mem_of_find?_eq_some he) i)
  have hok := FsModel.step_ok s h.ok (.create journalName)
  have hstep : (s.step (.create journalName)).1 = ⟨rebind s.dir journalName (some s.next),
      s.files ++ [(s.next, .empty)], s.next + 1, s.dirTrusted⟩ := by
    simp [Fs.step, hfree]
  rw [hstep] at hok ⊢
  have hans : v.answered = [] := by
    cases hv : v.answered with
    | nil => rfl
    | cons c cs =>
      have := h.answered c (by rw [hv]; exact List.mem_cons_self ..)
      rw [hph] at this
      simp [Phase.kept, commitsOf] at this
  have hleaves : ∀ e ∈ rebind s.dir journalName (some s.next), ∀ i, e.Leaves (some i) →
      e.name = journalName ∧ i = s.next := by
    intro e he i hl
    rcases rebind_leaves _ _ _ e he i hl with ⟨hn, hb⟩ | ⟨e₀, he₀, _, hl₀⟩
    · exact ⟨hn, Option.some.inj hb⟩
    · exact absurd hl₀ (h.empty hph e₀ he₀ i)
  have hfresh : ∀ p ∈ s.files, p.1 ≠ s.next := fun p hp heq => by
    have hlt := h.ok.2.2.1 p hp
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  have hdata := lookup_append_fresh s.next Data.empty s.files hfresh
  have hent : (Fs.mk (rebind s.dir journalName (some s.next)) (s.files ++ [(s.next, .empty)])
      (s.next + 1) s.dirTrusted).lookup journalName = some s.next := by
    simp only [Fs.lookup, Fs.entry]
    rw [FsModel.lookup_rebind, if_pos rfl]
  obtain ⟨e, he⟩ : ∃ e, (Fs.mk (rebind s.dir journalName (some s.next))
      (s.files ++ [(s.next, .empty)]) (s.next + 1) s.dirTrusted).entry journalName = some e := by
    simp only [Fs.lookup, Option.bind_eq_some_iff] at hent
    obtain ⟨e, he, _⟩ := hent
    exact ⟨e, he⟩
  have hem := List.mem_of_find?_eq_some he
  have halone : Alone (Fs.mk (rebind s.dir journalName (some s.next))
      (s.files ++ [(s.next, .empty)]) (s.next + 1) s.dirTrusted) :=
    fun e' he' hn i hl => hn (hleaves e' he' i hl).1
  refine ⟨hok, names_rebind_spool _ _ _ _ h.names ⟨.journal, parseName_bytes .journal rfl,
      fun q hq => by simp [seqOf] at hq⟩, h.room, (fun hne => by cases hne),
    fun _ => ⟨e, s.next, Data.empty, he, hent, fun b hb => ?_, hdata,
      ⟨creating_empty, Or.inl rfl⟩, fun e' he' hn hl => hn (hleaves e' he' _ hl).1⟩,
    fun _ => halone, fun _ => hans, fun c hc => by simp [Phase.kept, Phase.back, commitsOf] at hc,
    ⟨rules_nil cfg, fun r hr => by simp [Phase.back] at hr⟩,
    fun c hc => by simp [Phase.kept, Phase.back, commitsOf] at hc, fun c hc => by simp [hans] at hc,
    fun c hc => by simp [Phase.kept, Phase.back, commitsOf] at hc⟩
  cases b with
  | none => exact Or.inl rfl
  | some i => exact Or.inr (by rw [(hleaves e hem i hb).2])

/-! ## Files -/

theorem data_onData (s : Fs) (i j : Ino) (f : Data → Data) :
    (s.onData i f).1.data j = if j = i then (s.data j).map f else s.data j := by
  unfold Fs.onData
  split
  · simp only [Fs.data, lookup_change]
    cases s.files.lookup j with
    | none => split <;> rfl
    | some d => split <;> simp_all
  · rename_i hnone
    split
    · rename_i hji
      subst hji
      simp only [Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at hnone
      simp [hnone]
    · rfl

/-- A placed file stays placed through an operation on another file. -/
theorem placed_other (s : Fs) (files : Nat → Bytes) (c : Commit) (i : Ino) (f : Data → Data)
    (hp : Placed s files c) (hi : ∀ e, s.entry (finalName c.seq) = some e → e.synced ≠ some i) :
    Placed (s.onData i f).1 files c := by
  obtain ⟨e, j, d, he, hset, hsyn, hd, hk, hh, hseen, hlen, hcrc⟩ := hp
  have hji : j ≠ i := fun heq => hi e he (by rw [hsyn, heq])
  have hent := entry_of_dir s _ (FsModel.onData_dir s i f)
  refine ⟨e, j, d, by rw [hent]; exact he, hset, hsyn, ?_, hk, hh, hseen, hlen, hcrc⟩
  rw [data_onData, if_neg hji, hd]

/-- A placed file stays placed through an operation that leaves a file all of whose octets are kept
as it is: a sync, or a sync that failed. -/
theorem placed_settled (s : Fs) (files : Nat → Bytes) (c : Commit) (i : Ino) (f : Data → Data)
    (hf : ∀ d, d.kept = d.seen → d.high = d.seen.length →
      (f d).kept = (f d).seen ∧ (f d).high = (f d).seen.length ∧ (f d).seen = d.seen)
    (hp : Placed s files c) : Placed (s.onData i f).1 files c := by
  obtain ⟨e, j, d, he, hset, hsyn, hd, hk, hh, hseen, hlen, hcrc⟩ := hp
  have hent := entry_of_dir s _ (FsModel.onData_dir s i f)
  by_cases hji : j = i
  · subst hji
    obtain ⟨hk', hh', hs'⟩ := hf d hk hh
    exact ⟨e, j, f d, by rw [hent]; exact he, hset, hsyn, by rw [data_onData, if_pos rfl, hd]; rfl,
      hk', hh', by rw [hs', hseen], hlen, hcrc⟩
  · exact ⟨e, j, d, by rw [hent]; exact he, hset, hsyn, by rw [data_onData, if_neg hji, hd], hk, hh,
      hseen, hlen, hcrc⟩

theorem sync_keeps (d : Data) (hk : d.kept = d.seen) (hh : d.high = d.seen.length) :
    d.sync.kept = d.sync.seen ∧ d.sync.high = d.sync.seen.length ∧ d.sync.seen = d.seen := by
  unfold Data.sync; split <;> simp_all

theorem untrust_keeps (d : Data) (hk : d.kept = d.seen) (hh : d.high = d.seen.length) :
    d.untrust.kept = d.untrust.seen ∧ d.untrust.high = d.untrust.seen.length ∧
      d.untrust.seen = d.seen := ⟨hk, hh, rfl⟩

/-- **An operation on a file that is not the journal's** — an append, a cut and a sync of a file are
each `onData` — keeps a spool when the files of its commits stay placed. -/
theorem spool_file (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (i : Ino)
    (f : Data → Data) (hf : ∀ d, d.Ok → (f d).Ok)
    (hj : s.lookup journalName ≠ some i)
    (hp : ∀ c ∈ placedSet v, Placed s v.files c → Placed (s.onData i f).1 v.files c) :
    Spool cfg (s.onData i f).1 v := by
  have hdir : (s.onData i f).1.dir = s.dir := FsModel.onData_dir s i f
  have hent := entry_of_dir s _ hdir
  have hlk := lookup_of_dir s _ hdir
  refine spool_frame cfg s _ v h (FsModel.onData_ok s h.ok i f hf) (by rw [hdir]; exact h.names)
    (by rw [hdir]; exact h.empty) (by rw [hlk]) (fun e' he' => ⟨e', by rw [← hent]; exact he',
      fun _ h => h⟩) (fun hu e he hs => hu e (by rw [hent]; exact he) hs) (fun ij hl => ?_)
    (fun ij _ hap => by unfold Apart; rw [hdir]; exact hap)
    (fun hor => by unfold Alone; rw [hdir]; exact h.alone hor) hp
  have hne : ij ≠ i := fun heq => hj (by rw [hl, heq])
  rw [data_onData, if_neg hne]

/-- **An operation on the journal's file** that leaves it in a phase whose rules the spool keeps. -/
theorem spool_journal (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (ij : Ino)
    (hl : s.lookup journalName = some ij) (f : Data → Data) (hf : ∀ d, d.Ok → (f d).Ok)
    (ph : Phase) (hholds : ∀ d, s.data ij = some d → ph.Holds (f d))
    (halone : ph = .creating ∨ ph = .unformatted ∨ Unsettled s → Alone s)
    (hplaced : ∀ c ∈ commitsOf (ph.kept ++ ph.back), Placed s v.files c)
    (hrules : Rules cfg (commitsOf ph.kept) ∧ ∀ r ∈ ph.back, Rules cfg (commitsOf (ph.kept ++ [r])))
    (hseqs : ∀ c ∈ commitsOf (ph.kept ++ ph.back), c.seq < v.next)
    (hans : ∀ c ∈ v.answered, c ∈ commitsOf ph.kept)
    (happ : ∀ c ∈ commitsOf (ph.kept ++ ph.back), c ∈ v.appended) :
    Spool cfg (s.onData ij f).1 { v with phase := ph } := by
  have hdir : (s.onData ij f).1.dir = s.dir := FsModel.onData_dir s ij f
  have hent := entry_of_dir s _ hdir
  have hlk := lookup_of_dir s _ hdir
  have hjne : v.phase ≠ .none := by
    intro hn
    obtain ⟨e, he, hle⟩ := lookup_leaves s _ ij hl
    exact h.empty hn e (List.mem_of_find?_eq_some he) ij hle
  obtain ⟨e, ij', d, he, hl', hb, hd, _, hap⟩ := h.journal hjne
  rw [hl] at hl'
  cases hl'
  have hph : ph ≠ .none := fun hn => by
    have := hholds d hd
    rw [hn] at this
    exact this
  refine ⟨FsModel.onData_ok s h.ok ij f hf, by rw [hdir]; exact h.names, h.room,
    fun hn => absurd hn hph, fun _ => ⟨e, ij, f d, by rw [hent]; exact he, by rw [hlk]; exact hl,
      hb, by rw [data_onData, if_pos rfl, hd]; rfl, hholds d hd,
      by unfold Apart; rw [hdir]; exact hap⟩,
    fun hor => ?_, fun hu => h.quiet (by unfold Unsettled at hu ⊢; rw [hent] at hu; exact hu),
    fun c hc => placed_other s v.files c ij f (hplaced c hc) fun e' he' hsyn => ?_,
    hrules, hseqs, hans, happ⟩
  · have hA := halone (by
      rcases hor with hor | hor | hor
      · exact Or.inl hor
      · exact Or.inr (Or.inl hor)
      · exact Or.inr (Or.inr (by unfold Unsettled at hor ⊢; rw [hent] at hor; exact hor)))
    unfold Alone; rw [hdir]; exact hA
  · exact hap e' (List.mem_of_find?_eq_some he') (by
      rw [entry_name s _ e' he']; exact finalName_ne _) (Or.inl hsyn.symm)

/-- A sync of the journal's file that failed leaves it in its phase. -/
theorem holds_untrust (ph : Phase) (d : Data) (h : ph.Holds d) : ph.Holds d.untrust := by
  cases ph with
  | none => exact h
  | creating => exact ⟨creating_untrust d h.1, h.2⟩
  | unformatted => exact unformatted_untrust d h
  | steady k rs back => exact steady_untrust k rs _ d h
  | found k rs back => exact found_untrust k rs _ d h

/-! ## Helpers for the steps above -/

/-- What may come back where the records end, widened. -/
theorem steady_mono (k : Bytes) (rs : List Record) (P Q : Record → Prop) (d : Data)
    (h : Steady k rs P d) (hpq : ∀ r, P r → Q r) : Steady k rs Q d :=
  ⟨h.key, h.records, h.kept, h.high, h.written,
    fun w r hm hr hp hf => hpq r (h.back w r hm hr hp hf)⟩

/-- The journal's file in a spool that has one: the file its name holds, in the state its phase
says, no other name holding it. -/
theorem journal_holds (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v)
    (hne : v.phase ≠ .none) :
    ∃ ij d, s.lookup journalName = some ij ∧ s.data ij = some d ∧ v.phase.Holds d ∧ Apart s ij := by
  obtain ⟨_, ij, d, _, hl, _, hd, hholds, hap⟩ := h.journal hne
  exact ⟨ij, d, hl, hd, hholds, hap⟩

/-- Every file a name may be left holding is numbered below the next one created: a file created
next is no name's yet, the journal's and the placed commits' among them. -/
theorem leaves_below (s : Fs) (hs : s.Ok) (e : Entry) (he : e ∈ s.dir) (i : Ino)
    (hl : e.Leaves (some i)) : i < s.next := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hs.2.2.2.2 e he i hl)
  exact hs.2.2.1 p hp

/-- **A file just created is apart**: neither the journal's file nor a placed commit's, so the
operations of the POST that writes it leave the others as they are. -/
theorem fresh_apart (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (name : Bytes)
    (hj : name ≠ journalName) (hfree : s.lookup name = none) :
    (s.step (.create name)).1.lookup journalName ≠ some s.next ∧
      ∀ c ∈ placedSet v, ∀ e, (s.step (.create name)).1.entry (finalName c.seq) = some e →
        e.synced ≠ some s.next := by
  have hstep : (s.step (.create name)).1 = ⟨rebind s.dir name (some s.next),
      s.files ++ [(s.next, .empty)], s.next + 1, s.dirTrusted⟩ := by
    simp [Fs.step, hfree]
  rw [hstep]
  refine ⟨fun hl => ?_, fun c hc e he hsyn => ?_⟩
  · have hl' : s.lookup journalName = some s.next := by
      rw [← lookup_other s name journalName (some s.next) hj.symm]; exact hl
    exact Nat.lt_irrefl _ (held_below s h.ok _ _ hl')
  · obtain ⟨e₀, i, _, he₀, hset, hsyn₀, _⟩ := h.placed c hc
    have hne : finalName c.seq ≠ name := by
      intro heq
      rw [← heq] at hfree
      simp [Fs.lookup, he₀, Entry.seen, hset.1, hsyn₀] at hfree
    simp only [Fs.entry, FsModel.entry_rebind, if_neg hne] at he
    rw [show s.dir.find? (·.name == finalName c.seq) = some e₀ from he₀] at he
    cases he
    rw [hsyn₀] at hsyn
    cases hsyn
    have hl : s.lookup (finalName c.seq) = some s.next := by
      simp [Fs.lookup, he₀, Entry.seen, hset.1, hsyn₀]
    exact Nat.lt_irrefl _ (held_below s h.ok _ _ hl)

/-- **A commit's file placed**: once its final name holds a file all of whose octets are kept,
those the store wrote for it, of the commit's size and CRC-32C, a sync of the directory settles the
name. -/
theorem placed_syncDir (s : Fs) (hs : s.Ok) (ht : s.dirTrusted = true) (files : Nat → Bytes)
    (c : Commit) (i : Ino) (d : Data) (hl : s.lookup (finalName c.seq) = some i)
    (hd : s.data i = some d) (hk : d.kept = d.seen) (hh : d.high = d.seen.length)
    (hseen : d.seen = files c.seq) (hlen : (files c.seq).length = c.fileSize)
    (hcrc : (crc32c (files c.seq)).toNat = c.fileCrc) :
    Placed (s.step .syncDir).1 files c := by
  obtain ⟨e, he, hse⟩ : ∃ e, s.entry (finalName c.seq) = some e ∧ e.seen = some i := by
    simp only [Fs.lookup, Option.bind_eq_some_iff] at hl
    exact hl
  have hent : (s.step .syncDir).1.entry (finalName c.seq) =
      some ⟨finalName c.seq, some i, []⟩ := by
    simp only [Fs.step, ht, ↓reduceIte, Fs.entry]
    rw [entry_settle s hs, he, Option.bind_some]
    simp [Entry.settle, hse, entry_name s _ e he]
  refine ⟨_, i, d, hent, ⟨rfl, rfl⟩, rfl, ?_, hk, hh, hseen, hlen, hcrc⟩
  simp only [Fs.step, ht, ↓reduceIte]
  exact hd

/-- Opening a name, reading, a file's size and the list of names change nothing. -/
theorem step_pure (s : Fs) (op : FsModel.Op)
    (hop : (∃ n, op = .open_ n) ∨ (∃ i o l, op = .read i o l) ∨ (∃ i, op = .size i) ∨
      op = .list) : (s.step op).1 = s := by
  rcases hop with ⟨n, rfl⟩ | ⟨i, o, l, rfl⟩ | ⟨i, rfl⟩ | rfl
  · simp only [Fs.step]; split <;> rfl
  · simp only [Fs.step]; split <;> rfl
  · simp only [Fs.step]; split <;> rfl
  · rfl

/-! ## Failures -/

/-- **What an operation that fails may have left**: an append, the file with any first part of its
octets appended; a sync of a file, the file with no later sync trusted; a sync of the directory,
the directory with none trusted; anything else, all of it or nothing. -/
theorem failures_cases (s t : Fs) (op : FsModel.Op) (h : s.Fails t op) :
    (∃ i bs k, op = .append i bs ∧ t = (s.step (.append i (bs.take k))).1) ∨
      (∃ i, op = .sync i ∧ t = (s.onData i Data.untrust).1) ∨
      (op = .syncDir ∧ t = { s with dirTrusted := false }) ∨
      (t = s ∨ t = (s.step op).1) := by
  unfold Fs.Fails Fs.failures at h
  split at h
  · rename_i i bs
    simp only [List.mem_map, List.mem_range] at h
    obtain ⟨k, _, rfl⟩ := h
    exact Or.inl ⟨i, bs, k, rfl, rfl⟩
  · rename_i i
    simp only [List.mem_singleton] at h
    exact Or.inr (Or.inl ⟨i, rfl, h⟩)
  · simp only [List.mem_singleton] at h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact Or.inr (Or.inr (Or.inr h))

/-- An operation done whole or not at all keeps a spool when it keeps one done. -/
theorem spool_whole (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (op : FsModel.Op)
    (hstep : Spool cfg (s.step op).1 v) (t : Fs) (ht : t = s ∨ t = (s.step op).1) :
    Spool cfg t v := by
  rcases ht with rfl | rfl
  · exact h
  · exact hstep

/-- A sync of a file other than the journal's that failed keeps a spool. -/
theorem spool_file_untrust (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (i : Ino)
    (hj : s.lookup journalName ≠ some i) : Spool cfg (s.onData i Data.untrust).1 v :=
  spool_file cfg s v h i Data.untrust (fun d hd => FsModel.untrust_ok d hd) hj
    fun c _ hp => placed_settled s v.files c i Data.untrust untrust_keeps hp

/-- A sync of the journal's file that failed leaves it in its phase. -/
theorem spool_journal_untrust (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (ij : Ino)
    (hl : s.lookup journalName = some ij) : Spool cfg (s.onData ij Data.untrust).1 v := by
  have hne : v.phase ≠ .none := by
    intro hn
    obtain ⟨e, he, hle⟩ := lookup_leaves s _ ij hl
    exact h.empty hn e (List.mem_of_find?_eq_some he) ij hle
  obtain ⟨_, ij', d, _, hl', _, hd, hholds, _⟩ := h.journal hne
  rw [hl] at hl'
  cases hl'
  have := spool_journal cfg s v h ij hl Data.untrust (fun d hd => FsModel.untrust_ok d hd) v.phase
    (fun d' hd' => by rw [hd] at hd'; cases hd'; exact holds_untrust _ _ hholds) h.alone
    h.placed h.rules h.seqs h.answered h.appended
  exact this

/-! ## What the store learns -/

/-- **The octets a POST writes**, under a number no placed commit carries. -/
theorem spool_files (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (q : Nat) (bs : Bytes)
    (hq : ∀ c ∈ placedSet v, c.seq ≠ q) :
    Spool cfg s { v with files := fun n => if n = q then bs else v.files n } := by
  refine ⟨h.ok, h.names, h.room, h.empty, h.journal, h.alone, h.quiet, fun c hc => ?_, h.rules,
    h.seqs, h.answered, h.appended⟩
  have hne : c.seq ≠ q := hq c hc
  obtain ⟨e, i, d, he, hset, hsyn, hd, hk, hh, hseen, hlen, hcrc⟩ := h.placed c hc
  refine ⟨e, i, d, he, hset, hsyn, hd, hk, hh, ?_, ?_, ?_⟩ <;> simp only [if_neg hne]
  · exact hseen
  · exact hlen
  · exact hcrc

/-- A commit appended to the journal, whole or in part, counted as appended. -/
theorem spool_appended (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (c : Commit) :
    Spool cfg s { v with appended := v.appended ++ [c] } :=
  ⟨h.ok, h.names, h.room, h.empty, h.journal, h.alone, h.quiet, h.placed, h.rules, h.seqs,
    h.answered, fun c' hc => List.mem_append_left _ (h.appended c' hc)⟩

/-- A spool with a commit placed has its journal's name settled: the commit's file has a name. -/
theorem settled_of_placed (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (c : Commit)
    (hc : c ∈ placedSet v) : ¬ Unsettled s := by
  intro hu
  obtain ⟨e, i, _, he, _, hsyn, _⟩ := h.placed c hc
  exact h.alone (Or.inr (Or.inr hu)) e (List.mem_of_find?_eq_some he)
    (by rw [entry_name s _ e he]; exact finalName_ne _) i (Or.inl hsyn.symm)

/-- **An article answered 240** once its commit is kept. -/
theorem spool_answer (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (c : Commit)
    (hc : c ∈ commitsOf v.phase.kept) :
    Spool cfg s { v with answered := v.answered ++ [c] } :=
  have hset := settled_of_placed cfg s v h c (by
    unfold placedSet; rw [commitsOf_append]; exact List.mem_append_left _ hc)
  ⟨h.ok, h.names, h.room, h.empty, h.journal, h.alone, fun hu => absurd hu hset, h.placed, h.rules,
    h.seqs, fun c' hc' => by
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact h.answered c' hc'
      · simp only [List.mem_singleton] at hc'; subst hc'; exact hc, h.appended⟩

/-- **What a crash left, read cleanly**: the journal of its records kept, after which a crash can
leave nothing whole. -/
theorem spool_found_clean (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (k : Bytes)
    (rs back : List Record) (hph : v.phase = .found k rs back)
    (hclean : ∀ i d, s.lookup journalName = some i → s.data i = some d → d.seen = journal k rs) :
    Spool cfg s { v with phase := .steady k rs [] } := by
  have hne : v.phase ≠ .none := by rw [hph]; exact fun h => by cases h
  obtain ⟨e, ij, d, he, hl, hb, hd, hholds, hap⟩ := h.journal hne
  rw [hph] at hholds
  have hs := found_clean k rs _ d hholds (hclean ij d hl hd)
  have hsub : ∀ c ∈ commitsOf (rs ++ []), c ∈ commitsOf (v.phase.kept ++ v.phase.back) := by
    intro c hc
    rw [hph]
    simp only [List.append_nil, Phase.kept, Phase.back, commitsOf_append] at hc ⊢
    exact List.mem_append_left _ hc
  refine ⟨h.ok, h.names, h.room, (fun hn => by cases hn),
    fun _ => ⟨e, ij, d, he, hl, hb, hd,
      ⟨hs.key, hs.records, hs.kept, hs.high, hs.written, fun w r hm hr hp hf =>
        (hs.back w r hm hr hp hf).elim⟩, hap⟩,
    fun hor => h.alone (by
      rcases hor with hor | hor | hor
      · cases hor
      · cases hor
      · exact Or.inr (Or.inr hor)), h.quiet, fun c hc => h.placed c (hsub c hc),
    ⟨(by have := h.rules.1; rw [hph] at this; exact this), fun r hr => by simp [Phase.back] at hr⟩,
    fun c hc => h.seqs c (hsub c hc),
    (fun c hc => by have := h.answered c hc; rw [hph] at this; exact this),
    fun c hc => h.appended c (hsub c hc)⟩

/-! ## The premises can hold -/

/-- The premise `Phase.Holds` can hold: of the examples' journal with a commit not synced. -/
theorem holds_witness : (Phase.steady sampleKey wRecords [.commit (articleOf 2)]).Holds wJournal :=
  wJournal_steady

theorem wSpool_journal : wSpool.lookup journalName = some 0 := by decide

theorem wSpool_settled : ¬ Unsettled wSpool :=
  settled_of_placed sampleConfig wSpool wView spool_witness (articleOf 1)
    (by simp [placedSet, wView, wRecords, Phase.kept, Phase.back, commitsOf])

/-- The premises of `spool_journal` can hold together: the examples' journal synced over the commit
of article 2. -/
theorem w_commit_sync : Spool sampleConfig (wSpool.onData 0 Data.sync).1
    { wView with phase := .steady sampleKey (wRecords ++ [.commit (articleOf 2)]) [] } := by
  obtain ⟨_, _, hseen, _, htr⟩ := jSynced_steady
  have hmem : ∀ c ∈ commitsOf (wRecords ++ [.commit (articleOf 2)]),
      c = articleOf 1 ∨ c = articleOf 2 := by
    intro c hc
    simp [wRecords, commitsOf] at hc
    rcases hc with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine spool_journal sampleConfig wSpool wView spool_witness 0 wSpool_journal Data.sync
    (fun d hd => FsModel.sync_ok d hd) _ (fun d hd => ?_) (fun hor => ?_) (fun c hc => ?_)
    ⟨wRules 2 (Or.inr rfl), fun r hr => by simp [Phase.back] at hr⟩ (fun c hc => ?_)
    (fun c hc => ?_) (fun c hc => ?_)
  · have hd0 : wSpool.data 0 = some wJournal := rfl
    rw [hd0] at hd
    cases hd
    have := steady_sync sampleKey wRecords _ wJournal wJournal_steady (by simp [wJournal,
      Data.append, htr]) (.commit (articleOf 2)) (articleOf_ok 2 (by decide) (by decide)) rfl
      (by simp only [wJournal, Data.append, hseen]; rfl)
    exact steady_mono _ _ _ _ _ this.1 fun _ h => h.elim
  · rcases hor with hor | hor | hor
    · cases hor
    · cases hor
    · exact absurd hor wSpool_settled
  · have hc' : c ∈ commitsOf (wRecords ++ [.commit (articleOf 2)]) := by simpa using hc
    rcases hmem c hc' with rfl | rfl
    · exact placed_witness
    · exact spool_witness.placed _ (by simp [wView, wRecords, Phase.kept, Phase.back, commitsOf])
  · have hc' : c ∈ commitsOf (wRecords ++ [.commit (articleOf 2)]) := by simpa using hc
    rcases hmem c hc' with rfl | rfl <;> decide
  · simp only [wView, List.mem_singleton] at hc
    subst hc
    exact List.mem_filterMap.mpr ⟨.commit (articleOf 1), by simp [Phase.kept, wRecords], rfl⟩
  · have hc' : c ∈ commitsOf (wRecords ++ [.commit (articleOf 2)]) := by simpa using hc
    rcases hmem c hc' with rfl | rfl <;> simp [wView]

/-- The premises of `spool_create` and `spool_rename` can hold together: a POST numbered 3 creates
its temporary file and moves it to its final name. -/
theorem w_create_rename :
    Spool sampleConfig (((wSpool.step (.create (tempName 3))).1).step
      (.rename (tempName 3) (finalName 3))).1 { wView with next := 4 } := by
  have h4 := spool_next sampleConfig wSpool wView spool_witness 4 (by decide) (by decide)
  have hplaced : ∀ c ∈ placedSet { wView with next := 4 }, c = articleOf 1 ∨ c = articleOf 2 := by
    intro c hc
    simp [placedSet, wView, wRecords, Phase.kept, Phase.back, commitsOf] at hc
    rcases hc with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hc := spool_create sampleConfig wSpool _ h4 (tempName 3) (by decide)
    ⟨.temp 3, parseName_bytes (.temp 3) (by decide), fun q hq => by
      simp only [seqOf, Option.some.injEq] at hq; subst hq; decide⟩
    ⟨(fun h => by cases h), (fun h => by cases h)⟩ wSpool_settled
  refine spool_rename sampleConfig _ _ hc (tempName 3) (finalName 3) (by decide) (by decide)
    (fun c hc' => ?_) (fun c hc' => ?_) ⟨.final 3, parseName_bytes (.final 3) (by decide),
      fun q hq => by simp only [seqOf, Option.some.injEq] at hq; subst hq; decide⟩
  · rcases hplaced c hc' with rfl | rfl <;> decide
  · rcases hplaced c hc' with rfl | rfl <;> decide

/-- A crash of the examples' spool that keeps just what the journal synced. -/
def wClean : Fs := wSpool.crashWith ⟨[some 0, some 1, some 2], [jSynced.seen, body, body]⟩

/-- The premises of `spool_found_clean` can hold together: that crash, read cleanly. -/
theorem w_found_clean :
    Spool sampleConfig wClean { wView with phase := .steady sampleKey wRecords [] } := by
  obtain ⟨hs, _, hseen, hhigh, _⟩ := jSynced_steady
  have hk := hs.kept
  have hc : FsModel.Crash wSpool wClean := by
    refine ⟨_, ⟨?_, ?_⟩, rfl⟩
    · simp only [wSpool, FsModel.Each]
      exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, trivial⟩
    · simp only [wSpool, FsModel.Each]
      have hf : wFile.Leaves body := by rw [wFile_eq]; exact ⟨List.prefix_refl _, Nat.le_refl _⟩
      refine ⟨⟨?_, ?_⟩, hf, hf, trivial⟩
      · simp only [wJournal, Data.append]
        rw [hk, hseen]
        exact List.prefix_refl _
      · simp only [wJournal, Data.append]
        omega
  have hct : jSynced.seen = journal sampleKey wRecords ++ [] := by rw [hseen, List.append_nil]
  have hleaves : wJournal.Leaves jSynced.seen := by
    refine ⟨?_, ?_⟩
    · simp only [wJournal, Data.append]; rw [hk, hseen]; exact List.prefix_refl _
    · simp only [wJournal, Data.append]; omega
  have hf : Found sampleKey wRecords (· ∈ [.commit (articleOf 2)]) (wJournal.after jSynced.seen) :=
    ⟨rfl, rfl, ⟨[], hct, by simp [Data.after, hseen, scan_encoded sampleKey sampleKey_length
        wRecords wJournal_steady.records]⟩,
      (steady_cut sampleKey wRecords _ wJournal wJournal_steady _ hleaves wRecords [] hct
        (Or.inl rfl)).1⟩
  obtain ⟨st, ops, _, _, hsp, _⟩ := crash_spool_found sampleConfig sampleKey_length wSpool wClean
    wView spool_witness hc sampleKey wRecords [.commit (articleOf 2)] wRecords
    [.commit (articleOf 2)] ⟨rfl, rfl⟩ (fun c h => h) (fun c h => h) spool_witness.rules 0 _
    (by decide) rfl hf apart_witness
  exact spool_found_clean sampleConfig wClean _ hsp sampleKey wRecords _ rfl fun i d hi hd => by
    have hi0 : wClean.lookup journalName = some 0 := by decide
    rw [hi0] at hi
    cases hi
    have hd0 : wClean.data 0 = some (wJournal.after jSynced.seen) := rfl
    rw [hd0] at hd
    cases hd
    simp [Data.after, hseen]

/-! ## Examples -/

/-- What each operation's preconditions keep a spool from, each broken once: after article 1 is
answered, its file renamed away or removed, more written to it, a file put under the journal's
name, another file of its size moved onto its name, a file moved to a name recovery cannot read, the
journal removed or moved away; and the file of a commit appended and not synced removed — each
leaves a crash after which recovery refuses the store, or finds the article's file not the one
written. -/
def regression_919 : Bool :=
  let answered := postOne
  let faultsAfter (ops : List FsModel.Op) := faults (Fs.empty.run (answered ++ ops))
  (faultsAfter [.rename (finalName 1) (quarantineName 1)]).contains (.missingFile 1) &&
    (faultsAfter [.remove (finalName 1)]).contains (.missingFile 1) &&
    (faultsAfter [.append 1 (ascii "x"), .sync 1]).contains (.wrongSize 1) &&
    (faultsAfter [.create (tempName 2), .rename (tempName 2) journalName]).any (fun f =>
      match f with
      | .journal .. | .noJournal => true
      | _ => false) &&
    (recoveries (Fs.empty.run (answered ++ [.create (tempName 2), .append 2 (body.map (· + 1)),
      .sync 2, .rename (tempName 2) (finalName 1), .syncDir]))).contains none &&
    (faults (Fs.empty.run (started ++ posted 1 1 [.start] ++ [.remove (finalName 1)]))).contains
      (.missingFile 1) &&
    (faultsAfter [.create (tempName 2), .rename (tempName 2) (ascii "zz")]).any (fun f =>
      match f with
      | .badName _ => true
      | _ => false) &&
    (faultsAfter [.remove journalName]).contains .noJournal &&
    (faultsAfter [.rename journalName (quarantineName 9)]).contains .noJournal

end DN.News.SpoolOps
