-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.SpoolOps

/-!
# DN.News.RecoveryRun

How the host starts the store on the file system of `DN.News.FsModel`, as
docs/decisions/0005-article-store.md says: it syncs the journal and the directory, reads the
directory, makes each action recovery (`DN.News.Recovery`) plans as operations of the file system,
and then appends the run's start record to the journal and syncs it. A file kept is created, written
and synced; the journal cut is truncated and synced; created, or made again, it is created or cut to
nothing, takes its format and is synced; names are moved and removed, and the directory synced. An
operation that fails stops the start.

Proven: from a spool whose journal's and directory's syncs are trusted — what a crash leaves, or a
restart's spool before any of them failed — while numbers last and under what is assumed of the
journal (`RestartAssumed`), recovery reads what a crash that lost nothing would leave, and finds
every article answered and only commits appended, each with its file; every point of the start is a
spool with those syncs still trusted, and whatever any of its operations leaves when it fails is a
spool, with them trusted unless it was one of those syncs, its bound on numbers at most one past the
spool's — so that a crash there, and a restart unless a sync of the journal or the directory failed,
is like any other; and once the start is done, the store has started — the journal synced and
trusted, holding the records recovery read and then the run's start under recovery's key, the start
where recovery says the journal ends, nothing appended past it, every name settled in a directory
whose syncs are trusted, and every number of a name or a record below the next one recovery gives
(`start_safe`; after a crash, `crash_start`). Recovery's actions are shown one by one: a torn tail
kept (`safe_keep`) and cut (`safe_cut`), the journal made again or created (`safe_again`,
`safe_new`), names tidied (`safe_tidy`), the start record (`safe_record`); the start's syncs bring
the journal to what a crash that lost nothing leaves of it (`spool_startSync`). That the files
recovery sets aside are kept as it plans is tested, not proven. A restart after a sync of the
journal or the directory failed is not covered, as `DN.News.JournalCrash` says.
-/

namespace DN.News.RecoveryRun

open DN.News.Journal
open DN.News.FsModel (Data Entry Fs Ino Op rebind Crash)
open DN.News.Recovery
open DN.News.JournalCrash
open DN.News.Spool
open DN.News.SpoolOps

/-! ## What the host does -/

/-- The syncs a start makes before it reads: the journal's file, if a name holds it, then the
directory. -/
def syncOps (s : Fs) : List Op :=
  match s.lookup journalName with
  | some i => [.sync i, .syncDir]
  | none => [.syncDir]

/-- A journal's format under `k`, at its start. -/
def formatOf (k : Bytes) : Bytes := (Record.format k).encode k 0

/-- The operations the host makes for one of recovery's actions, on `s`. -/
def actionOps (s : Fs) : Action → List Op
  | .keep name octets => [.create name, .append s.next octets, .sync s.next]
  | .rename src dst => [.rename src dst]
  | .remove name => [.remove name]
  | .syncDir => [.syncDir]
  | .cut n =>
    match s.lookup journalName with
    | some i => [.truncate i n, .sync i]
    | none => []
  | .create k =>
    match s.lookup journalName with
    | some i => [.truncate i 0, .append i (formatOf k), .sync i]
    | none => [.create journalName, .append s.next (formatOf k), .sync s.next]

/-- The operations for recovery's actions, in order, each on what those before it left. -/
def planOps (s : Fs) : List Action → List Op
  | [] => []
  | a :: as => actionOps s a ++ planOps (s.run (actionOps s a)) as

/-- The run's start record appended where the journal ends, and synced. -/
def recordOps (st : Store) (s : Fs) : List Op :=
  match s.lookup journalName with
  | some i => [.append i (Record.start.encode st.key st.journalEnd), .sync i]
  | none => []

/-- **What the host does when the store starts on `s`**: the syncs; then, if recovery gives a store,
its actions and the start record. -/
def startOps (cfg : Config) (s : Fs) : List Op :=
  syncOps s ++
    match recover cfg (image (startSyncs s)) with
    | .ok (st, acts) =>
      planOps (startSyncs s) acts ++
        recordOps st ((startSyncs s).run (planOps (startSyncs s) acts))
    | .error _ => []

/-! ## Runs -/

/-- Every point of a run of operations has `P`, and whatever any of them leaves when it fails has
`F` of that operation. -/
def Safe (P : Fs → Prop) (F : Op → Fs → Prop) (s : Fs) : List Op → Prop
  | [] => P s
  | op :: ops => P s ∧ (∀ t, s.Fails t op → F op t) ∧ Safe P F (s.step op).1 ops

/-- Whether the syncs of the journal and of the directory are trusted: none of them has failed. -/
def Trusted (s : Fs) : Prop :=
  s.dirTrusted = true ∧
    ∀ i d, s.lookup journalName = some i → s.data i = some d → d.trusted = true

/-- A spool, with what the store knows of the articles, wherever the journal is, under a bound on
numbers no higher than `N`. -/
def Kept (cfg : Config) (v : View) (N : Nat) (s : Fs) : Prop :=
  ∃ ph n, n ≤ N ∧ Spool cfg s { v with phase := ph, next := n }

/-- **A point of the start**: a spool, its syncs trusted. -/
def Point (cfg : Config) (v : View) (N : Nat) (s : Fs) : Prop := Kept cfg v N s ∧ Trusted s

/-- **What an operation of the start leaves when it fails**: a spool, its syncs trusted unless the
operation was a sync of the journal or of the directory. -/
def Failed (cfg : Config) (v : View) (N : Nat) (op : Op) (t : Fs) : Prop :=
  Kept cfg v N t ∧ (Trusted t ∨ op = .syncDir ∨ ∃ i, op = .sync i ∧ t.lookup journalName = some i)

/-- **The store started**: a spool whose journal is synced and trusted, holding the records
recovery read and then a start, under the key recovery gives, the start's record where recovery
says the journal ends, nothing appended past it; every name settled in a directory whose syncs are
trusted; and every number below the next one recovery gives. -/
def Started (cfg : Config) (v : View) (st : Store) (s : Fs) : Prop :=
  ∃ rs ij d, Spool cfg s { v with phase := .steady st.key (rs ++ [.start]) [], next := st.next } ∧
    commitsOf rs = st.articles ∧ st.journalEnd = (journal st.key rs).length ∧
    s.lookup journalName = some ij ∧ s.data ij = some d ∧
    d.seen = journal st.key (rs ++ [.start]) ∧ d.high = d.seen.length ∧ d.trusted = true ∧
    Fresh st.key (rs ++ [.start]) d ∧ s.dirTrusted = true ∧ ∀ e ∈ s.dir, e.Settled

theorem run_append : ∀ (s : Fs) (l1 l2 : List Op), s.run (l1 ++ l2) = (s.run l1).run l2
  | _, [], _ => rfl
  | _, _ :: l1, l2 => run_append _ l1 l2

theorem safe_append (P : Fs → Prop) (F : Op → Fs → Prop) : ∀ (s : Fs) (l1 l2 : List Op),
    Safe P F s l1 → Safe P F (s.run l1) l2 → Safe P F s (l1 ++ l2)
  | _, [], _, _, h2 => h2
  | s, op :: l1, l2, ⟨hs, hf, h1⟩, h2 => ⟨hs, hf, safe_append P F (s.step op).1 l1 l2 h1 h2⟩

/-- A run, then more from where it ends, with what the second leaves. -/
theorem safe_then (P : Fs → Prop) (F : Op → Fs → Prop) (Q : Fs → Prop) (s : Fs) (a b : List Op)
    (h1 : Safe P F s a) (h2 : Safe P F (s.run a) b ∧ Q ((s.run a).run b)) :
    Safe P F s (a ++ b) ∧ Q (s.run (a ++ b)) :=
  ⟨safe_append P F s a b h1 h2.1, by rw [run_append]; exact h2.2⟩

theorem planOps_append : ∀ (s : Fs) (as bs : List Action),
    planOps s (as ++ bs) = planOps s as ++ planOps (s.run (planOps s as)) bs
  | _, [], _ => rfl
  | s, a :: as, bs => by
    simp only [List.cons_append, planOps, List.append_assoc]
    rw [planOps_append (s.run (actionOps s a)) as bs, run_append]

/-- An operation done whole or not at all, when it fails. -/
theorem fails_whole (s t : Fs) (op : Op) (h : s.Fails t op)
    (ha : ∀ i bs, op ≠ .append i bs) (hs : ∀ i, op ≠ .sync i) (hd : op ≠ .syncDir) :
    t = s ∨ t = (s.step op).1 := by
  rcases failures_cases s t op h with ⟨i, bs, _, rfl, _⟩ | ⟨i, rfl, _⟩ | ⟨rfl, _⟩ | h
  · exact absurd rfl (ha i bs)
  · exact absurd rfl (hs i)
  · exact absurd rfl hd
  · exact h

theorem fails_append (s t : Fs) (i : Ino) (bs : Bytes) (h : s.Fails t (.append i bs)) :
    ∃ k, t = (s.step (.append i (bs.take k))).1 := by
  simp only [Fs.Fails, Fs.failures, List.mem_map, List.mem_range] at h
  obtain ⟨k, _, rfl⟩ := h
  exact ⟨k, rfl⟩

theorem fails_sync (s t : Fs) (i : Ino) (h : s.Fails t (.sync i)) :
    t = (s.onData i Data.untrust).1 := by
  simpa [Fs.Fails, Fs.failures] using h

theorem fails_syncDir (s t : Fs) (h : s.Fails t .syncDir) : t = { s with dirTrusted := false } := by
  simpa [Fs.Fails, Fs.failures] using h

/-- A run of one operation done whole or not at all. -/
theorem safe_whole (P : Fs → Prop) (F : Op → Fs → Prop) (s : Fs) (op : Op) (ops : List Op)
    (hs : P s) (hstep : P (s.step op).1) (hpf : ∀ u, P u → F op u)
    (ha : ∀ i bs, op ≠ .append i bs) (hsy : ∀ i, op ≠ .sync i) (hd : op ≠ .syncDir)
    (rest : Safe P F (s.step op).1 ops) : Safe P F s (op :: ops) :=
  ⟨hs, fun t ht => by
    rcases fails_whole s t op ht ha hsy hd with rfl | rfl
    · exact hpf _ hs
    · exact hpf _ hstep, rest⟩

/-- What a point of the start leaves, failing, is a point. -/
theorem failed_of_point (cfg : Config) (v : View) (N : Nat) (op : Op) (t : Fs)
    (h : Point cfg v N t) : Failed cfg v N op t := ⟨h.1, Or.inl h.2⟩

/-! ## Facts about operations -/

theorem data_ok (s : Fs) (hs : s.Ok) (i : Ino) (d : Data) (hd : s.data i = some d) : d.Ok := by
  simp only [Fs.data, FsModel.lookup_eq_find, Option.map_eq_some_iff] at hd
  obtain ⟨p, hp, rfl⟩ := hd
  exact hs.2.2.2.1 p (List.mem_of_find?_eq_some hp)

theorem sync_trusted (d : Data) : d.sync.trusted = d.trusted := by
  unfold Data.sync; split <;> rfl

theorem syncDir_data (s : Fs) : (s.step .syncDir).1.data = s.data := by
  simp only [Fs.step]; split <;> rfl

theorem syncDir_dirTrusted (s : Fs) : (s.step .syncDir).1.dirTrusted = s.dirTrusted := by
  simp only [Fs.step]; split <;> rfl

theorem syncDir_lookup (s : Fs) (hs : s.Ok) (name : Bytes) :
    (s.step .syncDir).1.lookup name = s.lookup name := by
  simp only [Fs.step]
  split
  · simp only [Fs.lookup, Fs.entry]
    rw [entry_settle s hs name]
    simp only [Fs.entry]
    cases s.dir.find? (·.name == name) with
    | none => rfl
    | some e =>
      simp only [Option.bind_some, Entry.settle]
      cases e.seen <;> rfl
  · rfl

/-- After a trusted sync of the directory, a name that holds a file is settled. -/
theorem syncDir_settled (s : Fs) (hs : s.Ok) (ht : s.dirTrusted = true) (name : Bytes) (i : Ino)
    (hl : s.lookup name = some i) :
    (s.step .syncDir).1.entry name = some ⟨name, some i, []⟩ := by
  obtain ⟨e, he, hse⟩ : ∃ e, s.entry name = some e ∧ e.seen = some i := by
    simp only [Fs.lookup, Option.bind_eq_some_iff] at hl
    exact hl
  simp only [Fs.step, ht, ↓reduceIte, Fs.entry]
  rw [entry_settle s hs, he, Option.bind_some]
  simp [Entry.settle, hse, entry_name s _ e he]

theorem syncDir_unsettled (s : Fs) (hs : s.Ok) (ht : s.dirTrusted = true) (i : Ino)
    (hl : s.lookup journalName = some i) : ¬ Unsettled (s.step .syncDir).1 := fun hu =>
  hu _ (syncDir_settled s hs ht journalName i hl) ⟨rfl, rfl⟩

theorem onData_lookup (s : Fs) (i : Ino) (f : Data → Data) :
    (s.onData i f).1.lookup = s.lookup :=
  lookup_of_dir s _ (FsModel.onData_dir s i f)

theorem onData_entry (s : Fs) (i : Ino) (f : Data → Data) :
    (s.onData i f).1.entry = s.entry :=
  entry_of_dir s _ (FsModel.onData_dir s i f)

theorem onData_dirTrusted (s : Fs) (i : Ino) (f : Data → Data) :
    (s.onData i f).1.dirTrusted = s.dirTrusted := by
  unfold Fs.onData; split <;> rfl

/-- After a trusted sync of the directory, every name is settled. -/
theorem syncDir_all (s : Fs) (ht : s.dirTrusted = true) :
    ∀ e ∈ (s.step .syncDir).1.dir, e.Settled := by
  intro e he
  simp only [Fs.step, ht, ↓reduceIte] at he
  obtain ⟨e₀, _, hse⟩ := List.mem_filterMap.mp he
  simp only [Entry.settle, Option.map_eq_some_iff] at hse
  obtain ⟨i, _, rfl⟩ := hse
  exact ⟨rfl, rfl⟩

theorem trusted_syncDir (s : Fs) (hs : s.Ok) (ht : Trusted s) : Trusted (s.step .syncDir).1 :=
  ⟨by rw [syncDir_dirTrusted]; exact ht.1, fun i d hi hd => by
    rw [syncDir_lookup s hs] at hi
    rw [syncDir_data] at hd
    exact ht.2 i d hi hd⟩

/-- An operation on a file that keeps whether its syncs are trusted keeps the start's trust. -/
theorem trusted_onData (s : Fs) (i : Ino) (f : Data → Data) (hf : ∀ d, (f d).trusted = d.trusted)
    (ht : Trusted s) : Trusted (s.onData i f).1 := by
  refine ⟨by rw [onData_dirTrusted]; exact ht.1, fun j d hj hd => ?_⟩
  rw [onData_lookup] at hj
  rw [data_onData] at hd
  split at hd
  · cases hd' : s.data j with
    | none => rw [hd'] at hd; cases hd
    | some d₀ =>
      rw [hd', Option.map_some, Option.some.injEq] at hd
      subst hd
      rw [hf]
      exact ht.2 j d₀ hj hd'
  · exact ht.2 j d hj hd

/-- An operation on a file other than the journal's keeps the start's trust. -/
theorem trusted_other (s : Fs) (i : Ino) (f : Data → Data) (hj : s.lookup journalName ≠ some i)
    (ht : Trusted s) : Trusted (s.onData i f).1 := by
  refine ⟨by rw [onData_dirTrusted]; exact ht.1, fun j d hj' hd => ?_⟩
  rw [onData_lookup] at hj'
  have hne : j ≠ i := fun h => hj (h ▸ hj')
  rw [data_onData, if_neg hne] at hd
  exact ht.2 j d hj' hd

/-- What an operation on a name other than the journal's leaves of the journal: its entry, the
files and whether the directory's syncs are trusted. -/
theorem other_journal (s : Fs) (op : Op)
    (hop : (∃ n, op = .remove n ∧ n ≠ journalName) ∨
      (∃ a b, op = .rename a b ∧ a ≠ journalName ∧ b ≠ journalName)) :
    (s.step op).1.entry journalName = s.entry journalName ∧ (s.step op).1.files = s.files ∧
      (s.step op).1.dirTrusted = s.dirTrusted := by
  rcases hop with ⟨n, rfl, hn⟩ | ⟨a, b, rfl, ha, hb⟩
  · simp only [Fs.step]
    split
    · exact ⟨entry_other s n journalName none (Ne.symm hn), rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · simp only [Fs.step]
    split
    · split
      · exact ⟨rfl, rfl, rfl⟩
      · rename_i i _ _
        refine ⟨?_, rfl, rfl⟩
        rw [entry_other ({ s with dir := rebind s.dir b (some i) } : Fs) a journalName none
          (Ne.symm ha), entry_other s b journalName _ (Ne.symm hb)]
    · exact ⟨rfl, rfl, rfl⟩

/-! ## A spool through the journal's phases -/

/-- **An operation on the journal's file into a new phase**, its commits among those placed, keeping
those kept and the rules across them. -/
theorem spool_rephase (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (ij : Ino)
    (hl : s.lookup journalName = some ij) (f : Data → Data) (hf : ∀ d, d.Ok → (f d).Ok)
    (ph : Phase) (hholds : ∀ d, s.data ij = some d → ph.Holds (f d))
    (halone : ph = .creating ∨ ph = .unformatted → Alone s)
    (hsub : ∀ c ∈ commitsOf (ph.kept ++ ph.back), c ∈ placedSet v)
    (hkept : ∀ c ∈ commitsOf v.phase.kept, c ∈ commitsOf ph.kept)
    (hrules : Rules cfg (commitsOf ph.kept) ∧
      ∀ r ∈ ph.back, Rules cfg (commitsOf (ph.kept ++ [r]))) :
    Spool cfg (s.onData ij f).1 { v with phase := ph } :=
  spool_journal cfg s v h ij hl f hf ph hholds
    (fun hor => by
      rcases hor with hor | hor | hor
      · exact halone (Or.inl hor)
      · exact halone (Or.inr hor)
      · exact h.alone (Or.inr (Or.inr hor)))
    (fun c hc => h.placed c (hsub c hc)) hrules (fun c hc => h.seqs c (hsub c hc))
    (fun c hc => hkept c (h.answered c hc)) (fun c hc => h.appended c (hsub c hc))

theorem commits_start (rs : List Record) : commitsOf (rs ++ [.start]) = commitsOf rs := by
  simp [commitsOf]

/-! ## The start's syncs -/

/-- **The journal synced by a start**, its syncs trusted: it is then what a crash that lost nothing
leaves of it — with no format, or read as its records. -/
theorem spool_startSync (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (ij : Ino)
    (hl : s.lookup journalName = some ij) (ht : ∀ d, s.data ij = some d → d.trusted = true)
    (ha : RestartAssumed v s) :
    ∃ ph, Spool cfg (s.step (.sync ij)).1 { v with phase := ph } := by
  have hne : v.phase ≠ .none := by
    intro hn
    obtain ⟨e, he, hle⟩ := lookup_leaves s _ ij hl
    exact h.empty hn e (List.mem_of_find?_eq_some he) ij hle
  obtain ⟨_, ij', d, _, hl', _, hd, hholds, _⟩ := h.journal hne
  rw [hl] at hl'
  cases hl'
  have hok := data_ok s h.ok ij d hd
  have htd := ht d hd
  have hsync : ∀ ph : Phase, ph.Holds d.sync → ∀ d', s.data ij = some d' → ph.Holds d'.sync := by
    intro ph hp d' hd'; rw [hd] at hd'; cases hd'; exact hp
  have hsf : ∀ d : Data, d.Ok → d.sync.Ok := fun d hd => FsModel.sync_ok d hd
  have hnil : ∀ c ∈ commitsOf ([] ++ []), c ∈ placedSet v := fun c hc => by
    simp [commitsOf] at hc
  show ∃ ph, Spool cfg (s.onData ij Data.sync).1 _
  cases hp : v.phase with
  | none => exact absurd hp hne
  | creating =>
    rw [hp] at hholds
    have hk : ∀ c ∈ commitsOf v.phase.kept, c ∈ commitsOf ([] : List Record) := by
      rw [hp]; intro c hc; exact hc
    rcases restart_unformatted d hholds.1 hok htd hholds.2 with hu | ⟨k, _, _, hf⟩
    · exact ⟨.unformatted, spool_rephase cfg s v h ij hl Data.sync hsf .unformatted (hsync _ hu)
        (fun _ => h.alone (Or.inl hp)) hnil hk ⟨rules_nil cfg, fun r hr => by cases hr⟩⟩
    · exact ⟨.found k [] [], spool_rephase cfg s v h ij hl Data.sync hsf (.found k [] [])
        (hsync _ (found_mono k [] _ _ _ hf fun _ h => h.elim)) (fun _ => h.alone (Or.inl hp))
        hnil hk ⟨rules_nil cfg, fun r hr => by cases hr⟩⟩
  | unformatted =>
    rw [hp] at hholds
    exact ⟨.unformatted, spool_rephase cfg s v h ij hl Data.sync hsf .unformatted
      (hsync _ (unformatted_sync d hholds)) (fun _ => h.alone (Or.inr (Or.inl hp))) hnil
      (by rw [hp]; intro c hc; exact hc) ⟨rules_nil cfg, fun r hr => by cases hr⟩⟩
  | steady k rs back =>
    rw [hp] at hholds
    have hu := ha ij d hl hd
    rw [hp] at hu
    have hrules := h.rules
    rw [hp] at hrules
    have hpl : placedSet v = commitsOf (rs ++ back) := by simp only [placedSet, hp]; rfl
    rcases crash_found_back k rs _ d hholds d.seen (FsModel.leaves_seen d hok) hu with
      hf | ⟨r, hr, _, _, hf⟩
    · rw [← sync_after d htd] at hf
      exact ⟨.found k rs back, spool_rephase cfg s v h ij hl Data.sync hsf _ (hsync _ hf)
        (fun hor => by rcases hor with hor | hor <;> cases hor) (fun c hc => by rw [hpl]; exact hc)
        (by rw [hp]; intro c hc; exact hc) hrules⟩
    · rw [← sync_after d htd] at hf
      exact ⟨.found k (rs ++ [r]) [], spool_rephase cfg s v h ij hl Data.sync hsf _
        (hsync _ (found_mono k _ _ _ _ hf fun _ h => h.elim))
        (fun hor => by rcases hor with hor | hor <;> cases hor)
        (fun c hc => by rw [hpl]; exact commits_snoc rs back r hr c hc)
        (by rw [hp]; intro c hc; simp only [Phase.kept, commitsOf_append]
            exact List.mem_append_left _ hc)
        ⟨hrules.2 r hr, fun r hr => by cases hr⟩⟩
  | found k rs back =>
    rw [hp] at hholds
    have hrules := h.rules
    rw [hp] at hrules
    exact ⟨.found k rs back, spool_rephase cfg s v h ij hl Data.sync hsf _
      (hsync _ (found_sync k rs _ d hholds)) (fun hor => by rcases hor with hor | hor <;> cases hor)
      (fun c hc => by simp only [placedSet, hp]; exact hc) (by rw [hp]; intro c hc; exact hc)
      hrules⟩

theorem syncOps_run (s : Fs) : s.run (syncOps s) = startSyncs s := by
  cases h : s.lookup journalName <;> simp [syncOps, startSyncs, h, Fs.run]

/-- A sync of the directory at a point of the start, done or failed. -/
theorem safe_syncDir (cfg : Config) (v : View) (N : Nat) (u : Fs) (hu : Point cfg v N u)
    (ops : List Op) (rest : Safe (Point cfg v N) (Failed cfg v N) (u.step .syncDir).1 ops) :
    Safe (Point cfg v N) (Failed cfg v N) u (.syncDir :: ops) :=
  ⟨hu, fun t ht => by
    rw [fails_syncDir u t ht]
    obtain ⟨ph, n, hn, hsp⟩ := hu.1
    exact ⟨⟨ph, n, hn, spool_untrustDir cfg u _ hsp⟩, Or.inr (Or.inl rfl)⟩, rest⟩

theorem point_syncDir (cfg : Config) (v : View) (N : Nat) (u : Fs) (hu : Point cfg v N u) :
    Point cfg v N (u.step .syncDir).1 := by
  obtain ⟨⟨ph, n, hn, hsp⟩, ht⟩ := hu
  exact ⟨⟨ph, n, hn, spool_syncDir cfg u _ hsp⟩, trusted_syncDir u hsp.ok ht⟩

/-- **The start's syncs**, trusted: every point a spool with its syncs trusted, and whatever a sync
that fails leaves a spool. -/
theorem safe_syncOps (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v) (ht : Trusted s)
    (ha : RestartAssumed v s) (N : Nat) (hN : v.next ≤ N) :
    Safe (Point cfg v N) (Failed cfg v N) s (syncOps s) := by
  have hp : Point cfg v N s := ⟨⟨v.phase, v.next, hN, h⟩, ht⟩
  unfold syncOps
  cases hl : s.lookup journalName with
  | none => exact safe_syncDir cfg v N s hp [] (point_syncDir cfg v N s hp)
  | some ij =>
    obtain ⟨ph, hph⟩ := spool_startSync cfg s v h ij hl (fun d hd => ht.2 ij d hl hd) ha
    have hp1 : Point cfg v N (s.step (.sync ij)).1 :=
      ⟨⟨ph, v.next, hN, hph⟩, trusted_onData s ij Data.sync sync_trusted ht⟩
    refine ⟨hp, fun t hf => ?_, safe_syncDir cfg v N _ hp1 [] (point_syncDir cfg v N _ hp1)⟩
    rw [fails_sync s t ij hf]
    exact ⟨⟨v.phase, v.next, hN, spool_journal_untrust cfg s v h ij hl⟩,
      Or.inr (Or.inr ⟨ij, rfl, by rw [onData_lookup]; exact hl⟩)⟩

/-! ## What a start reads -/

theorem startSyncs_dirTrusted (s : Fs) (htd : s.dirTrusted = true) :
    (startSyncs s).dirTrusted = true := by
  unfold startSyncs
  rw [syncDir_dirTrusted]
  split
  · exact (onData_dirTrusted s _ Data.sync).trans htd
  · exact htd

theorem startSyncs_settled (s : Fs) (htd : s.dirTrusted = true) :
    ∀ e ∈ (startSyncs s).dir, e.Settled := by
  rw [startSyncs_dir s htd]
  intro e he
  obtain ⟨e₀, _, hse⟩ := List.mem_filterMap.mp he
  simp only [Entry.settle, Option.map_eq_some_iff] at hse
  obtain ⟨i, _, rfl⟩ := hse
  exact ⟨rfl, rfl⟩

theorem startSyncs_lookup (s : Fs) (hs : s.Ok) (name : Bytes) :
    (startSyncs s).lookup name = s.lookup name := by
  unfold startSyncs
  split
  · rename_i i _
    rw [syncDir_lookup _ (FsModel.step_ok s hs _)]
    exact congrFun (onData_lookup s i Data.sync) name
  · exact syncDir_lookup s hs name

theorem startSyncs_trusted (s : Fs) (hs : s.Ok)
    (ht : ∀ i d, s.lookup journalName = some i → s.data i = some d → d.trusted = true) :
    ∀ i d, (startSyncs s).lookup journalName = some i → (startSyncs s).data i = some d →
      d.trusted = true := by
  intro i d hi hd
  rw [startSyncs_lookup s hs] at hi
  rw [startSyncs_data, if_pos hi] at hd
  cases hd' : s.data i with
  | none => rw [hd'] at hd; cases hd
  | some d₀ =>
    rw [hd', Option.map_some, Option.some.injEq] at hd
    subst hd
    rw [sync_trusted]
    exact ht i d₀ hi hd'

theorem mem_image (s : Fs) (e : Entry) (he : e ∈ s.dir) (i : Ino) (hi : e.seen = some i)
    (d : Data) (hd : s.data i = some d) : (e.name, d.seen) ∈ image s :=
  List.mem_filterMap.mpr ⟨e, he, by simp [hi, hd]⟩

/-- **A spool all of whose names are settled stays one under a lower bound on numbers**, when every
name recovery reads is numbered below it. -/
theorem spool_lower (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v)
    (hset : ∀ e ∈ s.dir, e.Settled) (n : Nat)
    (hn : ∀ p ∈ image s, ∀ m q, parseName p.1 = some m → seqOf m = some q → q < n)
    (hroom : 1 ≤ n ∧ n + 1 < 2 ^ 64) : Spool cfg s { v with next := n } := by
  have hname : ∀ e ∈ s.dir, ∀ m q, parseName e.name = some m → seqOf m = some q → q < n := by
    intro e he m q hm hq
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hset e he).2
    have hseen : e.seen = some i := by simp [Entry.seen, (hset e he).1, hi]
    obtain ⟨d, hd⟩ := data_some s h.ok e.name i (by rw [(lookup_entry s h.ok e he).2, hseen])
    exact hn _ (mem_image s e he i hseen d hd) m q hm hq
  refine ⟨h.ok, fun e he => ?_, hroom, h.empty, h.journal, h.alone, h.quiet, h.placed, h.rules,
    fun c hc => ?_, h.answered, h.appended⟩
  · obtain ⟨m, hm, _⟩ := h.names e he
    exact ⟨m, hm, fun q hq => hname e he m q hm hq⟩
  · obtain ⟨e, i, _, he, _, _, _⟩ := h.placed c hc
    have hv : c.seq < 2 ^ 64 := by have := h.seqs c hc; have := h.room.2; omega
    refine hname e (List.mem_of_find?_eq_some he) (.final c.seq) c.seq ?_ rfl
    rw [entry_name s _ e he]
    exact parseName_bytes (.final c.seq) (by simp [Name.valid, hv])

theorem recover_pos (cfg : Config) (img : Image) (st : Store) (ops : List Action)
    (h : recover cfg img = .ok (st, ops)) : 1 ≤ st.next := by
  obtain ⟨_, _, hc⟩ := recover_cases cfg img st ops h
  rcases hc with ⟨_, rfl, _⟩ | ⟨_, _, ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, hr⟩⟩
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · obtain ⟨_, _, _, _, _, _, hnext, _⟩ := recoverRecords_ok _ _ _ _ _ _ _ _ _ hr
    rw [hnext]
    split <;> simp only [nextSeq] <;> omega

/-- A spool with no journal, its names settled, has no name. -/
theorem dir_none (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v)
    (hset : ∀ e ∈ s.dir, e.Settled) (hp : v.phase = .none) : s.dir = [] := by
  cases hd : s.dir with
  | nil => rfl
  | cons e es =>
    exfalso
    have he : e ∈ s.dir := by rw [hd]; exact List.mem_cons_self ..
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hset e he).2
    exact h.empty hp e he i (Or.inl hi.symm)

/-- What recovery reads of a directory whose only file is the journal's, its names settled. -/
theorem image_alone (s : Fs) (hs : s.Ok) (ha : Alone s) (hset : ∀ e ∈ s.dir, e.Settled)
    (ij : Ino) (d : Data) (hl : s.lookup journalName = some ij) (hd : s.data ij = some d) :
    image s = [(journalName, d.seen)] := by
  have hall : ∀ e ∈ s.dir, e.name = journalName := by
    intro e he
    refine Classical.byContradiction fun hn => ?_
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hset e he).2
    exact ha e he hn i (Or.inl hi.symm)
  obtain ⟨e₀, he₀, hse⟩ : ∃ e, s.entry journalName = some e ∧ e.seen = some ij := by
    simp only [Fs.lookup, Option.bind_eq_some_iff] at hl
    exact hl
  have hmem := List.mem_of_find?_eq_some he₀
  have hdir : s.dir = [e₀] := by
    have hnd := hs.1
    revert hnd hmem hall
    generalize s.dir = l
    intro hall hmem hnd
    match l, hall, hmem, hnd with
    | [a], _, hm, _ => simp only [List.mem_singleton] at hm; rw [hm]
    | a :: b :: rest, hall', _, hnd' =>
      exfalso
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd'
      exact hnd'.1.1 (by rw [hall' a (by simp), hall' b (by simp)])
  simp only [image, hdir, List.filterMap_cons, List.filterMap_nil, hse, Option.bind_some, hd,
    Option.map_some, entry_name s _ e₀ he₀]

/-- What recovery plans for a journal a crash left read as its records: its tail kept and cut, if
torn, then the names tidied. -/
theorem recover_found (cfg : Config) (hkey : cfg.key.length = keyLength) (s : Fs) (v : View)
    (h : Spool cfg s v) (k : Bytes) (rs back : List Record) (hp : v.phase = .found k rs back)
    (ij : Ino) (d : Data) (hl : s.lookup journalName = some ij) (hd : s.data ij = some d)
    (st : Store) (acts : List Action) (hrec : recover cfg (image s) = .ok (st, acts)) :
    Found k rs (· ∈ back) d ∧ ∃ tl, d.seen = journal k rs ++ tl ∧
      recoverRecords cfg (image s) ((image s).filterMap (parseName ·.1)) d.seen k (commitsOf rs)
        (if tl.isEmpty then none else some (journal k rs).length) = .ok (st, acts) := by
  have hne : v.phase ≠ .none := by rw [hp]; exact fun h => by cases h
  obtain ⟨_, ij', d', _, hl', _, hd', hholds, _⟩ := h.journal hne
  rw [hl] at hl'
  cases hl'
  rw [hd] at hd'
  cases hd'
  rw [hp] at hholds
  refine ⟨hholds, ?_⟩
  obtain ⟨tl, hseen, hscan⟩ := hholds.reads
  have hall : ∀ q ∈ image s, (parseName q.1).isSome := by
    intro q hq
    obtain ⟨e, he, hn⟩ := image_names s q hq
    obtain ⟨n, hpn, _⟩ := h.names e he
    rw [← hn, hpn]
    rfl
  have hlook : (image s).lookup journalName = some d.seen := by
    rw [image_lookup s h.ok, hl, Option.bind_some, hd, Option.map_some]
  have hnc : ∀ x w, (if tl.isEmpty then End.clean else End.torn (journal k rs).length) ≠
      .corrupt x w := by
    intro x w; split <;> simp
  rw [recover_of cfg hkey (image s) d.seen k rs _ hall hlook hscan hnc] at hrec
  refine ⟨tl, hseen, ?_⟩
  have hcut : cutOf (if tl.isEmpty then End.clean else End.torn (journal k rs).length) =
      if tl.isEmpty then none else some (journal k rs).length := by
    split <;> rfl
  rw [← hcut]
  exact hrec

/-- What tidying does to a name, `recorded` the names of the records' files: a temporary file
removed, or a final file no record names removed or set aside. -/
theorem tidy_kinds (recorded : List Bytes) (names : List Name) (torn : Bool) (a : Action)
    (ha : a ∈ names.filterMap (tidyName recorded names torn)) :
    (∃ q, a = .remove (tempName q)) ∨
      (∃ q, a = .remove (finalName q) ∧ .final q ∈ names ∧ finalName q ∉ recorded) ∨
      (∃ q, a = .rename (finalName q) (quarantineName q) ∧ .final q ∈ names ∧
        finalName q ∉ recorded) := by
  obtain ⟨n, hn, hna⟩ := List.mem_filterMap.mp ha
  cases n with
  | temp q =>
    simp only [tidyName, Option.some.injEq] at hna
    exact Or.inl ⟨q, hna.symm⟩
  | final q =>
    simp only [tidyName] at hna
    split at hna
    · cases hna
    · rename_i hr
      have hr' : finalName q ∉ recorded := by simpa using hr
      split at hna
      · simp only [Option.some.injEq] at hna
        exact Or.inr (Or.inl ⟨q, hna.symm, hn, hr'⟩)
      · simp only [Option.some.injEq] at hna
        exact Or.inr (Or.inr ⟨q, hna.symm, hn, hr'⟩)
  | journal => simp [tidyName] at hna
  | quarantine q => simp [tidyName] at hna
  | tail q => simp [tidyName] at hna

/-! ## Recovery's actions -/

/-- **The spool at a point of the start**: a spool in that phase, under that bound, the journal's
name holding that file with that data, trusted, the name settled, in a directory whose syncs are
trusted. -/
def At (cfg : Config) (v : View) (ph : Phase) (n : Nat) (ij : Ino) (d : Data) (s : Fs) : Prop :=
  Spool cfg s { v with phase := ph, next := n } ∧ s.lookup journalName = some ij ∧
    s.data ij = some d ∧ d.trusted = true ∧ s.dirTrusted = true ∧ ¬ Unsettled s

theorem at_point (cfg : Config) (v : View) (ph : Phase) (n : Nat) (ij : Ino) (d : Data) (s : Fs)
    (N : Nat) (h : At cfg v ph n ij d s) (hn : n ≤ N) : Point cfg v N s :=
  ⟨⟨ph, n, hn, h.1⟩, h.2.2.2.2.1, fun i d' hi hd' => by
    rw [h.2.1] at hi; cases hi; rw [h.2.2.1] at hd'; cases hd'; exact h.2.2.2.1⟩

/-- An operation on a file other than the journal's, at a point of the start. -/
theorem at_onData (cfg : Config) (v : View) (ph : Phase) (n : Nat) (ij : Ino) (d : Data) (u : Fs)
    (h : At cfg v ph n ij d u) (i : Ino) (f : Data → Data) (hi : ij ≠ i)
    (hsp : Spool cfg (u.onData i f).1 { v with phase := ph, next := n }) :
    At cfg v ph n ij d (u.onData i f).1 := by
  obtain ⟨_, hl, hd, htr, ht, hu⟩ := h
  refine ⟨hsp, by rw [onData_lookup]; exact hl, by rw [data_onData, if_neg hi]; exact hd, htr,
    by rw [onData_dirTrusted]; exact ht, fun hu' => hu ?_⟩
  unfold Unsettled at hu' ⊢
  rw [onData_entry] at hu'
  exact hu'

/-- **The directory synced**, at a point of the start. -/
theorem safe_syncDirAt (cfg : Config) (v : View) (ph : Phase) (n : Nat) (ij : Ino) (d : Data)
    (s : Fs) (N : Nat) (h : At cfg v ph n ij d s) (hn : n ≤ N) :
    Safe (Point cfg v N) (Failed cfg v N) s [.syncDir] ∧
      At cfg v ph n ij d (s.step .syncDir).1 := by
  have hp := at_point cfg v ph n ij d s N h hn
  obtain ⟨hsp, hl, hd, htr, ht, _⟩ := h
  have hat : At cfg v ph n ij d (s.step .syncDir).1 :=
    ⟨spool_syncDir cfg s _ hsp, by rw [syncDir_lookup s hsp.ok]; exact hl,
      by rw [syncDir_data]; exact hd, htr, by rw [syncDir_dirTrusted]; exact ht,
      syncDir_unsettled s hsp.ok ht ij hl⟩
  exact ⟨safe_syncDir cfg v N s hp [] (at_point cfg v ph n ij d _ N hat hn), hat⟩

/-- A name removed or moved, neither the journal's, at a point of the start. -/
theorem safe_otherAt (cfg : Config) (v : View) (ph : Phase) (n : Nat) (ij : Ino) (d : Data)
    (s : Fs) (N : Nat) (h : At cfg v ph n ij d s) (hn : n ≤ N) (op : Op)
    (hop : (∃ m, op = .remove m ∧ m ≠ journalName) ∨
      (∃ a b, op = .rename a b ∧ a ≠ journalName ∧ b ≠ journalName))
    (hsp' : Spool cfg (s.step op).1 { v with phase := ph, next := n }) :
    Safe (Point cfg v N) (Failed cfg v N) s [op] ∧ At cfg v ph n ij d (s.step op).1 := by
  have hp := at_point cfg v ph n ij d s N h hn
  obtain ⟨_, hl, hd, htr, ht, hu⟩ := h
  obtain ⟨he, hf, hdt⟩ := other_journal s op hop
  have h1 : ∀ i bs, op ≠ .append i bs := by
    rcases hop with ⟨m, rfl, _⟩ | ⟨a, b, rfl, _, _⟩ <;> intro i bs h <;> cases h
  have h2 : ∀ i, op ≠ .sync i := by
    rcases hop with ⟨m, rfl, _⟩ | ⟨a, b, rfl, _, _⟩ <;> intro i h <;> cases h
  have h3 : op ≠ .syncDir := by
    rcases hop with ⟨m, rfl, _⟩ | ⟨a, b, rfl, _, _⟩ <;> intro h <;> cases h
  have hat : At cfg v ph n ij d (s.step op).1 :=
    ⟨hsp', by simp only [Fs.lookup, he]; exact hl, by simp only [Fs.data, hf]; exact hd, htr,
      by rw [hdt]; exact ht, fun hu' => hu (by
        unfold Unsettled at hu' ⊢; rw [he] at hu'; exact hu')⟩
  have hp' := at_point cfg v ph n ij d _ N hat hn
  exact ⟨safe_whole _ _ s op [] hp hp' (fun u hu => failed_of_point cfg v N op u hu) h1 h2 h3 hp',
    hat⟩

/-- **A name tidied** once the journal is cut, or read cleanly: a temporary file removed, a final
file no record names removed or set aside, or the directory synced. -/
theorem safe_tidyAction (cfg : Config) (v : View) (k : Bytes) (rs : List Record) (n N : Nat)
    (hn : n < 2 ^ 64) (hN : n ≤ N) (ij : Ino) (d : Data) (s : Fs) (a : Action)
    (ha : a = .syncDir ∨ (∃ q, a = .remove (tempName q)) ∨
      (∃ q, a = .remove (finalName q) ∧ finalName q ∉ (commitsOf rs).map (finalName ·.seq)) ∨
      (∃ q, a = .rename (finalName q) (quarantineName q) ∧
        finalName q ∉ (commitsOf rs).map (finalName ·.seq) ∧ q < n))
    (h : At cfg v (.steady k rs []) n ij d s) :
    Safe (Point cfg v N) (Failed cfg v N) s (actionOps s a) ∧
      At cfg v (.steady k rs []) n ij d (s.run (actionOps s a)) := by
  have hpl : ∀ c ∈ placedSet { v with phase := .steady k rs [], next := n }, c ∈ commitsOf rs := by
    intro c hc
    simpa [placedSet, Phase.kept, Phase.back] using hc
  rcases ha with rfl | ⟨q, rfl⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq, hqn⟩
  · exact safe_syncDirAt cfg v _ n ij d s N h hN
  · exact safe_otherAt cfg v _ n ij d s N h hN _ (Or.inl ⟨_, rfl, temp_ne_journal q⟩)
      (spool_remove cfg s _ h.1 _ (temp_ne_journal q) fun c _ => final_ne_temp _ _)
  · exact safe_otherAt cfg v _ n ij d s N h hN _ (Or.inl ⟨_, rfl, final_ne_journal q⟩)
      (spool_remove cfg s _ h.1 _ (final_ne_journal q) fun c hc e =>
        hq (List.mem_map.mpr ⟨c, hpl c hc, e⟩))
  · have hv : q < 2 ^ 64 := by omega
    exact safe_otherAt cfg v _ n ij d s N h hN _
      (Or.inr ⟨_, _, rfl, final_ne_journal q, quarantine_ne_journal q⟩)
      (spool_rename cfg s _ h.1 _ _ (final_ne_journal q) (quarantine_ne_journal q)
        (fun c hc e => hq (List.mem_map.mpr ⟨c, hpl c hc, e⟩))
        (fun c _ => final_ne_quarantine _ _)
        ⟨.quarantine q, parseName_bytes (.quarantine q) (by simp [Name.valid, hv]),
          fun q' hq' => by simp only [seqOf, Option.some.injEq] at hq'; subst hq'; exact hqn⟩)

/-- **The names tidied**, each action in turn. -/
theorem safe_tidy (cfg : Config) (v : View) (k : Bytes) (rs : List Record) (n N : Nat)
    (hn : n < 2 ^ 64) (hN : n ≤ N) (ij : Ino) (d : Data) :
    ∀ (as : List Action) (s : Fs),
      (∀ a ∈ as, a = .syncDir ∨ (∃ q, a = .remove (tempName q)) ∨
        (∃ q, a = .remove (finalName q) ∧ finalName q ∉ (commitsOf rs).map (finalName ·.seq)) ∨
        (∃ q, a = .rename (finalName q) (quarantineName q) ∧
          finalName q ∉ (commitsOf rs).map (finalName ·.seq) ∧ q < n)) →
      At cfg v (.steady k rs []) n ij d s →
      Safe (Point cfg v N) (Failed cfg v N) s (planOps s as) ∧
        At cfg v (.steady k rs []) n ij d (s.run (planOps s as))
  | [], _, _, h => ⟨at_point cfg v _ n ij d _ N h hN, h⟩
  | a :: as, s, ha, h => by
    obtain ⟨h1, h2⟩ := safe_tidyAction cfg v k rs n N hn hN ij d s a
      (ha a (List.mem_cons_self ..)) h
    obtain ⟨h3, h4⟩ := safe_tidy cfg v k rs n N hn hN ij d as _
      (fun b hb => ha b (List.mem_cons_of_mem _ hb)) h2
    refine ⟨safe_append _ _ _ _ _ h1 h3, ?_⟩
    show At cfg v _ n ij d (s.run (actionOps s a ++ planOps (s.run (actionOps s a)) as))
    rw [run_append]
    exact h4

/-- The names settled once tidying is done: none was tidied, or the directory was synced after. -/
theorem settled_post (u : Fs) (tidy : List Action) (hu : ∀ e ∈ u.dir, e.Settled)
    (ht : (u.run (planOps u tidy)).dirTrusted = true) :
    ∀ e ∈ (u.run (planOps u (tidy ++ if tidy.isEmpty then [] else [.syncDir]))).dir,
      e.Settled := by
  cases tidy with
  | nil => exact hu
  | cons a as =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    rw [planOps_append, run_append]
    exact syncDir_all _ ht

/-- An operation on a file neither the journal's nor a placed commit's keeps a spool. -/
theorem spool_fresh (cfg : Config) (t : Fs) (V : View) (h : Spool cfg t V) (i : Ino)
    (f : Data → Data) (hf : ∀ d, d.Ok → (f d).Ok) (hj : t.lookup journalName ≠ some i)
    (hp : ∀ c ∈ placedSet V, ∀ e, t.entry (finalName c.seq) = some e → e.synced ≠ some i) :
    Spool cfg (t.onData i f).1 V :=
  spool_file cfg t V h i f hf hj fun c hc hpl => placed_other t V.files c i f hpl (hp c hc)

theorem create_eq (s : Fs) (name : Bytes) (hfree : s.lookup name = none) :
    (s.step (.create name)).1 = ⟨rebind s.dir name (some s.next), s.files ++ [(s.next, .empty)],
      s.next + 1, s.dirTrusted⟩ := by
  simp [Fs.step, hfree]

/-- **A torn tail kept**: a new file under a name no file holds, its octets written and synced. -/
theorem safe_keep (cfg : Config) (v : View) (ph : Phase) (n N : Nat) (ij : Ino) (d : Data)
    (s : Fs) (h : At cfg v ph n ij d s) (hN : n ≤ N) (hph : ph ≠ .creating ∧ ph ≠ .unformatted)
    (q : Nat) (hq : q < n) (hfree : s.lookup (tailName q) = none) (o : Bytes) :
    Safe (Point cfg v N) (Failed cfg v N) s (actionOps s (.keep (tailName q) o)) ∧
      At cfg v ph n ij d (s.run (actionOps s (.keep (tailName q) o))) := by
  have hp := at_point cfg v ph n ij d s N h hN
  obtain ⟨hsp, hl, hd, htr, ht, hu⟩ := h
  have hv : q < 2 ^ 64 := by have : n + 1 < 2 ^ 64 := hsp.room.2; omega
  have hj : tailName q ≠ journalName := tail_ne_journal q
  have hname : ∃ m, parseName (tailName q) = some m ∧ ∀ q', seqOf m = some q' → q' < n :=
    ⟨.tail q, parseName_bytes (.tail q) (by simp [Name.valid, hv]), fun q' hq' => by
      simp only [seqOf, Option.some.injEq] at hq'; subst hq'; exact hq⟩
  have h1 := spool_create cfg s _ hsp (tailName q) hj hname hph hu
  obtain ⟨hfj, hfp⟩ := fresh_apart cfg s _ hsp (tailName q) hj hfree
  have hne : ij ≠ s.next := Nat.ne_of_lt (held_below s hsp.ok _ ij hl)
  have hl1 : (s.step (.create (tailName q))).1.lookup journalName = some ij := by
    rw [FsModel.lookup_create s _ _ hfree, if_neg (Ne.symm hj)]; exact hl
  have hd1 : (s.step (.create (tailName q))).1.data ij = some d := by
    rw [create_eq s _ hfree]
    exact lookup_append_new _ _ _ _ hd
  have ht1 : (s.step (.create (tailName q))).1.dirTrusted = true := by
    rw [create_eq s _ hfree]; exact ht
  have he1 : (s.step (.create (tailName q))).1.entry journalName = s.entry journalName := by
    rw [create_eq s _ hfree]; exact entry_other s _ journalName _ (Ne.symm hj)
  have hat1 : At cfg v ph n ij d (s.step (.create (tailName q))).1 :=
    ⟨h1, hl1, hd1, htr, ht1, fun hu' => hu (by
      unfold Unsettled at hu' ⊢; rw [he1] at hu'; exact hu')⟩
  -- the append and the sync touch only the new file
  have hfile : ∀ (u : Fs), Spool cfg u { v with phase := ph, next := n } →
      u.entry = (s.step (.create (tailName q))).1.entry →
      u.lookup = (s.step (.create (tailName q))).1.lookup → ∀ f : Data → Data,
      (∀ d, d.Ok → (f d).Ok) →
      Spool cfg (u.onData s.next f).1 { v with phase := ph, next := n } := by
    intro u hu' he hlk f hf
    refine spool_fresh cfg u _ hu' s.next f hf (by rw [hlk]; exact hfj) fun c hc e he' => ?_
    rw [he] at he'
    exact hfp c hc e he'
  have hat2 : ∀ bs : Bytes, At cfg v ph n ij d ((s.step (.create (tailName q))).1.onData s.next
      fun d => d.append bs).1 := fun bs =>
    at_onData cfg v ph n ij d _ hat1 s.next _ hne
      (hfile _ h1 rfl rfl _ fun d hd => FsModel.append_ok d hd bs)
  have he2 := onData_entry (s.step (.create (tailName q))).1 s.next fun d => d.append o
  have hl2 := onData_lookup (s.step (.create (tailName q))).1 s.next fun d => d.append o
  have hat3 := at_onData cfg v ph n ij d _ (hat2 o) s.next Data.sync hne
    (hfile _ (hat2 o).1 he2 hl2 Data.sync fun d hd => FsModel.sync_ok d hd)
  have hun := at_onData cfg v ph n ij d _ (hat2 o) s.next Data.untrust hne
    (hfile _ (hat2 o).1 he2 hl2 Data.untrust fun d hd => FsModel.untrust_ok d hd)
  refine ⟨safe_whole _ _ s _ _ hp (at_point cfg v ph n ij d _ N hat1 hN)
    (fun u hu => failed_of_point cfg v N _ u hu) (fun _ _ h => by cases h) (fun _ h => by cases h)
    (fun h => by cases h)
    ⟨at_point cfg v ph n ij d _ N hat1 hN, fun t hf => ?_, at_point cfg v ph n ij d _ N (hat2 o) hN,
      fun t hf => ?_, at_point cfg v ph n ij d _ N hat3 hN⟩, hat3⟩
  · obtain ⟨k, rfl⟩ := fails_append _ t s.next o hf
    exact failed_of_point cfg v N _ _ (at_point cfg v ph n ij d _ N (hat2 (o.take k)) hN)
  · rw [fails_sync _ t s.next hf]
    exact failed_of_point cfg v N _ _ (at_point cfg v ph n ij d _ N hun hN)

/-- **The torn tail cut** and the cut synced: the journal of the records read, kept, after which a
crash can leave nothing whole. -/
theorem safe_cut (cfg : Config) (v : View) (k : Bytes) (rs back : List Record) (n N : Nat)
    (ij : Ino) (d : Data) (s : Fs) (h : At cfg v (.found k rs back) n ij d s) (hN : n ≤ N)
    (hf : Found k rs (· ∈ back) d) :
    Safe (Point cfg v N) (Failed cfg v N) s (actionOps s (.cut (journal k rs).length)) ∧
      At cfg v (.steady k rs []) n ij (d.truncate (journal k rs).length).sync
        (s.run (actionOps s (.cut (journal k rs).length))) ∧
      (s.run (actionOps s (.cut (journal k rs).length))).dir = s.dir ∧
      (d.truncate (journal k rs).length).sync.seen = journal k rs ∧
      (d.truncate (journal k rs).length).sync.high = (journal k rs).length := by
  have hp := at_point cfg v _ n ij d s N h hN
  obtain ⟨hsp, hl, hd, ht, htd, hu⟩ := h
  obtain ⟨hcut, hseen⟩ := found_cut k rs _ d hf
  have hops : actionOps s (.cut (journal k rs).length) =
      [.truncate ij (journal k rs).length, .sync ij] := by
    simp [actionOps, hl]
  rw [hops]
  have h1 : Spool cfg (s.onData ij fun d => d.truncate (journal k rs).length).1
      { v with phase := .steady k rs back, next := n } :=
    spool_rephase cfg s _ hsp ij hl _ (fun d hd => FsModel.truncate_ok d hd _) (.steady k rs back)
      (fun d' hd' => by rw [hd] at hd'; cases hd'; exact hcut)
      (fun hor => by rcases hor with hor | hor <;> cases hor) (fun c hc => hc) (fun c hc => hc)
      hsp.rules
  have hl1 : (s.onData ij fun d => d.truncate (journal k rs).length).1.lookup journalName =
      some ij := by
    rw [onData_lookup]; exact hl
  have hd1 : (s.onData ij fun d => d.truncate (journal k rs).length).1.data ij =
      some (d.truncate (journal k rs).length) := by
    rw [data_onData, if_pos rfl, hd]; rfl
  have ht1 : (d.truncate (journal k rs).length).trusted = true := ht
  have hsteady := steady_sync_same k rs _ _ hcut ht1 hseen
  have h2 := spool_rephase cfg _ _ h1 ij hl1 Data.sync (fun d hd => FsModel.sync_ok d hd)
    (.steady k rs [])
    (fun d' hd' => by
      rw [hd1] at hd'; cases hd'; exact steady_mono k rs _ _ _ hsteady fun _ h => h.elim)
    (fun hor => by rcases hor with hor | hor <;> cases hor)
    (fun c hc => by
      simp only [Phase.kept, Phase.back, List.append_nil, placedSet] at hc ⊢
      rw [commitsOf_append]; exact List.mem_append_left _ hc)
    (fun c hc => hc) ⟨hsp.rules.1, fun r hr => by cases hr⟩
  have hu1 : ¬ Unsettled (s.onData ij fun d => d.truncate (journal k rs).length).1 := by
    intro hu'
    apply hu
    unfold Unsettled at hu' ⊢
    rw [onData_entry] at hu'
    exact hu'
  have hat1 : At cfg v (.steady k rs back) n ij (d.truncate (journal k rs).length)
      (s.onData ij fun d => d.truncate (journal k rs).length).1 :=
    ⟨h1, hl1, hd1, ht1, by rw [onData_dirTrusted]; exact htd, hu1⟩
  have hat2 : At cfg v (.steady k rs []) n ij (d.truncate (journal k rs).length).sync
      ((s.onData ij fun d => d.truncate (journal k rs).length).1.onData ij Data.sync).1 :=
    ⟨h2, by rw [onData_lookup]; exact hl1, by rw [data_onData, if_pos rfl, hd1]; rfl,
      by rw [sync_trusted]; exact ht, by rw [onData_dirTrusted, onData_dirTrusted]; exact htd,
      fun hu' => hu1 (by unfold Unsettled at hu' ⊢; rw [onData_entry] at hu'; exact hu')⟩
  refine ⟨safe_whole _ _ s _ _ hp (at_point cfg v _ n ij _ _ N hat1 hN)
    (fun u hu => failed_of_point cfg v N _ u hu) (fun _ _ h => by cases h) (fun _ h => by cases h)
    (fun h => by cases h)
    ⟨at_point cfg v _ n ij _ _ N hat1 hN, fun t hf' => ?_, at_point cfg v _ n ij _ _ N hat2 hN⟩,
    hat2, ?_, ?_, ?_⟩
  · rw [fails_sync _ t ij hf']
    exact ⟨⟨_, n, hN, spool_journal_untrust cfg _ _ h1 ij hl1⟩,
      Or.inr (Or.inr ⟨ij, rfl, by rw [onData_lookup]; exact hl1⟩)⟩
  · show ((s.onData ij _).1.onData ij Data.sync).1.dir = s.dir
    rw [FsModel.onData_dir, FsModel.onData_dir]
  · rw [seen_sync]; exact hseen
  · rw [high_sync _ ht1, hseen]

theorem formatOf_journal (k : Bytes) : formatOf k = journal k [] := (format_journal k).symm

/-- The format appended, whole or in part, to a journal being written that holds nothing. -/
theorem holds_format (d : Data) (hc : Creating d) (hs : d.seen = []) (k : Bytes)
    (hk : k.length = keyLength) (j : Nat) : Phase.creating.Holds (d.append ((formatOf k).take j)) :=
  ⟨creating_append d hc hs k hk j, Or.inr (by simp [Data.append, hs])⟩

/-- **The journal's format written and synced**, the journal holding nothing before: every point a
spool, the journal of no record kept after. -/
theorem safe_format (cfg : Config) (v : View) (n N : Nat) (hN : n ≤ N) (ij : Ino) (d : Data)
    (s : Fs) (h : Spool cfg s { v with phase := .creating, next := n })
    (hl : s.lookup journalName = some ij) (hd : s.data ij = some d) (hc : Creating d)
    (hs : d.seen = []) (ht : d.trusted = true) (htd : s.dirTrusted = true) (k : Bytes)
    (hk : k.length = keyLength) :
    Safe (Point cfg v N) (Failed cfg v N) s [.append ij (formatOf k), .sync ij] ∧
      Spool cfg (s.run [.append ij (formatOf k), .sync ij])
        { v with phase := .steady k [] [], next := n } ∧
      (s.run [.append ij (formatOf k), .sync ij]).lookup journalName = some ij ∧
      (s.run [.append ij (formatOf k), .sync ij]).data ij = some (d.append (formatOf k)).sync ∧
      (s.run [.append ij (formatOf k), .sync ij]).dirTrusted = s.dirTrusted ∧
      (s.run [.append ij (formatOf k), .sync ij]).dir = s.dir ∧
      (d.append (formatOf k)).sync.seen = journal k [] ∧
      (d.append (formatOf k)).sync.high = (journal k []).length ∧
      (d.append (formatOf k)).sync.trusted = true := by
  have hnil : ∀ ph : Phase, ph.kept = [] → ph.back = [] →
      ∀ c ∈ commitsOf (ph.kept ++ ph.back),
        c ∈ placedSet { v with phase := .creating, next := n } := by
    intro ph hk hb c hc; rw [hk, hb] at hc; simp [commitsOf] at hc
  have hT : Trusted s :=
    ⟨htd, fun i d' hi hd' => by rw [hl] at hi; cases hi; rw [hd] at hd'; cases hd'; exact ht⟩
  have h1 : ∀ j, Spool cfg (s.onData ij fun d => d.append ((formatOf k).take j)).1
      { v with phase := .creating, next := n } := fun j =>
    spool_rephase cfg s _ h ij hl _ (fun d hd => FsModel.append_ok d hd _) .creating
      (fun d' hd' => by rw [hd] at hd'; cases hd'; exact holds_format d hc hs k hk j)
      (fun _ => h.alone (Or.inl rfl)) (hnil _ rfl rfl) (fun c hc => hc) h.rules
  have hp1 : ∀ j, Point cfg v N (s.onData ij fun d => d.append ((formatOf k).take j)).1 :=
    fun j => ⟨⟨_, n, hN, h1 j⟩, trusted_onData s ij _ (fun _ => rfl) hT⟩
  have h1' := h1 (formatOf k).length
  rw [List.take_length] at h1'
  have hp1' := hp1 (formatOf k).length
  rw [List.take_length] at hp1'
  have hl1 : (s.onData ij fun d => d.append (formatOf k)).1.lookup journalName = some ij := by
    rw [onData_lookup]; exact hl
  have hd1 : (s.onData ij fun d => d.append (formatOf k)).1.data ij =
      some (d.append (formatOf k)) := by
    rw [data_onData, if_pos rfl, hd]; rfl
  have hc1 : Creating (d.append (formatOf k)) := by
    have := holds_format d hc hs k hk (formatOf k).length
    rw [List.take_length] at this
    exact this.1
  have hs1 : (d.append (formatOf k)).seen = journal k [] := by
    simp [Data.append, hs, formatOf_journal]
  have ht1 : (d.append (formatOf k)).trusted = true := ht
  obtain ⟨hst, _⟩ := creating_sync _ hc1 ht1 k hk hs1
  have h2 := spool_rephase cfg _ _ h1' ij hl1 Data.sync (fun d hd => FsModel.sync_ok d hd)
    (.steady k [] [])
    (fun d' hd' => by
      rw [hd1] at hd'; cases hd'; exact steady_mono k [] _ _ _ hst fun _ h => h.elim)
    (fun hor => by rcases hor with hor | hor <;> cases hor) (hnil _ rfl rfl)
    (fun c hc => by simp [Phase.kept, commitsOf] at hc)
    ⟨rules_nil cfg, fun r hr => by cases hr⟩
  refine ⟨⟨⟨⟨_, n, hN, h⟩, hT⟩, fun t hf => ?_, hp1', fun t hf => ?_,
    ⟨⟨_, n, hN, h2⟩, trusted_onData _ ij Data.sync sync_trusted hp1'.2⟩⟩, h2, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := fails_append s t ij _ hf
    exact failed_of_point cfg v N _ _ (hp1 j)
  · rw [fails_sync _ t ij hf]
    exact ⟨⟨_, n, hN, spool_journal_untrust cfg _ _ h1' ij hl1⟩,
      Or.inr (Or.inr ⟨ij, rfl, by rw [onData_lookup]; exact hl1⟩)⟩
  · show ((s.onData ij _).1.onData ij Data.sync).1.lookup journalName = some ij
    rw [onData_lookup]; exact hl1
  · show ((s.onData ij _).1.onData ij Data.sync).1.data ij = _
    rw [data_onData, if_pos rfl, hd1]; rfl
  · show ((s.onData ij _).1.onData ij Data.sync).1.dirTrusted = _
    rw [onData_dirTrusted, onData_dirTrusted]
  · show ((s.onData ij _).1.onData ij Data.sync).1.dir = _
    rw [FsModel.onData_dir, FsModel.onData_dir]
  · rw [seen_sync]; exact hs1
  · rw [high_sync _ ht1, hs1]
  · rw [sync_trusted]; exact ht

/-- **The journal made again**: what a crash left with no format cut to nothing, its format
appended and synced. -/
theorem safe_again (cfg : Config) (v : View) (n N : Nat) (ij : Ino) (d : Data) (s : Fs)
    (h : At cfg v .unformatted n ij d s) (hN : n ≤ N) (hu : Unformatted d) (k : Bytes)
    (hk : k.length = keyLength) :
    Safe (Point cfg v N) (Failed cfg v N) s (actionOps s (.create k)) ∧
      At cfg v (.steady k [] []) n ij ((d.truncate 0).append (formatOf k)).sync
        (s.run (actionOps s (.create k))) ∧
      (s.run (actionOps s (.create k))).dir = s.dir ∧
      ((d.truncate 0).append (formatOf k)).sync.seen = journal k [] ∧
      ((d.truncate 0).append (formatOf k)).sync.high = (journal k []).length := by
  have hp := at_point cfg v _ n ij d s N h hN
  obtain ⟨hsp, hl, hd, ht, htd, hun⟩ := h
  have hops : actionOps s (.create k) = .truncate ij 0 :: [.append ij (formatOf k), .sync ij] := by
    simp [actionOps, hl]
  rw [hops]
  obtain ⟨hc, hs⟩ := unformatted_again d hu
  have h1 : Spool cfg (s.onData ij fun d => d.truncate 0).1
      { v with phase := .creating, next := n } :=
    spool_rephase cfg s _ hsp ij hl _ (fun d hd => FsModel.truncate_ok d hd 0) .creating
      (fun d' hd' => by rw [hd] at hd'; cases hd'; exact ⟨hc, Or.inl hs⟩)
      (fun _ => hsp.alone (Or.inr (Or.inl rfl)))
      (fun c hc => by simp [Phase.kept, Phase.back, commitsOf] at hc)
      (fun c hc => by simp [Phase.kept, commitsOf] at hc) ⟨rules_nil cfg, fun r hr => by cases hr⟩
  have hl1 : (s.onData ij fun d => d.truncate 0).1.lookup journalName = some ij := by
    rw [onData_lookup]; exact hl
  have hd1 : (s.onData ij fun d => d.truncate 0).1.data ij = some (d.truncate 0) := by
    rw [data_onData, if_pos rfl, hd]; rfl
  have htd1 : (s.onData ij fun d => d.truncate 0).1.dirTrusted = true := by
    rw [onData_dirTrusted]; exact htd
  have hp1 : Point cfg v N (s.onData ij fun d => d.truncate 0).1 :=
    ⟨⟨_, n, hN, h1⟩, trusted_onData s ij _ (fun _ => rfl) hp.2⟩
  obtain ⟨hsafe, h2, hl2, hd2, ht2, hdir2, hseen, hhigh, htr⟩ :=
    safe_format cfg v n N hN ij (d.truncate 0) _ h1 hl1 hd1 hc hs ht htd1 k hk
  have hrun : s.run [.truncate ij 0, .append ij (formatOf k), .sync ij] =
      (s.onData ij fun d => d.truncate 0).1.run [.append ij (formatOf k), .sync ij] := rfl
  have hdir : ((s.onData ij fun d => d.truncate 0).1.run
      [.append ij (formatOf k), .sync ij]).dir = s.dir := by
    rw [hdir2, FsModel.onData_dir]
  rw [hrun]
  refine ⟨safe_whole _ _ s _ _ hp hp1 (fun u hu => failed_of_point cfg v N _ u hu)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun h => by cases h) hsafe,
    ⟨h2, hl2, hd2, htr, by rw [ht2]; exact htd1, ?_⟩, hdir, hseen, hhigh⟩
  intro hu'
  apply hun
  unfold Unsettled at hu' ⊢
  rw [entry_of_dir s _ hdir] at hu'
  exact hu'

/-- **The journal created** where there is none: its format appended and synced, then its name. -/
theorem safe_new (cfg : Config) (v : View) (n N : Nat) (hN : n ≤ N) (s : Fs)
    (hsp : Spool cfg s { v with phase := .none, next := n }) (ht : s.dirTrusted = true) (k : Bytes)
    (hk : k.length = keyLength) :
    Safe (Point cfg v N) (Failed cfg v N) s (actionOps s (.create k) ++ [.syncDir]) ∧
      At cfg v (.steady k [] []) n s.next (Data.empty.append (formatOf k)).sync
        (s.run (actionOps s (.create k) ++ [.syncDir])) ∧
      (∀ e ∈ (s.run (actionOps s (.create k) ++ [.syncDir])).dir, e.Settled) ∧
      (Data.empty.append (formatOf k)).sync.seen = journal k [] ∧
      (Data.empty.append (formatOf k)).sync.high = (journal k []).length := by
  have hfree : s.lookup journalName = none := by
    cases hl : s.lookup journalName with
    | none => rfl
    | some i =>
      obtain ⟨e, he, hle⟩ := lookup_leaves s _ i hl
      exact absurd hle (hsp.empty rfl e (List.mem_of_find?_eq_some he) i)
  have hops : actionOps s (.create k) =
      .create journalName :: [.append s.next (formatOf k), .sync s.next] := by
    simp [actionOps, hfree]
  rw [hops]
  have h1 := spool_create_journal cfg s _ hsp rfl
  have hl1 : (s.step (.create journalName)).1.lookup journalName = some s.next := by
    rw [FsModel.lookup_create s _ _ hfree, if_pos rfl]
  have hd1 : (s.step (.create journalName)).1.data s.next = some Data.empty := by
    rw [create_eq s _ hfree]
    exact lookup_append_fresh s.next Data.empty s.files fun p hp heq => by
      have := hsp.ok.2.2.1 p hp; rw [heq] at this; exact Nat.lt_irrefl _ this
  have ht1 : (s.step (.create journalName)).1.dirTrusted = true := by
    rw [create_eq s _ hfree]; exact ht
  have hp : Point cfg v N s :=
    ⟨⟨_, n, hN, hsp⟩, ht, fun i d hi _ => by rw [hfree] at hi; cases hi⟩
  have hp1 : Point cfg v N (s.step (.create journalName)).1 :=
    ⟨⟨_, n, hN, h1⟩, ht1, fun i d hi hd => by
      rw [hl1] at hi; cases hi; rw [hd1] at hd; cases hd; rfl⟩
  obtain ⟨hsafe, h3, hl3, hd3, ht3, _, hseen, hhigh, htr⟩ :=
    safe_format cfg v n N hN s.next Data.empty _ h1 hl1 hd1 creating_empty rfl rfl ht1 k hk
  have ht3' : ((s.step (.create journalName)).1.run
      [.append s.next (formatOf k), .sync s.next]).dirTrusted = true := by
    rw [ht3]; exact ht1
  have hok3 := h3.ok
  have hp3 : Point cfg v N ((s.step (.create journalName)).1.run
      [.append s.next (formatOf k), .sync s.next]) :=
    ⟨⟨_, n, hN, h3⟩, ht3', fun i d hi hd => by
      rw [hl3] at hi; cases hi; rw [hd3] at hd; cases hd; exact htr⟩
  have hrun : s.run ([.create journalName, .append s.next (formatOf k), .sync s.next] ++
      [.syncDir]) =
      (((s.step (.create journalName)).1.run [.append s.next (formatOf k), .sync s.next]).step
        .syncDir).1 := by
    rw [run_append]; rfl
  refine ⟨safe_append _ _ s _ _ (safe_whole _ _ s _ _ hp hp1
    (fun u hu => failed_of_point cfg v N _ u hu) (fun _ _ h => by cases h) (fun _ h => by cases h)
    (fun h => by cases h) hsafe) (safe_syncDir cfg v N _ hp3 [] (point_syncDir cfg v N _ hp3)),
    ?_, ?_, hseen, hhigh⟩
  · rw [hrun]
    exact ⟨spool_syncDir cfg _ _ h3, by rw [syncDir_lookup _ hok3]; exact hl3,
      by rw [syncDir_data]; exact hd3, htr, by rw [syncDir_dirTrusted]; exact ht3',
      syncDir_unsettled _ hok3 ht3' s.next hl3⟩
  · rw [hrun]; exact syncDir_all _ ht3'

/-- **The run's start appended** where the journal ends, and synced: the store started. -/
theorem safe_record (cfg : Config) (v : View) (st : Store) (rs : List Record) (N : Nat) (ij : Ino)
    (d : Data) (s : Fs) (h : At cfg v (.steady st.key rs []) st.next ij d s) (hN : st.next ≤ N)
    (hs : d.seen = journal st.key rs) (hh : d.high = d.seen.length)
    (hend : st.journalEnd = (journal st.key rs).length) (harts : commitsOf rs = st.articles)
    (hall : ∀ e ∈ s.dir, e.Settled) :
    Safe (Point cfg v N) (Failed cfg v N) s (recordOps st s) ∧
      Started cfg v st (s.run (recordOps st s)) := by
  have hp := at_point cfg v _ _ ij d s N h hN
  obtain ⟨hsp, hl, hd, ht, htd, _⟩ := h
  obtain ⟨_, ij', d', _, hl', _, hd', hholds, _⟩ := hsp.journal (fun h => by cases h)
  rw [hl] at hl'
  cases hl'
  rw [hd] at hd'
  cases hd'
  have hops : recordOps st s = [.append ij (Record.start.encode st.key (journal st.key rs).length),
      .sync ij] := by
    simp [recordOps, hl, hend]
  rw [hops]
  have hrules : Rules cfg (commitsOf rs) := hsp.rules.1
  have hh' : d.high = (journal st.key rs).length := by rw [hh, hs]
  have h1 : ∀ j, Spool cfg (s.onData ij fun d =>
      d.append ((Record.start.encode st.key (journal st.key rs).length).take j)).1
      { v with phase := .steady st.key rs [.start], next := st.next } := fun j =>
    spool_rephase cfg s _ hsp ij hl _ (fun d hd => FsModel.append_ok d hd _)
      (.steady st.key rs [.start])
      (fun d' hd' => by
        rw [hd] at hd'; cases hd'
        exact steady_mono _ rs _ _ _
          (steady_append _ rs _ d hholds hs hh' .start rfl rfl (Or.inr rfl) j)
          fun r hr => List.mem_singleton.mpr hr)
      (fun hor => by rcases hor with hor | hor <;> cases hor)
      (fun c hc => by simpa [Phase.kept, Phase.back, placedSet, commits_start] using hc)
      (fun c hc => hc)
      ⟨hrules, fun r hr => by
        simp only [Phase.back, List.mem_singleton] at hr
        subst hr
        show Rules cfg (commitsOf (rs ++ [.start]))
        rw [commits_start]; exact hrules⟩
  have hp1 : ∀ j, Point cfg v N (s.onData ij fun d =>
      d.append ((Record.start.encode st.key (journal st.key rs).length).take j)).1 := fun j =>
    ⟨⟨_, st.next, hN, h1 j⟩, trusted_onData s ij _ (fun _ => rfl) hp.2⟩
  have h1' := h1 (Record.start.encode st.key (journal st.key rs).length).length
  rw [List.take_length] at h1'
  have hp1' := hp1 (Record.start.encode st.key (journal st.key rs).length).length
  rw [List.take_length] at hp1'
  have hl1 : (s.onData ij fun d =>
      d.append (Record.start.encode st.key (journal st.key rs).length)).1.lookup journalName =
      some ij := by
    rw [onData_lookup]; exact hl
  have hd1 : (s.onData ij fun d =>
      d.append (Record.start.encode st.key (journal st.key rs).length)).1.data ij =
      some (d.append (Record.start.encode st.key (journal st.key rs).length)) := by
    rw [data_onData, if_pos rfl, hd]; rfl
  have hst1 := steady_append _ rs _ d hholds hs hh' .start rfl rfl (Or.inr rfl)
    (Record.start.encode st.key (journal st.key rs).length).length
  rw [List.take_length] at hst1
  have ht1 : (d.append (Record.start.encode st.key (journal st.key rs).length)).trusted = true := ht
  have hs1 : (d.append (Record.start.encode st.key (journal st.key rs).length)).seen =
      journal st.key rs ++ Record.start.encode st.key (journal st.key rs).length := by
    simp [Data.append, hs]
  obtain ⟨hst2, hfr2⟩ := steady_sync _ rs _ _ hst1 ht1 .start rfl rfl hs1
  have h2 := spool_rephase cfg _ _ h1' ij hl1 Data.sync (fun d hd => FsModel.sync_ok d hd)
    (.steady st.key (rs ++ [.start]) [])
    (fun d' hd' => by
      rw [hd1] at hd'; cases hd'; exact steady_mono _ _ _ _ _ hst2 fun _ h => h.elim)
    (fun hor => by rcases hor with hor | hor <;> cases hor)
    (fun c hc => by simpa [Phase.kept, Phase.back, placedSet, commits_start] using hc)
    (fun c hc => by simpa [Phase.kept, commits_start] using hc)
    ⟨by show Rules cfg (commitsOf (rs ++ [.start])); rw [commits_start]; exact hrules,
      fun r hr => by cases hr⟩
  refine ⟨⟨hp, fun t hf => ?_, hp1', fun t hf => ?_,
    ⟨⟨_, st.next, hN, h2⟩, trusted_onData _ ij Data.sync sync_trusted hp1'.2⟩⟩,
    rs, ij, _, h2, harts, hend, ?_, ?_, ?_, ?_, ?_, hfr2, ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := fails_append s t ij _ hf
    exact failed_of_point cfg v N _ _ (hp1 j)
  · rw [fails_sync _ t ij hf]
    exact ⟨⟨_, st.next, hN, spool_journal_untrust cfg _ _ h1' ij hl1⟩,
      Or.inr (Or.inr ⟨ij, rfl, by rw [onData_lookup]; exact hl1⟩)⟩
  · show ((s.onData ij _).1.onData ij Data.sync).1.lookup journalName = some ij
    rw [onData_lookup]; exact hl1
  · show ((s.onData ij _).1.onData ij Data.sync).1.data ij = _
    rw [data_onData, if_pos rfl, hd1]; rfl
  · rw [seen_sync, hs1, journal_append]
  · rw [high_sync _ ht1, seen_sync]
  · rw [sync_trusted]; exact ht
  · show ((s.onData ij _).1.onData ij Data.sync).1.dirTrusted = true
    rw [onData_dirTrusted, onData_dirTrusted]; exact htd
  · show ∀ e ∈ ((s.onData ij _).1.onData ij Data.sync).1.dir, e.Settled
    rw [FsModel.onData_dir, FsModel.onData_dir]; exact hall

/-! ## The start -/

/-- The journal's name settled, when every name is and it holds a file. -/
theorem settled_journal (s : Fs) (hset : ∀ e ∈ s.dir, e.Settled) (ij : Ino)
    (hl : s.lookup journalName = some ij) : ¬ Unsettled s := by
  intro hu
  obtain ⟨e, he, _⟩ : ∃ e, s.entry journalName = some e ∧ e.seen = some ij := by
    simp only [Fs.lookup, Option.bind_eq_some_iff] at hl; exact hl
  exact hu e he (hset e (List.mem_of_find?_eq_some he))

/-- A name recovery reads no file under holds none. -/
theorem lookup_none_of_image (s : Fs) (hs : s.Ok) (name : Bytes)
    (h : (image s).lookup name = none) : s.lookup name = none := by
  cases hl : s.lookup name with
  | none => rfl
  | some i =>
    obtain ⟨d, hd⟩ := data_some s hs name i hl
    rw [image_lookup s hs, hl, Option.bind_some, hd] at h
    cases h

/-- **A start keeps the spool**: from a spool whose journal's and directory's syncs are trusted —
after a crash, or a restart before any of them failed — while numbers last and under what is
assumed of the journal, recovery reads what a crash that lost nothing would leave and finds every
article answered and only commits appended, each with its file; every point of the start is a
spool with those syncs trusted, and whatever any of its operations leaves when it fails is a spool,
with them trusted unless it was one of those syncs, under a bound on numbers at most one past the
spool's; and once the start is done the store has started as recovery says. -/
theorem start_safe (cfg : Config) (hkey : cfg.key.length = keyLength) (s : Fs) (v : View)
    (h : Spool cfg s v) (ht : Trusted s) (ha : RestartAssumed v s) (hroom : v.next + 2 < 2 ^ 64) :
    image (startSyncs s) = image (s.crashWith s.current) ∧
    ∃ st acts, recover cfg (image (startSyncs s)) = .ok (st, acts) ∧
      Recovers v (image (startSyncs s)) st ∧
      Safe (Point cfg v (v.next + 1)) (Failed cfg v (v.next + 1)) s (startOps cfg s) ∧
      Started cfg v st (s.run (startOps cfg s)) := by
  refine ⟨by rw [image_startSyncs, image_current], ?_⟩
  obtain ⟨st, acts, ph, hrec, hrv, hsp, harts, hnx, _, hkind⟩ :=
    spool_restart cfg hkey s v h ht.1 ht.2 ha
  refine ⟨st, acts, hrec, hrv, ?_⟩
  have hok2 := startSyncs_ok s h.ok
  have hset2 := startSyncs_settled s ht.1
  have htd2 := startSyncs_dirTrusted s ht.1
  have htj2 := startSyncs_trusted s h.ok ht.2
  have hpos := recover_pos cfg _ st acts hrec
  have hlow : Spool cfg (startSyncs s) { v with phase := ph, next := st.next } :=
    spool_lower cfg _ _ hsp hset2 st.next
      (fun p hp m q hm hq => (recover_next cfg _ st acts hrec).2 p hp m q hm hq) ⟨hpos, by omega⟩
  have hstart : startOps cfg s = syncOps s ++ (planOps (startSyncs s) acts ++
      recordOps st ((startSyncs s).run (planOps (startSyncs s) acts))) := by
    simp only [startOps, hrec]
  rw [hstart, run_append, syncOps_run]
  suffices H : Safe (Point cfg v (v.next + 1)) (Failed cfg v (v.next + 1)) (startSyncs s)
      (planOps (startSyncs s) acts ++
        recordOps st ((startSyncs s).run (planOps (startSyncs s) acts))) ∧
      Started cfg v st ((startSyncs s).run (planOps (startSyncs s) acts ++
        recordOps st ((startSyncs s).run (planOps (startSyncs s) acts)))) from
    ⟨safe_append _ _ _ _ _ (safe_syncOps cfg s v h ht ha _ (Nat.le_succ _))
      (by rw [syncOps_run]; exact H.1), H.2⟩
  have finish : ∀ (L : List Op) (k : Bytes) (rs : List Record) (ij : Ino) (d : Data), st.key = k →
      Safe (Point cfg v (v.next + 1)) (Failed cfg v (v.next + 1)) (startSyncs s) L →
      At cfg v (.steady k rs []) st.next ij d ((startSyncs s).run L) ∧
        (∀ e ∈ ((startSyncs s).run L).dir, e.Settled) →
      d.seen = journal k rs → d.high = d.seen.length →
      st.journalEnd = (journal k rs).length → commitsOf rs = st.articles →
      Safe (Point cfg v (v.next + 1)) (Failed cfg v (v.next + 1)) (startSyncs s)
          (L ++ recordOps st ((startSyncs s).run L)) ∧
        Started cfg v st ((startSyncs s).run (L ++ recordOps st ((startSyncs s).run L))) := by
    intro L k rs ij d hk h1 h2 hs hh hend hc
    subst hk
    exact safe_then _ _ _ _ _ _ h1
      (safe_record cfg v st rs _ ij d _ h2.1 hnx hs hh hend hc h2.2)
  have hfirst : firstFrame = (journal cfg.key []).length := by
    rw [format_journal, format_encode_length cfg.key hkey]
  rcases hkind with rfl | rfl | ⟨k, rs, back, rfl, hk⟩
  · -- no journal: one is created
    have hdir := dir_none cfg _ _ hlow hset2 rfl
    rw [image_nil _ hdir, recover_empty cfg hkey] at hrec
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrec
    obtain ⟨rfl, rfl⟩ := hrec
    obtain ⟨h1, h2, hall, hs, hh⟩ :=
      safe_new cfg v (fresh cfg).next _ hnx (startSyncs s) hlow htd2 cfg.key hkey
    have hplan : planOps (startSyncs s) [.create cfg.key, .syncDir] =
        actionOps (startSyncs s) (.create cfg.key) ++ [.syncDir] := rfl
    rw [hplan]
    exact finish _ cfg.key [] _ _ rfl h1 ⟨h2, hall⟩ hs (by rw [hh, hs]) hfirst rfl
  · -- a journal with no format: made again
    obtain ⟨_, ij, d, _, hl, _, hd, hholds, _⟩ := hlow.journal (fun h => by cases h)
    have hu : Unformatted d := hholds
    have halone := hlow.alone (Or.inr (Or.inl rfl))
    rw [image_alone _ hok2 halone hset2 ij d hl hd, recover_unformatted cfg hkey d.seen
      (by rw [hu.reads]) (fun x w => by rw [hu.reads]; split <;> simp)] at hrec
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrec
    obtain ⟨rfl, rfl⟩ := hrec
    obtain ⟨h1, h2, hdir, hs, hh⟩ := safe_again cfg v _ _ ij d _
      ⟨hlow, hl, hd, htj2 ij d hl hd, htd2, settled_journal _ hset2 ij hl⟩ hnx hu cfg.key hkey
    have hplan : planOps (startSyncs s) [.create cfg.key] =
        actionOps (startSyncs s) (.create cfg.key) := by
      simp only [planOps, List.append_nil]
    rw [hplan]
    exact finish _ cfg.key [] _ _ rfl h1 ⟨h2, by rw [hdir]; exact hset2⟩ hs (by rw [hh, hs])
      hfirst rfl
  · -- a journal read as its records: its tail kept and cut, if torn, and the names tidied
    obtain ⟨_, ij, d, _, hl, _, hd, _, _⟩ := hlow.journal (fun h => by cases h)
    have hnu := settled_journal _ hset2 ij hl
    obtain ⟨hf, tl, hseen, hrr⟩ :=
      recover_found cfg hkey _ _ hlow k rs back rfl ij d hl hd st acts hrec
    obtain ⟨_, _, _, _, _, _, hnext, hlt, hend⟩ := recoverRecords_ok _ _ _ _ _ _ _ _ _ hrr
    have hops := recoverRecords_ops _ _ _ _ _ _ _ _ _ hrr
    have harts' : commitsOf rs = st.articles := harts.symm
    have ht := htj2 ij d hl hd
    have hat : At cfg v (.found k rs back) st.next ij d (startSyncs s) :=
      ⟨hlow, hl, hd, ht, htd2, hnu⟩
    have hpost : ∀ torn : Bool, ∀ a ∈ ((image (startSyncs s)).filterMap (parseName ·.1)).filterMap
        (tidyName ((commitsOf rs).map (finalName ·.seq))
          ((image (startSyncs s)).filterMap (parseName ·.1)) torn) ++
        (if (((image (startSyncs s)).filterMap (parseName ·.1)).filterMap
          (tidyName ((commitsOf rs).map (finalName ·.seq))
            ((image (startSyncs s)).filterMap (parseName ·.1)) torn)).isEmpty then []
          else [.syncDir]),
        a = .syncDir ∨ (∃ q, a = .remove (tempName q)) ∨
          (∃ q, a = .remove (finalName q) ∧ finalName q ∉ (commitsOf rs).map (finalName ·.seq)) ∨
          (∃ q, a = .rename (finalName q) (quarantineName q) ∧
            finalName q ∉ (commitsOf rs).map (finalName ·.seq) ∧ q < st.next) := by
      intro torn a ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases tidy_kinds _ _ torn a ha with ⟨q, rfl⟩ | ⟨q, rfl, _, hq⟩ | ⟨q, rfl, hqn, hq⟩
        · exact Or.inr (Or.inl ⟨q, rfl⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨q, rfl, hq⟩))
        · refine Or.inr (Or.inr (Or.inr ⟨q, rfl, hq, ?_⟩))
          obtain ⟨p, hp, hpn⟩ := (mem_names _ _).mp hqn
          exact (recover_next cfg _ st acts hrec).2 p hp _ q hpn rfl
      · split at ha
        · cases ha
        · exact Or.inl (List.mem_singleton.mp ha)
    -- the names tidied after `u`, every name settled at the end
    have tidied : ∀ (torn : Bool) (u : Fs) (d' : Data),
        At cfg v (.steady k rs []) st.next ij d' u → (∀ e ∈ u.dir, e.Settled) →
        Safe (Point cfg v (v.next + 1)) (Failed cfg v (v.next + 1)) u (planOps u
          (((image (startSyncs s)).filterMap (parseName ·.1)).filterMap
            (tidyName ((commitsOf rs).map (finalName ·.seq))
              ((image (startSyncs s)).filterMap (parseName ·.1)) torn) ++
          (if (((image (startSyncs s)).filterMap (parseName ·.1)).filterMap
            (tidyName ((commitsOf rs).map (finalName ·.seq))
              ((image (startSyncs s)).filterMap (parseName ·.1)) torn)).isEmpty then []
            else [.syncDir]))) ∧
        (At cfg v (.steady k rs []) st.next ij d' (u.run (planOps u
          (((image (startSyncs s)).filterMap (parseName ·.1)).filterMap
            (tidyName ((commitsOf rs).map (finalName ·.seq))
              ((image (startSyncs s)).filterMap (parseName ·.1)) torn) ++
          (if (((image (startSyncs s)).filterMap (parseName ·.1)).filterMap
            (tidyName ((commitsOf rs).map (finalName ·.seq))
              ((image (startSyncs s)).filterMap (parseName ·.1)) torn)).isEmpty then []
            else [.syncDir])))) ∧
          ∀ e ∈ (u.run (planOps u
            (((image (startSyncs s)).filterMap (parseName ·.1)).filterMap
              (tidyName ((commitsOf rs).map (finalName ·.seq))
                ((image (startSyncs s)).filterMap (parseName ·.1)) torn) ++
            (if (((image (startSyncs s)).filterMap (parseName ·.1)).filterMap
              (tidyName ((commitsOf rs).map (finalName ·.seq))
                ((image (startSyncs s)).filterMap (parseName ·.1)) torn)).isEmpty then []
              else [.syncDir])))).dir, e.Settled) := by
      intro torn u d' hu hall
      obtain ⟨h1, h2⟩ := safe_tidy cfg v k rs st.next _ hlt hnx ij d' _ u (hpost torn) hu
      have hpre := safe_tidy cfg v k rs st.next _ hlt hnx ij d' _ u
        (fun a ha => hpost torn a (List.mem_append_left _ ha)) hu
      exact ⟨h1, h2, settled_post u _ hall hpre.2.2.2.2.2.1⟩
    by_cases htl : tl = []
    · -- read cleanly
      subst htl
      simp only [List.isEmpty_nil, ↓reduceIte, List.append_nil, Option.isSome_none,
        Option.getD_none, List.nil_append] at hseen hops hend
      have hclean := spool_found_clean cfg _ _ hlow k rs back rfl fun i d' hi hd' => by
        rw [hl] at hi; cases hi; rw [hd] at hd'; cases hd'; exact hseen
      obtain ⟨h1, h2⟩ := tidied false (startSyncs s) d ⟨hclean, hl, hd, ht, htd2, hnu⟩ hset2
      rw [hops]
      exact finish _ k rs ij d hk h1 h2 hseen hf.high (by rw [hend, hseen]) harts'
    · -- a torn tail
      have hcut : (if tl.isEmpty then none else some (journal k rs).length) =
          some (journal k rs).length := by
        cases tl with
        | nil => exact absurd rfl htl
        | cons _ _ => rfl
      rw [hcut] at hrr hops hend hnext
      simp only [Option.isSome_some, ↓reduceIte, Option.getD_some] at hops hend hnext
      have hfree : (startSyncs s).lookup (tailName (nextSeq (commitsOf rs)
          ((image (startSyncs s)).filterMap (parseName ·.1)))) = none :=
        lookup_none_of_image _ hok2 _ ((recover_safe cfg _ st acts hrec
          (.keep (tailName (nextSeq (commitsOf rs) ((image (startSyncs s)).filterMap
            (parseName ·.1)))) (le 8 (journal k rs).length ++ d.seen.drop (journal k rs).length))
          (by rw [hops]; simp)).2 _ rfl)
      obtain ⟨hk1, hk2⟩ := safe_keep cfg v _ st.next _ ij d _ hat hnx
        ⟨(fun h => by cases h), (fun h => by cases h)⟩ _ (by omega) hfree
        (le 8 (journal k rs).length ++ d.seen.drop (journal k rs).length)
      obtain ⟨hd1, hd2⟩ := safe_syncDirAt cfg v _ st.next ij d _ _ hk2 hnx
      have hall4 := syncDir_all _ hk2.2.2.2.2.1
      obtain ⟨hc1, hc2, hcdir, hcs, hch⟩ := safe_cut cfg v k rs back st.next _ ij d _ hd2 hnx hf
      have hT := tidied true _ _ hc2 (by rw [hcdir]; exact hall4)
      have hC := safe_then _ _ (fun u => At cfg v (.steady k rs []) st.next ij _ u ∧
        ∀ e ∈ u.dir, e.Settled) _ _ _ hc1 hT
      have hD := safe_then _ _ (fun u => At cfg v (.steady k rs []) st.next ij _ u ∧
        ∀ e ∈ u.dir, e.Settled) _ [.syncDir] _ hd1 hC
      have hK := safe_then _ _ (fun u => At cfg v (.steady k rs []) st.next ij _ u ∧
        ∀ e ∈ u.dir, e.Settled) _ _ _ hk1 hD
      rw [hops]
      exact finish _ k rs ij _ hk hK.1 hK.2 hcs (by rw [hch, hcs]) hend harts'

/-- What a crash leaves has its syncs trusted, as a start needs. -/
theorem crash_trusted (s t : Fs) (h : Crash s t) : Trusted t := by
  have hs := FsModel.crash_settles s t h
  refine ⟨hs.1, fun i d _ hd => ?_⟩
  simp only [Fs.data, FsModel.lookup_eq_find, Option.map_eq_some_iff] at hd
  obtain ⟨p, hp, rfl⟩ := hd
  exact (hs.2.2.1 p (List.mem_of_find?_eq_some hp)).2.2

/-- **A start after a crash**: under what is assumed of the journal, while numbers last, the start
on what a crash of a spool left reads it as it is, recovers as `spool_crash` says, keeps a spool
at every point and failure as `start_safe` says, and starts the store. -/
theorem crash_start (cfg : Config) (hkey : cfg.key.length = keyLength) (s t : Fs) (v : View)
    (h : Spool cfg s v) (hc : Crash s t) (ha : Assumed v s t) (hroom : v.next + 2 < 2 ^ 64) :
    image (startSyncs t) = image t ∧
    ∃ st acts, recover cfg (image (startSyncs t)) = .ok (st, acts) ∧
      Recovers v (image (startSyncs t)) st ∧
      Safe (Point cfg v (v.next + 1)) (Failed cfg v (v.next + 1)) t (startOps cfg t) ∧
      Started cfg v st (t.run (startOps cfg t)) := by
  obtain ⟨_, _, ph, _, _, hsp, _, _, _, hkind⟩ := spool_crash cfg hkey s v h t hc ha
  have hra : RestartAssumed { v with phase := ph } t := by
    intro i d _ _
    rcases hkind with rfl | rfl | ⟨k, rs, back, rfl, _⟩ <;> trivial
  exact ⟨image_startSyncs t,
    (start_safe cfg hkey t { v with phase := ph } hsp (crash_trusted s t hc) hra hroom).2⟩

/-! ## The premises can hold -/

/-- The premise `At` can hold: of a crash of the examples' spool that kept what the journal synced,
read cleanly. -/
theorem at_witness : At sampleConfig wView (.steady sampleKey wRecords []) 3 0
    (wJournal.after jSynced.seen) wClean := by
  have hsp := w_found_clean
  refine ⟨hsp, by decide, rfl, rfl, rfl,
    settled_of_placed sampleConfig wClean _ hsp (articleOf 1) ?_⟩
  simp [placedSet, wRecords, Phase.kept, Phase.back, commitsOf]

/-- The premise `Point` can hold: of that crash. -/
theorem point_witness : Point sampleConfig wView 3 wClean :=
  at_point _ _ _ _ _ _ _ 3 at_witness (Nat.le_refl _)

/-- The premise `Trusted` can hold: of the crash that left the commit of article 2 torn. -/
theorem trusted_witness : Trusted wCrash := crash_trusted wSpool wCrash wCrash_crash

/-- The premises of `crash_start`, and so those of `start_safe` on what the crash left, hold
together, and with them `Safe` and `Started`: of the crash of the examples' spool that left the
commit of article 2 torn. -/
theorem start_witness : image (startSyncs wCrash) = image wCrash ∧
    ∃ st acts, recover sampleConfig (image (startSyncs wCrash)) = .ok (st, acts) ∧
    Recovers wView (image (startSyncs wCrash)) st ∧
    Safe (Point sampleConfig wView 4) (Failed sampleConfig wView 4) wCrash
      (startOps sampleConfig wCrash) ∧
    Started sampleConfig wView st (wCrash.run (startOps sampleConfig wCrash)) :=
  crash_start sampleConfig sampleKey_length wSpool wCrash wView spool_witness wCrash_crash
    assumed_witness (by decide)

/-! ## Examples -/

/-- The points of a run from `s`, and what each operation, failing, may leave. -/
def reached (s : Fs) (ops : List Op) : List Fs :=
  (List.range (ops.length + 1)).flatMap fun n =>
    let u := s.run (ops.take n)
    u :: match ops[n]? with
      | some op => u.failures op
      | none => []

/-- Whether every name holds a file, every name and file is synced, and the directory's syncs are
trusted. -/
def allSynced (u : Fs) : Bool :=
  u.dirTrusted && u.dir.all fun e => e.held.isEmpty &&
    match e.synced.bind u.data with
    | some d => d.kept == d.seen && d.high == d.seen.length && d.trusted
    | none => false

/-- Whether the start on `s` leaves what recovery planned and the run's start record after the
journal's records, every name and file synced. -/
def asPlanned (s : Fs) : Bool :=
  match recover sampleConfig (image (startSyncs s)) with
  | .ok (st, acts) =>
    let img := applyAll (image (startSyncs s)) acts
    let want := setName img journalName
      ((img.lookup journalName).getD [] ++ Record.start.encode st.key st.journalEnd)
    let u := s.run (startOps sampleConfig s)
    allSynced u && (image u).length == want.length && want.all ((image u).contains ·)
  | .error _ => false

/-- Whether every crash at every point of the start on `s`, and of whatever any of its operations
leaves when it fails, recovers with the articles `answered` among its own, each file whole; whether
the start leaves what recovery planned; and whether recovering again then finds the same articles
and nothing to do. -/
def startsOn (s : Fs) (answered : List Commit) : Bool :=
  (reached s (startOps sampleConfig s)).all (fun u =>
    (recoveries u).all fun r => match r with
      | some cs => answered.all (cs.contains ·)
      | none => false) &&
  asPlanned s &&
  match recover sampleConfig (image (startSyncs s)),
      recover sampleConfig (image (s.run (startOps sampleConfig s))) with
  | .ok (st, _), .ok (st', acts) => acts.isEmpty && st'.articles == st.articles
  | _, _ => false

/-- The file system after `ops`, then a crash that lost nothing. -/
def after (ops : List Op) : Fs := (Fs.empty.run ops).crashWith (Fs.empty.run ops).current

/-- **Starts on what crashes left, and restarts**: a journal torn in a commit, the file of that
commit in place and a temporary file — the tail kept and cut, the file set aside, the temporary one
removed; a journal read cleanly beside a file no record names, removed; a journal with no format,
made again; no journal, created; and, with nothing lost, a process stopped once the journal was
synced and before its name was, and one stopped with a commit appended and not synced. Article 1
answered stays at every point and failure of each, and each start leaves what recovery planned. -/
def regression_920 : Bool :=
  let commit2 := (Record.commit (articleOf 2)).encode sampleKey (journal sampleKey wRecords).length
  let placed := postOne ++ [.create (tempName 2), .append 2 body, .sync 2,
    .rename (tempName 2) (finalName 2), .syncDir]
  startsOn (after (placed ++ [.append 0 (commit2.take 5), .create (tempName 3)])) [articleOf 1] &&
    startsOn (after placed) [articleOf 1] &&
    startsOn (after [.create journalName, .append 0 ((journal sampleKey []).take 7)]) [] &&
    startsOn Fs.empty [] &&
    startsOn (Fs.empty.run [.create journalName, .append 0 (journal sampleKey []), .sync 0]) [] &&
    startsOn (Fs.empty.run (started ++ posted 1 1 [.start])) []

/-- Why a start needs its syncs trusted: once a sync of the journal has failed after a commit was
appended, a restart reads the commit, but its own syncs make nothing durable, and a crash after the
start may lose the article it started with; had the sync been done, none could. -/
def regression_921 : Bool :=
  let s := Fs.empty.run (started ++ posted 1 1 [.start])
  let failed := (s.onData 0 Data.untrust).1
  let synced := (s.step (.sync 0)).1
  articlesOf (recover sampleConfig (image (startSyncs failed))) == some [articleOf 1] &&
    (recoveries (failed.run (startOps sampleConfig failed))).contains (some []) &&
    recoveries (synced.run (startOps sampleConfig synced)) == [some [articleOf 1]]

end DN.News.RecoveryRun
