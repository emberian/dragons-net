-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.StoreOps

/-!
# DN.News.StoreRun

The store's runs from an empty directory on the file system of `DN.News.FsModel` (`Reach`): starts
(`DN.News.RecoveryRun`), one process at a time, each with its own configuration (a key of sixteen
octets, the last start's groups or more), only while the journal's and the directory's syncs are
trusted and sequence numbers last; the store's steps (`DN.News.StoreOps`); crashes and the process
killed at any point, a kill during an operation counting as its failure.

Proven: every point keeps the invariant (`reach_good`); a crash anywhere recovers without
corruption under the next start's configuration, with every article answered 240 and only commits
a run appended for an article it did not refuse, each with its octets and CRC-32C (`store_safe`);
a running store keeps every answered article, its file in place (`store_serves`).

Assumed: `CrashAssumed`, `StartAssumed` (after a crash it holds of itself, so it is assumed only of
a start after the process ended without a loss of power); the program's and the host's part, as in
`DN.News.StoreOps`. Not covered: a start after a failed sync of the journal or the directory without
a loss of power; a start without a group an article carries.
-/

namespace DN.News.StoreRun

open DN.News.Journal
open DN.News.FsModel (Data Entry Fs Ino Op Crash)
open DN.News.Recovery
open DN.News.JournalCrash
open DN.News.Spool
open DN.News.SpoolOps
open DN.News.RecoveryRun
open DN.News.StoreOps
open DN.News.CommandSpec (ascii)

/-! ## Runs -/

/-- Where a run of the store is: no process, a start from `s₀` that has made `n` of its operations,
or the store running. -/
inductive Proc
  | down
  | starting (s₀ : Fs) (n : Nat)
  | up (p : Prog)

/-- **Assumed of a crash**, of the journal's file as it was and as the crash left it: while nothing
of it is kept, a frame at its start that checks under the key it carries is a format written there
(`FormatWritten`); once a format under a key of sixteen octets is kept, under that key, a frame
whose tag checks past what is kept is one an append wrote where it lies (`Unforged`). -/
def CrashAssumed (s t : Fs) : Prop :=
  ∀ i d d', t.lookup journalName = some i → s.data i = some d → t.data i = some d' →
    (d.kept = [] → FormatWritten d d'.seen) ∧
    ∀ k, k.length = keyLength → (Record.format k).encode k 0 <+: d.kept → Unforged k d d'.seen

/-- **Assumed of a start**, of the journal's file the program reads: once a format under a key of
sixteen octets is kept, under that key, a frame whose tag checks past what is kept is one an append
wrote where it lies. -/
def StartAssumed (s : Fs) : Prop :=
  ∀ i d, s.lookup journalName = some i → s.data i = some d →
    ∀ k, k.length = keyLength → (Record.format k).encode k 0 <+: d.kept → Unforged k d d.seen

/-- A run number above every run that appended or refused an article. -/
def nextRun (h : Hist) : Nat := (h.appended.map (·.1) ++ h.refused.map (·.1)).foldl max 0 + 1

/-- What the program knows once its start is done: recovery's key and next number, the journal's
file, and the journal's records as it reads them, the run's start the last. -/
def progAfter (st : Store) (s : Fs) (r : Nat) : Prog :=
  ⟨st.key, ((s.data ((s.lookup journalName).getD 0)).map fun d =>
    (scan d.seen).records.tail).getD [], (s.lookup journalName).getD 0, st.next, fun _ => none,
    none, true, true, r⟩

/-- The history of a run that has done nothing. -/
def Hist.empty : Hist := ⟨[], [], [], fun _ => []⟩

/-- **The runs of the store**, from an empty directory, with the configuration of the last start
and a bound on the sequence numbers they have reached. -/
inductive Reach : Config → Fs → Proc → Hist → Nat → Prop
  /-- an empty directory and no process -/
  | init (cfg : Config) : Reach cfg Fs.empty .down Hist.empty 1
  /-- a crash, under what is assumed of it -/
  | crash (cfg : Config) (s : Fs) (proc : Proc) (h : Hist) (b : Nat) (t : Fs)
      (hr : Reach cfg s proc h b) (hc : Crash s t) (ha : CrashAssumed s t) :
      Reach cfg t .down h b
  /-- the process ended, or killed between operations -/
  | stop (cfg : Config) (s : Fs) (proc : Proc) (h : Hist) (b : Nat)
      (hr : Reach cfg s proc h b) : Reach cfg s .down h b
  /-- a start begun with no process, under a configuration of its own — a key of sixteen octets,
  and the groups of the last start, perhaps with more — while the syncs of the journal and the
  directory are trusted and numbers last, under what is assumed of it -/
  | begin (cfg cfg' : Config) (s : Fs) (h : Hist) (b : Nat) (hr : Reach cfg s .down h b)
      (hkey : cfg'.key.length = keyLength) (hg : cfg.groups ⊆ cfg'.groups) (ht : Trusted s)
      (ha : StartAssumed s) (hb : b + 2 < 2 ^ 64) : Reach cfg' s (.starting s 0) h (b + 1)
  /-- one more of the start's operations done -/
  | startStep (cfg : Config) (s s₀ : Fs) (n : Nat) (h : Hist) (b : Nat)
      (hr : Reach cfg s (.starting s₀ n) h b) (hn : n < (startOps cfg s₀).length) :
      Reach cfg (s.step (startOps cfg s₀)[n]).1 (.starting s₀ (n + 1)) h b
  /-- one of the start's operations failed, or the process was killed during it: the start stops -/
  | startFails (cfg : Config) (s s₀ : Fs) (n : Nat) (h : Hist) (b : Nat) (t : Fs)
      (hr : Reach cfg s (.starting s₀ n) h b) (hn : n < (startOps cfg s₀).length)
      (ht : s.Fails t (startOps cfg s₀)[n]) : Reach cfg t .down h b
  /-- the start done: the store runs, its run numbered above every run that appended or refused
  an article -/
  | started (cfg : Config) (s s₀ : Fs) (h : Hist) (b : Nat) (st : Store) (acts : List Action)
      (hr : Reach cfg s (.starting s₀ (startOps cfg s₀).length) h b)
      (hrec : recover cfg (image (startSyncs s₀)) = .ok (st, acts)) :
      Reach cfg s (.up (progAfter st s (nextRun h))) h st.next
  /-- a step of the store, its operation failing or not -/
  | step (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (b : Nat) (s' : Fs) (p' : Prog)
      (h' : Hist) (hr : Reach cfg s (.up p) h b) (hs : Step cfg s p h s' p' h') :
      Reach cfg s' (.up p') h' p'.next

/-! ## What a run keeps -/

/-- The spool as the history knows it, wherever the journal is and whatever the bound. -/
def histView (h : Hist) (ph : Phase) (n : Nat) : View :=
  ⟨ph, h.answered, h.appended.map Prod.snd, h.files, n⟩

/-- No commit appended for an article refused, by the run that refused it. -/
def Unrefused (h : Hist) : Prop := ∀ r c, (r, c) ∈ h.appended → (r, c.seq) ∉ h.refused

/-- **What a run keeps**: with no process, a spool as the history knows it, under the bound; during
a start, what `start_safe` asks of where the start began and the start's operations done so far;
and while the store runs, the store running. -/
def Good (cfg : Config) : Fs → Proc → Hist → Nat → Prop
  | s, .down, h, b => Unrefused h ∧ ∃ ph n, n ≤ b ∧ Spool cfg s (histView h ph n)
  | s, .starting s₀ k, h, b => cfg.key.length = keyLength ∧ Unrefused h ∧ ∃ ph m, m + 1 ≤ b ∧
      m + 2 < 2 ^ 64 ∧ Spool cfg s₀ (histView h ph m) ∧ Trusted s₀ ∧
      RestartAssumed (histView h ph m) s₀ ∧ k ≤ (startOps cfg s₀).length ∧
      s = s₀.run ((startOps cfg s₀).take k)
  | s, .up p, h, b => Running cfg s p h ∧ p.next = b

/-! ## What is assumed, on the data -/

/-- The journal's file a crash leaves under its name is the one the spool's journal's name held. -/
theorem crash_journal_ino (cfg : Config) (s t : Fs) (v : View) (h : Spool cfg s v)
    (hc : Crash s t) (i : Ino) (hi : t.lookup journalName = some i) :
    v.phase ≠ .none ∧ s.lookup journalName = some i := by
  obtain ⟨e, he, hl⟩ := crash_held s t h.ok hc journalName i hi
  have hne : v.phase ≠ .none := fun hn => h.empty hn e (List.mem_of_find?_eq_some he) i hl
  obtain ⟨e', ij, _, he', hl', hb, _⟩ := h.journal hne
  rw [he] at he'
  cases he'
  rcases hb _ hl with hb | hb
  · cases hb
  · cases hb; exact ⟨hne, hl'⟩

/-- **What is assumed of a crash, on the data, is what a spool's crash lemma assumes**, whatever the
spool's view. -/
theorem assumed_of (cfg : Config) (s t : Fs) (v : View) (h : Spool cfg s v) (hc : Crash s t)
    (ha : CrashAssumed s t) : Assumed v s t := by
  intro i d d' hi hd hd'
  obtain ⟨hne, hl⟩ := crash_journal_ino cfg s t v h hc i hi
  obtain ⟨hfw, hun⟩ := ha i d d' hi hd hd'
  obtain ⟨_, ij, d₀, _, hl₀, _, hd₀, hholds, _⟩ := h.journal hne
  rw [hl] at hl₀
  cases hl₀
  rw [hd] at hd₀
  cases hd₀
  cases hp : v.phase with
  | creating => rw [hp] at hholds; exact hfw hholds.1.kept
  | steady k rs back =>
    rw [hp] at hholds
    have hk : d.kept = journal k rs := hholds.kept
    exact hun k hholds.key (hk ▸ format_prefix_journal k rs)
  | none => trivial
  | unformatted => trivial
  | found _ _ _ => trivial

/-- What is assumed of a start, on the data, is what `start_safe` assumes, whatever the spool's
view. -/
theorem restartAssumed_of (cfg : Config) (s : Fs) (v : View) (h : Spool cfg s v)
    (ha : StartAssumed s) : RestartAssumed v s := by
  intro i d hi hd
  cases hp : v.phase with
  | steady k rs back =>
    have hne : v.phase ≠ .none := by rw [hp]; exact fun h => by cases h
    obtain ⟨_, ij, d₀, _, hl₀, _, hd₀, hholds, _⟩ := h.journal hne
    rw [hi] at hl₀
    cases hl₀
    rw [hd] at hd₀
    cases hd₀
    rw [hp] at hholds
    have hk : d.kept = journal k rs := hholds.kept
    exact ha i d hi hd k hholds.key (hk ▸ format_prefix_journal k rs)
  | none => trivial
  | creating => trivial
  | unformatted => trivial
  | found _ _ _ => trivial

/-- **After a crash, what is assumed of a start holds of itself**: a crash leaves nothing past what
is kept. So it is assumed only of a start after the process ended without a loss of power. -/
theorem startAssumed_crash (s t : Fs) (h : Crash s t) : StartAssumed t := by
  intro i d _ hd k _ _
  have hs := FsModel.crash_settles s t h
  simp only [Fs.data, FsModel.lookup_eq_find, Option.map_eq_some_iff] at hd
  obtain ⟨p, hp, rfl⟩ := hd
  have := (hs.2.2.1 p (List.mem_of_find?_eq_some hp)).1
  exact unforged_kept k _ _ (by rw [this]; exact Nat.le_refl _)

/-! ## Facts used below -/

theorem spool_empty (cfg : Config) : Spool cfg Fs.empty (histView Hist.empty .none 1) :=
  ⟨FsModel.empty_fs_ok, (fun e he => by cases he), ⟨Nat.le_refl _, by decide⟩,
    (fun _ e he => by cases he), (fun h => absurd rfl h), (fun _ e he => by cases he),
    (fun _ => rfl), (fun c hc => by simp [histView, Phase.kept, Phase.back, commitsOf] at hc),
    ⟨rules_nil cfg, fun r hr => by cases hr⟩,
    (fun c hc => by simp [histView, Phase.kept, Phase.back, commitsOf] at hc),
    (fun c hc => by cases hc),
    (fun c hc => by simp [histView, Phase.kept, Phase.back, commitsOf] at hc)⟩

/-- What a crash of a spool leaves is a spool, whatever the configuration's key. -/
theorem crash_spool (cfg : Config) (s t : Fs) (v : View) (h : Spool cfg s v) (hc : Crash s t)
    (ha : CrashAssumed s t) : ∃ ph, Spool cfg t { v with phase := ph } := by
  let cfgK : Config := { cfg with key := List.replicate keyLength 0 }
  obtain ⟨_, _, ph, _, _, hsp, _⟩ := spool_crash cfgK (by simp [cfgK]) s v
    (spool_config cfg cfgK (List.Subset.refl _) s v h) t hc (assumed_of cfg s t v h hc ha)
  exact ⟨ph, spool_config cfgK cfg (List.Subset.refl _) t _ hsp⟩

theorem lt_nextRun (h : Hist) (r : Nat)
    (hr : r ∈ h.appended.map (·.1) ++ h.refused.map (·.1)) : r < nextRun h := by
  have := (foldl_max_ge (h.appended.map (·.1) ++ h.refused.map (·.1)) 0).2 r hr
  simp only [nextRun]
  omega

/-- The program a start leaves is the one that runs: what it reads of the journal is the records
recovery kept and the start. -/
theorem progAfter_eq (cfg : Config) (s : Fs) (h : Hist) (st : Store) (r : Nat) (rs : List Record)
    (ij : Ino)
    (hr : Running cfg s ⟨st.key, rs ++ [.start], ij, st.next, fun _ => none, none, true, true, r⟩
      h) :
    progAfter st s r =
      ⟨st.key, rs ++ [.start], ij, st.next, fun _ => none, none, true, true, r⟩ := by
  obtain ⟨d, hd, hseen, _, _⟩ := hr.synced rfl rfl
  have hne : (viewOf ⟨st.key, rs ++ [.start], ij, st.next, fun _ => none, none, true, true, r⟩
      h).phase ≠ .none := by simp [viewOf]
  obtain ⟨_, ij', d', _, hl', _, hd', hholds, _⟩ := hr.spool.journal hne
  rw [hr.lookup] at hl'
  cases hl'
  rw [hd] at hd'
  cases hd'
  have hst : Steady st.key (rs ++ [.start]) (· ∈ []) d := hholds
  have hscan := scan_encoded st.key hst.key _ hst.records
  simp only [progAfter, hr.lookup, Option.getD_some, hd, Option.map_some, hseen, hscan]
  rfl

/-- A start's operations done in turn, as many as one likes. -/
theorem reach_start (cfg : Config) (s : Fs) (h : Hist) (b : Nat)
    (hr : Reach cfg s (.starting s 0) h b) :
    ∀ n, n ≤ (startOps cfg s).length →
      Reach cfg (s.run ((startOps cfg s).take n)) (.starting s n) h b
  | 0, _ => by simpa [Fs.run] using hr
  | n + 1, hn => by
    rw [run_take_succ s _ n (by omega)]
    exact .startStep _ _ _ _ _ _ (reach_start cfg s h b hr n (by omega)) (by omega)

/-- What a run keeps gives a spool as the history knows it, under the bound. -/
theorem good_spool (cfg : Config) (s : Fs) (proc : Proc) (h : Hist) (b : Nat)
    (hg : Good cfg s proc h b) : Unrefused h ∧ ∃ ph n, n ≤ b ∧ Spool cfg s (histView h ph n) := by
  cases proc with
  | down => exact hg
  | starting s₀ k =>
    obtain ⟨hkey, hu, ph, m, hmb, hroom, hsp, ht, hra, hk, rfl⟩ := hg
    obtain ⟨_, _, _, _, _, hsafe, _⟩ := start_safe cfg hkey s₀ _ hsp ht hra hroom
    obtain ⟨⟨ph', n', hn', hsp'⟩, _⟩ := safe_point _ _ s₀ _ k hsafe hk
    have : n' ≤ m + 1 := hn'
    exact ⟨hu, ph', n', by omega, hsp'⟩
  | up p =>
    obtain ⟨hr, hb⟩ := hg
    exact ⟨hr.apart, _, p.next, by omega, hr.spool⟩

/-! ## Every run keeps it -/

/-- **Every step of a run keeps what a run keeps.** -/
theorem reach_good (cfg : Config) (s : Fs) (proc : Proc) (h : Hist) (b : Nat)
    (hr : Reach cfg s proc h b) : Good cfg s proc h b := by
  induction hr with
  | init cfg => exact ⟨(fun r c hc => by cases hc), .none, 1, Nat.le_refl _, spool_empty cfg⟩
  | crash cfg s proc h b t _ hc ha ih =>
    obtain ⟨hu, ph, n, hn, hsp⟩ := good_spool cfg s proc h b ih
    obtain ⟨ph', hsp'⟩ := crash_spool cfg s t _ hsp hc ha
    exact ⟨hu, ph', n, hn, hsp'⟩
  | stop cfg s proc h b _ ih => exact good_spool cfg s proc h b ih
  | begin cfg cfg' s h b _ hkey hg ht ha hb ih =>
    obtain ⟨hu, ph, n, hn, hsp⟩ := ih
    have hsp' := spool_config cfg cfg' hg s _ hsp
    exact ⟨hkey, hu, ph, n, by omega, by omega, hsp', ht, restartAssumed_of cfg' s _ hsp' ha,
      Nat.zero_le _, by simp [Fs.run]⟩
  | startStep cfg s s₀ k h b _ hk ih =>
    obtain ⟨hkey, hu, ph, m, hmb, hroom, hsp, ht, hra, _, rfl⟩ := ih
    exact ⟨hkey, hu, ph, m, hmb, hroom, hsp, ht, hra, hk, (run_take_succ s₀ _ k hk).symm⟩
  | startFails cfg s s₀ k h b t _ hk hf ih =>
    obtain ⟨hkey, hu, ph, m, hmb, hroom, hsp, ht, hra, _, rfl⟩ := ih
    obtain ⟨_, _, _, _, _, hsafe, _⟩ := start_safe cfg hkey s₀ _ hsp ht hra hroom
    obtain ⟨⟨ph', n', hn', hsp'⟩, _⟩ := safe_fail _ _ s₀ _ k hk t hsafe hf
    have : n' ≤ m + 1 := hn'
    exact ⟨hu, ph', n', by omega, hsp'⟩
  | started cfg s s₀ h b st acts _ hrec ih =>
    obtain ⟨hkey, hu, ph, m, _, hroom, hsp, ht, hra, _, rfl⟩ := ih
    obtain ⟨_, st', acts', hrec', _, _, hst⟩ := start_safe cfg hkey s₀ _ hsp ht hra hroom
    rw [hrec] at hrec'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrec'
    obtain ⟨rfl, rfl⟩ := hrec'
    rw [List.take_length]
    obtain ⟨rs, ij, _, _, hrun⟩ := running_started cfg st _ h (nextRun h) hst hu
      fun r q hq => lt_nextRun h r (by
        rcases hq with hq | ⟨c, hc, _⟩
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨(r, q), hq, rfl⟩)
        · exact List.mem_append_left _ (List.mem_map.mpr ⟨(r, c), hc, rfl⟩))
    rw [progAfter_eq cfg _ h st (nextRun h) rs ij hrun]
    exact ⟨hrun, rfl⟩
  | step cfg s p h b s' p' h' _ hs ih =>
    exact ⟨running_step cfg s p h ih.1 s' p' h' hs, rfl⟩

/-! ## The store -/

/-- **The store is crash safe.** A crash at any point of any run, under `CrashAssumed`, recovers
without corruption under the next start's configuration: every article answered 240, and only
commits a run appended for an article it did not refuse, each with its octets and the CRC-32C its
record gives. The octets are those of the number's last reservation: a number is reserved again
only once no record and no name carries it (`recover_next`). -/
theorem store_safe (cfg cfg' : Config) (s : Fs) (proc : Proc) (h : Hist) (b : Nat)
    (hr : Reach cfg s proc h b) (t : Fs) (hc : Crash s t) (ha : CrashAssumed s t)
    (hkey : cfg'.key.length = keyLength) (hg : cfg.groups ⊆ cfg'.groups) :
    ∃ st ops, recover cfg' (image t) = .ok (st, ops) ∧ (∀ c ∈ h.answered, c ∈ st.articles) ∧
      ∀ c ∈ st.articles, (∃ r, (r, c) ∈ h.appended ∧ (r, c.seq) ∉ h.refused) ∧
        (image t).lookup (finalName c.seq) = some (h.files c.seq) ∧
        (crc32c (h.files c.seq)).toNat = c.fileCrc := by
  obtain ⟨hu, ph, n, _, hsp⟩ := good_spool cfg s proc h b (reach_good cfg s proc h b hr)
  have hsp' := spool_config cfg cfg' hg s _ hsp
  obtain ⟨st, ops, _, hrec, ⟨hans, hart⟩, _⟩ := spool_crash cfg' hkey s _ hsp' t hc
    (assumed_of cfg' s t _ hsp' hc ha)
  refine ⟨st, ops, hrec, hans, fun c hc => ⟨?_, (hart c hc).2.1, (hart c hc).2.2⟩⟩
  obtain ⟨⟨r, c'⟩, hm, rfl⟩ := List.mem_map.mp (hart c hc).1
  exact ⟨r, hm, hu r c' hm⟩

/-- **While the store runs, it serves every article answered**: each among the records the program
keeps, its file in place with the octets written for it. -/
theorem store_serves (cfg : Config) (s : Fs) (p : Prog) (h : Hist) (b : Nat)
    (hr : Reach cfg s (.up p) h b) :
    ∀ c ∈ h.answered, c ∈ commitsOf p.records ∧ Placed s h.files c := by
  intro c hc
  have hrun := (reach_good cfg s (.up p) h b hr).1
  have hk : c ∈ commitsOf p.records := hrun.spool.answered c hc
  refine ⟨hk, hrun.spool.placed c ?_⟩
  simp only [viewOf, Phase.kept, Phase.back, commitsOf, List.filterMap_append, List.mem_append]
  exact Or.inl hk

/-! ## The premises can hold -/

/-- The premise `CrashAssumed` can hold: of the crash of the examples' spool that left the commit
of article 2 torn. -/
theorem crashAssumed_witness : CrashAssumed wSpool wCrash := by
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
  obtain ⟨hs, _, hseen, _, _⟩ := jSynced_steady
  have hk : wJournal.kept = journal sampleKey wRecords := by
    show jSynced.kept = _; rw [hs.kept]
  refine ⟨fun h0 => ?_, fun k _ _ => unforged_near _ _ _ ?_⟩
  · exfalso
    rw [hk] at h0
    have := journal_length sampleKey sampleKey_length wRecords
    rw [h0] at this
    exact absurd this (by decide)
  · simp only [Data.after, wLeft, wJournal, Data.append, List.length_append, List.length_take,
      headerLength, hs.kept, hseen]
    omega

/-- A journal whose format is written and not synced. -/
def wCreating : Fs :=
  ⟨[⟨journalName, some 0, []⟩], [(0, Data.empty.append (journal sampleKey []))], 1, true⟩

/-- The premise `CrashAssumed` can hold where nothing of the journal is kept: of a crash that left
the format whole. -/
theorem crashAssumed_creating_witness :
    CrashAssumed wCreating (wCreating.crashWith ⟨[some 0], [journal sampleKey []]⟩) := by
  intro i d d' hl hd hd'
  have hl0 : (wCreating.crashWith ⟨[some 0], [journal sampleKey []]⟩).lookup journalName =
      some 0 := by decide
  rw [hl0] at hl
  cases hl
  have hd0 : wCreating.data 0 = some (Data.empty.append (journal sampleKey [])) := rfl
  rw [hd0] at hd
  cases hd
  have hd'0 : (wCreating.crashWith ⟨[some 0], [journal sampleKey []]⟩).data 0 =
      some ((Data.empty.append (journal sampleKey [])).after (journal sampleKey [])) := rfl
  rw [hd'0] at hd'
  cases hd'
  refine ⟨fun _ => formatWritten_append Data.empty rfl _, fun k _ hk => ?_⟩
  have h0 := hk.length_le
  rw [encode_length] at h0
  simp [Data.append, Data.empty, headerLength] at h0

/-- The premise `StartAssumed` can hold: of the examples' spool whose journal's append of the commit
of article 2 failed after three octets. -/
theorem startAssumed_witness : StartAssumed wFailed := by
  intro i d hl hd k _ _
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

/-- The premises `Reach` and `Good` can hold: of an empty directory. -/
theorem good_witness : Reach sampleConfig Fs.empty .down Hist.empty 1 ∧
    Good sampleConfig Fs.empty .down Hist.empty 1 :=
  ⟨.init _, reach_good sampleConfig _ _ _ _ (.init _)⟩

/-- A run reaches the store running: from an empty directory, a start done. -/
theorem up_witness : ∃ s p h b, Reach sampleConfig s (.up p) h b := by
  have r1 := Reach.begin sampleConfig sampleConfig _ _ _ (.init _) sampleKey_length
    (List.Subset.refl _) ⟨rfl, fun _ _ hi _ => by cases hi⟩ (fun _ _ hi _ => by cases hi)
    (by decide)
  have r2 := reach_start _ _ _ _ r1 _ (Nat.le_refl _)
  have he : image (startSyncs Fs.empty) = [] := by decide
  obtain ⟨st, acts, hrec⟩ : ∃ st acts,
      recover sampleConfig (image (startSyncs Fs.empty)) = .ok (st, acts) := by
    rw [he]; exact ⟨_, _, recover_empty sampleConfig sampleKey_length⟩
  exact ⟨_, _, _, _, .started _ _ _ _ _ st acts r2 hrec⟩

/-! ## Examples -/

/-- `Trusted`, computed. -/
def trusted (s : Fs) : Bool :=
  s.dirTrusted && match s.lookup journalName with
    | some i => match s.data i with
      | some d => d.trusted
      | none => true
    | none => true

theorem trusted_sound (s : Fs) (h : trusted s = true) : Trusted s := by
  simp only [trusted, Bool.and_eq_true] at h
  refine ⟨h.1, fun i d hi hd => ?_⟩
  have h2 := h.2
  simp only [hi, hd] at h2
  exact h2

/-- Whether a start may assume what `StartAssumed` says, `k` the journal's key: nothing past what is
kept, or the format's frame under `k` kept and no frame forged past it (`unforged`). -/
def startChecked (k : Bytes) (s : Fs) : Bool :=
  match s.lookup journalName with
  | some i => match s.data i with
    | some d => decide (d.seen.length ≤ d.kept.length) ||
        ((Record.format k).encode k 0).isPrefixOf d.kept && unforged k d d.seen
    | none => true
  | none => true

theorem startChecked_sound (k : Bytes) (hk : k.length = keyLength) (s : Fs)
    (h : startChecked k s = true) : StartAssumed s := by
  intro i d hi hd k' hk' hp
  simp only [startChecked, hi, hd, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    List.isPrefixOf_iff_prefix] at h
  rcases h with h | ⟨hf, hu⟩
  · exact unforged_kept k' d d.seen h
  · rw [format_key_unique k' k d.kept hk' hk hp hf]
    exact (unforged_iff k d d.seen).mp hu

/-- Whether a start may begin on `s`, `k` the journal's key: `Trusted` and `StartAssumed`. -/
def startable (k : Bytes) (s : Fs) : Bool := trusted s && startChecked k s

/-- The store a start on `s` under `cfg` leaves, the history `h` and the run `r`. -/
def startOn (cfg : Config) (s : Fs) (h : Hist) (r : Nat) : Option St :=
  match recover cfg (image (startSyncs s)) with
  | .ok (st, _) =>
    let u := s.run (startOps cfg s)
    some ⟨u, progAfter st u r, h⟩
  | .error _ => none

/-- **The starts the examples make are starts of a run**, what `startable` checks holding. -/
theorem reach_startOn (cfg cfg' : Config) (s : Fs) (h : Hist) (b : Nat) (k : Bytes) (z : St)
    (hr : Reach cfg s .down h b) (hkey : cfg'.key.length = keyLength)
    (hg : cfg.groups ⊆ cfg'.groups) (hk : k.length = keyLength) (hs : startable k s = true)
    (hb : b + 2 < 2 ^ 64) (hz : startOn cfg' s h (nextRun h) = some z) :
    Reach cfg' z.fs (.up z.prog) z.hist z.prog.next := by
  simp only [startable, Bool.and_eq_true] at hs
  have r1 := Reach.begin cfg cfg' s h b hr hkey hg (trusted_sound s hs.1)
    (startChecked_sound k hk s hs.2) hb
  have r2 := reach_start cfg' s h (b + 1) r1 _ (Nat.le_refl _)
  rw [List.take_length] at r2
  unfold startOn at hz
  split at hz
  · rename_i st acts hrec
    cases hz
    exact .started cfg' _ s h _ st acts r2 hrec
  · cases hz

/-- **The commands the examples run, each allowed where it is run, are steps of a run.** -/
theorem reach_script (cfg : Config) : ∀ (x : St) (cs : List Cmd) (b : Nat),
    Reach cfg x.fs (.up x.prog) x.hist b → allowedRun cfg x cs = true →
    ∃ b', Reach cfg (cs.foldl St.after x).fs (.up (cs.foldl St.after x).prog)
      (cs.foldl St.after x).hist b'
  | _, [], b, hr, _ => ⟨b, hr⟩
  | x, c :: cs, _, hr, h => by
    simp only [allowedRun, Bool.and_eq_true] at h
    exact reach_script cfg (x.after c) cs _
      (.step cfg _ _ _ _ _ _ _ hr (after_step cfg x c (allowed_sound cfg x c h.1))) h.2

/-- What the examples leave of a failure of an allowed command is a point of a run. -/
theorem reach_fails (cfg : Config) (x : St) (c : Cmd) (b : Nat)
    (hr : Reach cfg x.fs (.up x.prog) x.hist b) (h : c.allowed cfg x = true) (u : St)
    (hu : u ∈ x.fails c) : Reach cfg u.fs (.up u.prog) u.hist u.prog.next :=
  .step cfg _ _ _ _ _ _ _ hr (fails_step cfg x c (allowed_sound cfg x c h) u hu)

/-- Whether every crash `liteCrashes` lists, at every point of the start on `s` under `cfg` and of
whatever any of its operations leaves when it fails, recovers as `recoversAll` asks of the history
`h`. -/
def startsAll (cfg : Config) (s : Fs) (h : Hist) : Bool :=
  (reached s (startOps cfg s)).all fun u => recoversAll cfg ⟨u, startSt.prog, h⟩

/-- What a crash leaves when it loses all it may: each name as the directory's last sync left it,
each file with what is kept. -/
def lossy (s : Fs) : Fs := s.crashWith ⟨s.dir.map (·.synced), s.files.map (·.2.kept)⟩

/-- Whether a start after `u` begins as `Reach` asks and recovers as `recoversAll` asks, and a run
after it answers one more article, recovering so throughout. -/
def restarts (u : St) : Bool :=
  startable sampleKey u.fs && startsAll sampleConfig u.fs u.hist &&
    match startOn sampleConfig u.fs u.hist (nextRun u.hist) with
    | some z =>
      let q := z.prog.next
      let more : List Cmd := [.reserve bodyB, .create q, .write q 100, .sync q, .rename q,
        .place q, .commit q (commitFor q 2 bodyB), .publish]
      allowedRun sampleConfig z more && (runOn z more).all (recoversAll sampleConfig) &&
        (more.foldl St.after z).hist.answered.contains (commitFor q 2 bodyB)
    | none => false

/-- **Runs and starts again**: a start; a run answers article 1 and stops with article 2 written in
part; a start removes article 2's file; a run under another number answers article 3; a crash that
loses all it may, and a start finds articles 1 and 3. Also starts after a torn append of a commit
and after a failed sync of an article's file, each followed by a run that answers an article. Every
start and command is checked against `Reach`; every listed crash at every point and failure
recovers as `recoversAll` asks. -/
def regression_924 (_ : Unit) : Bool :=
  let c1 := commitFor 1 1 body
  let placing : List Cmd := [.reserve body, .create 1, .write 1 100, .sync 1, .rename 1, .place 1]
  let first : List Cmd := placing ++ [.commit 1 c1, .publish, .reserve bodyB, .create 2, .write 2 5]
  let written : List Cmd := [.reserve body, .create 1, .write 1 100]
  match startOn sampleConfig Fs.empty Hist.empty (nextRun Hist.empty) with
  | none => false
  | some x =>
    let y := first.foldl St.after x
    let placed := placing.foldl St.after x
    let unsynced := written.foldl St.after x
    match startOn sampleConfig y.fs y.hist (nextRun y.hist) with
    | none => false
    | some z =>
      let c3 := commitFor z.prog.next 2 bodyB
      let second : List Cmd := [.reserve bodyB, .create 3, .write 3 100, .sync 3, .rename 3,
        .place 3, .commit 3 c3, .publish]
      let w := second.foldl St.after z
      startable sampleKey Fs.empty && startable sampleKey y.fs &&
        startable sampleKey (lossy w.fs) && allowedRun sampleConfig x first &&
        allowedRun sampleConfig z second && z.prog.next == 3 && z.prog.run != x.prog.run &&
        (z.fs.lookup (tempName 2)).isNone && startsAll sampleConfig Fs.empty Hist.empty &&
        (runOn x first).all (recoversAll sampleConfig) && startsAll sampleConfig y.fs y.hist &&
        (runOn z second).all (recoversAll sampleConfig) && w.hist.answered == [c1, c3] &&
        startsAll sampleConfig (lossy w.fs) w.hist &&
        articlesOf (recover sampleConfig (image (startSyncs (lossy w.fs)))) == some [c1, c3] &&
        (Cmd.commit 1 c1).allowed sampleConfig placed &&
        (placed.fails (.commit 1 c1)).all restarts &&
        allowedRun sampleConfig x written && (Cmd.sync 1).allowed sampleConfig unsynced &&
        (unsynced.fails (.sync 1)).all fun u =>
          restarts u && (Cmd.clean 1 false).allowed sampleConfig u &&
            restarts (u.after (.clean 1 false))

/-- **Why a run's number is above those before**: a run refuses article 1 and stops; after a start
the number is free, and the next run answers another article as 1. Under a fresh number every crash
recovers as `recoversAll` asks; under the refusing run's number a crash finds article 1 appended by
the run that refused it. -/
def regression_925 (_ : Unit) : Bool :=
  let first : List Cmd := [.reserve body, .create 1, .write 1 100, .refuse 1, .clean 1 false,
    .drop 1]
  let c1 := commitFor 1 1 bodyB
  let second : List Cmd := [.reserve bodyB, .create 1, .write 1 100, .sync 1, .rename 1,
    .place 1, .commit 1 c1, .publish]
  match startOn sampleConfig Fs.empty Hist.empty (nextRun Hist.empty) with
  | none => false
  | some x =>
    let y := first.foldl St.after x
    match startOn sampleConfig y.fs y.hist (nextRun y.hist),
        startOn sampleConfig y.fs y.hist x.prog.run with
    | some z, some z' =>
      allowedRun sampleConfig x first && startable sampleKey y.fs &&
        allowedRun sampleConfig z second && z.prog.next == 1 &&
        (runOn z second).all (recoversAll sampleConfig) &&
        !(runOn z' second).all (recoversAll sampleConfig)
    | _, _ => false

/-- Another key of sixteen octets. -/
def keyB : Bytes := (List.range 16).map fun n => BitVec.ofNat 8 (n + 100)

/-- **Each start under its own configuration**: a journal whose name a crash lost before the
directory's sync is created again under another key, in another file; a run answers article 1; a
start under a third key with a group added keeps the journal's key; a run answers article 2 in that
group; after a crash that loses all it may, a start finds both. Checked against `Reach` and
`recoversAll` throughout. A start without that group finds the store corrupt. -/
def regression_926 (_ : Unit) : Bool :=
  let more := ascii "local.more"
  let cfgB : Config := ⟨sampleConfig.groups, keyB⟩
  let cfgC : Config := ⟨sampleConfig.groups ++ [more], sampleKey⟩
  let u := Fs.empty.run ((startOps sampleConfig Fs.empty).take 4)
  let c1 := commitFor 1 1 body
  let c2 := { commitFor 2 1 bodyB with groups := [⟨more, 1⟩] }
  let first : List Cmd := [.reserve body, .create 1, .write 1 100, .sync 1, .rename 1, .place 1,
    .commit 1 c1, .publish]
  let second : List Cmd := [.reserve bodyB, .create 2, .write 2 100, .sync 2, .rename 2, .place 2,
    .commit 2 c2, .publish]
  match startOn cfgB (lossy u) Hist.empty (nextRun Hist.empty) with
  | none => false
  | some x =>
    let y := first.foldl St.after x
    match startOn cfgC y.fs y.hist (nextRun y.hist) with
    | none => false
    | some z =>
      let w := second.foldl St.after z
      let last := image (startSyncs (lossy w.fs))
      startable sampleKey Fs.empty && (u.lookup journalName).isSome &&
        (lossy u).dir.isEmpty && startable keyB (lossy u) &&
        startsAll cfgB (lossy u) Hist.empty && x.prog.journal == 1 && x.prog.key == keyB &&
        allowedRun cfgB x first && (runOn x first).all (recoversAll cfgB) &&
        startable keyB y.fs && startsAll cfgC y.fs y.hist && z.prog.key == keyB &&
        allowedRun cfgC z second && (runOn z second).all (recoversAll cfgC) &&
        w.hist.answered == [c1, c2] && startable keyB (lossy w.fs) &&
        startsAll cfgC (lossy w.fs) w.hist && articlesOf (recover cfgC last) == some [c1, c2] &&
        match recover cfgB last with
        | .error _ => true
        | .ok _ => false

end DN.News.StoreRun
