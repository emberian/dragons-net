-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverSpec

/-!
# DN.News.RecoverDrive

Recovery's steps, the host reading directory `img`, find what `Recovery.recover` does (`drives_recover`) and nothing
else (`drives_det`). This holds from any area whose phase is 0. Each phase has its lemma: `first_ok`, `scan_drives`,
`files_drives`, `tail_drives`, `second_drives` and the rest.
-/

namespace DN.News.RecoverSpec

open DN.News.Journal DN.News.Recovery
open DN.News.ScanRun (St stepSpec Valid valid_start scan_first scanFrom_ok)

variable {cfg : Config} {img : Image} {J : Bytes}

/-! ## Steps and drives, phase by phase -/

/-- A step ends in one state with one output. -/
theorem steps_det {r r1 r2 : RSt} {o1 o2 : ROut} (h1 : Steps cfg J r r1 o1) (h2 : Steps cfg J r r2 o2) :
    r1 = r2 ∧ o1 = o2 := by
  induction h1 with
  | out e1 =>
    cases h2 with
    | out e2 => rw [e1] at e2; cases e2; exact ⟨rfl, rfl⟩
    | go e2 _ => rw [e1] at e2; cases e2
  | go e1 _ ih =>
    cases h2 with
    | out e2 => rw [e1] at e2; cases e2
    | go e2 h2' => rw [e1] at e2; cases e2; exact ih h2'

/-- **What recovery finds is one**: steps the host answers come to one finding at most. -/
theorem drives_det {r : RSt} {h : Host} {x y : Except Fault (Store × List Action)} (hx : Drives cfg img J r h x)
    (hy : Drives cfg img J r h y) : x = y := by
  induction hx with
  | done s1 =>
    cases hy with
    | done s2 => obtain ⟨rfl, -⟩ := steps_det s1 s2; rfl
    | refused s2 => cases (steps_det s1 s2).2
    | next s2 he _ => obtain ⟨-, rfl⟩ := steps_det s1 s2; cases he
  | refused s1 =>
    cases hy with
    | done s2 => cases (steps_det s1 s2).2
    | refused s2 => cases (steps_det s1 s2).2; rfl
    | next s2 he _ => obtain ⟨-, rfl⟩ := steps_det s1 s2; cases he
  | next s1 he1 _ ih =>
    cases hy with
    | done s2 => obtain ⟨-, rfl⟩ := steps_det s1 s2; cases he1
    | refused s2 => obtain ⟨-, rfl⟩ := steps_det s1 s2; cases he1
    | next s2 _ hd => obtain ⟨rfl, rfl⟩ := steps_det s1 s2; exact ih hd

/-- A phase that asks or gives nothing. -/
theorem drives_go {r r' : RSt} {h : Host} {x : Except Fault (Store × List Action)}
    (hp : phase cfg J r = (r', none)) (hd : Drives cfg img J r' h x) : Drives cfg img J r h x := by
  cases hd with
  | done s => exact .done (.go hp s)
  | refused s => exact .refused (.go hp s)
  | next s he hn => exact .next (.go hp s) he hn

/-- A phase that asks or gives, the host answering. -/
theorem drives_out {r r' : RSt} {h : Host} {o : ROut} {x : Except Fault (Store × List Action)}
    (hp : phase cfg J r = (r', some o)) (he : o.ends = false)
    (hd : Drives cfg img J (answer cfg img J r' h o).1 (answer cfg img J r' h o).2 x) : Drives cfg img J r h x :=
  .next (.out hp) he hd

/-- A phase that is done. -/
theorem drives_done {r r' : RSt} {h : Host} (hp : phase cfg J r = (r', some .done)) :
    Drives cfg img J r h (.ok (storeAt cfg r' h, h.acts)) :=
  .done (.out hp)

/-- A phase that refuses. -/
theorem drives_refused {r r' : RSt} {h : Host} {e : Fault} (hp : phase cfg J r = (r', some (.refused e))) :
    Drives cfg img J r h (.error e) :=
  .refused (.out hp)

/-! ## Phases one at a time -/

section Phases
variable {r : RSt}

/-- Phase 0 is `begin`. -/
theorem phase_begin (h : r.phase = 0) : phase cfg J r = begin r := by unfold phase; rw [h]

/-- Phase 1 is `firstPass`. -/
theorem phase_firstPass (h : r.phase = 1) : phase cfg J r = firstPass r := by unfold phase; rw [h]

/-- Phase 2 is `journalGiven`. -/
theorem phase_journalGiven (h : r.phase = 2) : phase cfg J r = journalGiven r := by unfold phase; rw [h]

/-- Phase 3 is `scanning`. -/
theorem phase_scanning (h : r.phase = 3) : phase cfg J r = scanning cfg J r := by unfold phase; rw [h]

/-- Phase 4 is `rules`. -/
theorem phase_rules (h : r.phase = 4) : phase cfg J r = rules r := by unfold phase; rw [h]

/-- Phase 5 is `files`. -/
theorem phase_files (h : r.phase = 5) : phase cfg J r = files r := by unfold phase; rw [h]

/-- Phase 6 is `numbered`. -/
theorem phase_numbered (h : r.phase = 6) : phase cfg J r = numbered r := by unfold phase; rw [h]

/-- Phase 7 is `tail`. -/
theorem phase_tail (h : r.phase = 7) : phase cfg J r = tail r := by unfold phase; rw [h]

/-- Phase 8 is `secondPass`. -/
theorem phase_secondPass (h : r.phase = 8) : phase cfg J r = secondPass r := by unfold phase; rw [h]

/-- Phase 9 is `asideGiven`. -/
theorem phase_asideGiven (h : r.phase = 9) : phase cfg J r = asideGiven r := by unfold phase; rw [h]

/-- Phase 10 is `created`. -/
theorem phase_created (h : r.phase = 10) : phase cfg J r = created r := by unfold phase; rw [h]

/-- Phase 11 is `finish`. -/
theorem phase_finish (h : r.phase = 11) : phase cfg J r = finish r := by unfold phase; rw [h]

/-- Phase 12 is `renamed`. -/
theorem phase_renamed (h : r.phase = 12) : phase cfg J r = renamed r := by unfold phase; rw [h]

/-- Phase 13 is `askNext`. -/
theorem phase_askNext (h : r.phase = 13) : phase cfg J r = askNext r := by unfold phase; rw [h]

/-- A phase past 12 is `askNext`. -/
theorem phase_late (h : 13 ≤ r.phase) : phase cfg J r = askNext r := by
  unfold phase; split <;> first | rfl | omega

end Phases

/-! ## The first pass -/

/-- What the first pass found of the names `ns`, kept while the journal is read. -/
structure FPK (ns : List Name) (r : RSt) : Prop where
  names : r.names = ns.length
  journal : r.journal = ns.contains .journal
  maxSeq : r.maxSeq = (ns.filterMap seqOf).foldl max 0
  tails : r.tails = !(ns.filterMap tailOf).isEmpty
  maxTail : r.maxTail = (ns.filterMap tailOf).foldl max 0
  torn : r.torn = false
  fresh : r.fresh = false
  tidied : r.tidied = 0
  wait : r.wait = false

/-- What the first pass keeps of the names `ns`, and the rest as recovery starts. -/
structure FP (ns : List Name) (r : RSt) : Prop extends FPK ns r where
  commits : r.commits = []
  records : r.records = 0
  unknown : r.unknown = none

/-- A name of the first pass read. -/
theorem fp_snoc {ns : List Name} {r : RSt} (h : FP ns r) (n : Name) :
    FP (ns ++ [n]) { firstName { r with names := r.names + 1 } n with first := false } := by
  cases n <;> exact ⟨⟨by simp [firstName, h.names], by simp [firstName, h.journal],
    by simp [firstName, h.maxSeq, seqOf, List.foldl_append],
    by simp [firstName, h.tails, tailOf], by simp [firstName, h.maxTail, tailOf, List.foldl_append],
    by simp [firstName, h.torn], by simp [firstName, h.fresh], by simp [firstName, h.tidied],
    by simp [firstName, h.wait]⟩, by simp [firstName, h.commits], by simp [firstName, h.records],
    by simp [firstName, h.unknown]⟩

/-- The host's next name, `c` names in. -/
theorem answer_name {r : RSt} {h : Host} {c : Nat} (hc : (if r.first then 0 else h.cursor) = c) :
    answer cfg img J r h .askName = match img[c]? with
      | none => ({ r with ended := true }, { h with cursor := c })
      | some p => ({ r with ended := false, name := p.1 }, { h with cursor := c + 1 }) := by
  subst hc; rfl

/-- The directory's names from `k` on: the next one, and the rest. -/
theorem drop_cons {k : Nat} {p : Bytes × Bytes} {suf : Image} (hd : img.drop k = p :: suf) :
    img[k]? = some p ∧ k + 1 ≤ img.length ∧ img.drop (k + 1) = suf := by
  refine ⟨by rw [← List.head?_drop, hd]; rfl, ?_, by rw [← List.drop_drop, hd]; rfl⟩
  have := congrArg List.length hd; simp only [List.length_drop, List.length_cons] at this; omega

/-- The directory's names from `k` on, none left: `k` is how many it holds. -/
theorem drop_nil {k : Nat} (hd : img.drop k = []) (hle : k ≤ img.length) : img.length = k := by
  have := congrArg List.length hd; simp only [List.length_drop, List.length_nil] at this; omega

/-- Names that all read: the first, and the rest. -/
theorem mapM_cons_ok {p : Bytes × Bytes} {suf : Image} {ms : List Name} (h : (p :: suf).mapM nameOf = .ok ms) :
    ∃ n ms', parseName p.1 = some n ∧ suf.mapM nameOf = .ok ms' ∧ ms = n :: ms' := by
  simp only [List.mapM_cons, bind, Except.bind, nameOf] at h
  cases hp : parseName p.1 with
  | none => simp [hp, Option.elim] at h
  | some n =>
    simp only [hp, Option.elim] at h
    cases hs : suf.mapM nameOf with
    | error f => simp [hs] at h
    | ok ms' =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨n, ms', rfl, rfl, h.symm⟩

/-- Names one of which does not read: the first, or one of the rest. -/
theorem mapM_cons_error {p : Bytes × Bytes} {suf : Image} {f : Fault} (h : (p :: suf).mapM nameOf = .error f) :
    (parseName p.1 = none ∧ f = .badName p.1) ∨ ∃ n, parseName p.1 = some n ∧ suf.mapM nameOf = .error f := by
  simp only [List.mapM_cons, bind, Except.bind, nameOf] at h
  cases hp : parseName p.1 with
  | none => simp only [hp, Option.elim, Except.error.injEq] at h; exact .inl ⟨rfl, h.symm⟩
  | some n =>
    simp only [hp, Option.elim] at h
    cases hs : suf.mapM nameOf with
    | ok _ => simp [hs, pure, Except.pure] at h
    | error f' => simp only [hs, Except.error.injEq] at h; exact .inr ⟨n, rfl, by rw [h]⟩

/-- Where the host's next name is, the first pass `ns.length` names in. -/
theorem cursor_first {r : RSt} {ns : List Name} (h : r.first = ns.isEmpty) :
    (if r.first then 0 else ns.length) = ns.length := by
  split
  · rename_i e; rw [h] at e; rw [List.isEmpty_iff.mp e]; rfl
  · rfl

/-- A name of the first pass that reads: the next one asked for, what the pass keeps one name on. -/
theorem first_next {ns : List Name} {r : RSt} {p : Bytes × Bytes} {n : Name} (h : FP ns r) (hph : r.phase = 1)
    (hp : parseName p.1 = some n) :
    ∃ r2, phase cfg J { r with ended := false, name := p.1 } = (r2, some .askName) ∧ FP (ns ++ [n]) r2 ∧
      r2.phase = 1 ∧ r2.first = (ns ++ [n]).isEmpty :=
  ⟨_, by rw [phase_firstPass (r := { r with ended := false, name := p.1 }) hph, firstPass]; simp [hp],
    fp_snoc (r := { r with ended := false, name := p.1 }) { h with } n,
    by cases n <;> simpa [firstName] using hph, by simp⟩

/-- **The first pass** over names that all parse ends with what it keeps of them all. -/
theorem first_ok {x : Except Fault (Store × List Action)} :
    ∀ (suf : Image) (ns ms : List Name) (r : RSt), FP ns r →
    r.phase = 1 → r.first = ns.isEmpty → ns.length ≤ img.length → img.drop ns.length = suf →
    suf.mapM nameOf = .ok ms →
    (∀ r', FP (ns ++ ms) r' → r'.phase = 1 → r'.ended = true →
      Drives cfg img J r' ⟨img.length, [], []⟩ x) →
    Drives cfg img J (answer cfg img J r ⟨ns.length, [], []⟩ .askName).1
      (answer cfg img J r ⟨ns.length, [], []⟩ .askName).2 x
  | [], ns, ms, r, h, hph, hfi, hle, hd, hm, k => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm
    subst hm
    have hl := drop_nil hd hle
    rw [answer_name (h := ⟨ns.length, [], []⟩) (cursor_first hfi), List.getElem?_eq_none (by omega)]
    rw [hl, List.append_nil] at k
    exact k _ { h with } hph rfl
  | p :: suf, ns, ms, r, h, hph, hfi, hle, hd, hm, k => by
    obtain ⟨n, ms', hp, hs, rfl⟩ := mapM_cons_ok hm
    obtain ⟨hget, hl, hd'⟩ := drop_cons hd
    rw [answer_name (h := ⟨ns.length, [], []⟩) (cursor_first hfi), hget]
    dsimp only
    obtain ⟨r2, hp1, h', h2, h3⟩ := first_next (cfg := cfg) (J := J) h hph hp
    refine drives_out hp1 rfl ?_
    simpa using first_ok suf (ns ++ [n]) ms' r2 h' h2 h3 (by simpa using hl) (by simpa using hd') hs
      (by simpa using k)

/-- **The first pass** stops at the first name the store does not give. -/
theorem first_err {f : Fault} : ∀ (suf : Image) (ns : List Name) (r : RSt), FP ns r → r.phase = 1 →
    r.first = ns.isEmpty → ns.length ≤ img.length → img.drop ns.length = suf → suf.mapM nameOf = .error f →
    Drives cfg img J (answer cfg img J r ⟨ns.length, [], []⟩ .askName).1
      (answer cfg img J r ⟨ns.length, [], []⟩ .askName).2 (.error f)
  | [], _, _, _, _, _, _, _, hm => by simp [pure, Except.pure] at hm
  | p :: suf, ns, r, h, hph, hfi, hle, hd, hm => by
    obtain ⟨hget, hl, hd'⟩ := drop_cons hd
    rw [answer_name (h := ⟨ns.length, [], []⟩) (cursor_first hfi), hget]
    dsimp only
    rcases mapM_cons_error hm with ⟨hp, rfl⟩ | ⟨n, hp, hs⟩
    · exact drives_refused (r' := { r with ended := false, name := p.1 }) (by
        rw [phase_firstPass (r := { r with ended := false, name := p.1 }) hph, firstPass]; simp [hp])
    · obtain ⟨r2, hp1, h', h2, h3⟩ := first_next (cfg := cfg) (J := J) h hph hp
      refine drives_out hp1 rfl ?_
      simpa using first_err suf (ns ++ [n]) r2 h' h2 h3 (by simpa using hl) (by simpa using hd') hs

/-! ## A new store -/

/-- **A new journal**: created, the directory synced if it held no file, the store new. -/
theorem fresh_drives {r : RSt} {h : Host} (synced : Bool) (hc : r.commits = []) (ha : h.acts = [])
    (hs : h.aside = []) : Drives cfg img J (startNew r synced) h
      (.ok (fresh cfg, [.create cfg.key] ++ if synced then [.syncDir] else [])) := by
  refine drives_out (phase_created rfl) rfl ?_
  simp only [startNew, answer, actOf, ha, List.nil_append]
  cases synced with
  | true =>
    refine drives_out (phase_created rfl) rfl ?_
    simp only [answer, actOf]
    let r2 : RSt := { r with fresh := true, next := 1, journalEnd := firstFrame, i := 2, wait := true, phase := 10 }
    have := drives_done (cfg := cfg) (img := img) (J := J) (h := { h with acts := [.create cfg.key, .syncDir] })
      (phase_created (r := r2) rfl)
    simpa [r2, storeAt, fresh, hc, hs] using this
  | false =>
    let r1 : RSt := { r with fresh := true, next := 1, journalEnd := firstFrame, i := 1, wait := false, phase := 10 }
    have := drives_done (cfg := cfg) (img := img) (J := J) (h := { h with acts := [.create cfg.key] })
      (phase_created (r := r1) rfl)
    simpa [r1, storeAt, fresh, hc, hs] using this

/-! ## The journal read -/

/-- **A step of the scanner**, reading the journal from where it stands. It is at the end, stopped, a record read, or
octets wanted with nothing read. -/
theorem step_cases (st : St) (F : Nat) :
    (stepSpec J st = .clean ∧
      scanFrom spec (F + 1) (J.drop st.pos) st.pos st.key st.acc = ⟨st.acc.reverse, .clean⟩) ∨
    (∃ e, stepSpec J st = .stop e ∧
      scanFrom spec (F + 1) (J.drop st.pos) st.pos st.key st.acc = ⟨st.acc.reverse, e⟩) ∨
    (∃ rec st', stepSpec J st = .record rec st' ∧ st'.key = (st.key <|> rec.key) ∧ st'.acc = rec :: st.acc ∧
      scanFrom spec (F + 1) (J.drop st.pos) st.pos st.key st.acc =
        scanFrom spec F (J.drop st'.pos) st'.pos st'.key st'.acc) ∨
    (∃ st' n, stepSpec J st = .want st' n ∧ st'.pos = st.pos ∧ st'.key = st.key ∧ st'.acc = st.acc) := by
  by_cases h1 : J.length ≤ st.pos
  · refine .inl ⟨by simp [stepSpec, h1], ?_⟩
    rw [List.drop_eq_nil_of_le h1]; simp [scanFrom, next]
  by_cases h2 : st.base + st.len < st.pos + min (J.length - st.pos) maxFrame
  · exact .inr (.inr (.inr ⟨{ st with base := st.pos, len := st.base + st.len - st.pos },
      min ScanProg.chunk (J.length - (st.base + st.len)), by simp only [stepSpec, if_neg h1, if_pos h2], rfl, rfl,
      rfl⟩))
  cases hnx : next spec st.key st.pos (J.drop st.pos) with
  | done => exact .inl ⟨by simp only [stepSpec, if_neg h1, if_neg h2, hnx], by simp only [scanFrom, hnx]⟩
  | bad why =>
    exact .inr (.inl ⟨stop spec st.pos (J.drop st.pos) st.key why, by simp only [stepSpec, if_neg h1, if_neg h2, hnx],
      by simp only [scanFrom, hnx]⟩)
  | record rec taken rest =>
    by_cases h3 : (!st.acc.isEmpty && rec.key.isSome) = true
    · exact .inr (.inl ⟨.corrupt st.pos .formatAgain, by simp only [stepSpec, if_neg h1, if_neg h2, hnx, if_pos h3],
        by simp only [scanFrom, hnx, spec_formatOnce, Bool.true_and, if_pos h3]⟩)
    · obtain ⟨hrest, -⟩ := ScanRun.next_record hnx
      let st2 : St := { st with pos := st.pos + taken, key := st.key <|> rec.key, acc := rec :: st.acc }
      refine .inr (.inr (.inl ⟨rec, st2,
        by simp only [stepSpec, if_neg h1, if_neg h2, hnx, if_neg h3]; rfl, rfl, rfl, ?_⟩))
      simp only [scanFrom, hnx, spec_formatOnce, Bool.true_and, if_neg h3]
      rw [hrest, List.drop_drop]

/-- The first unknown group among the commits the index holds, one more read. -/
theorem unknown_snoc (cs : List Commit) (c : Commit) :
    unknownGroup? cfg ((cs ++ [c]).take capacity) =
      if cs.length + 1 ≤ capacity then unknownGroup? cfg (cs.take capacity) <|> unknownIn cfg c
      else unknownGroup? cfg (cs.take capacity) := by
  split
  · rename_i hc
    rw [List.take_of_length_le (by simpa using hc), List.take_of_length_le (by omega)]
    simp only [unknownGroup?, unknownIn, List.flatMap_append, List.flatMap_singleton, List.find?_append]
    cases (List.flatMap (·.groups) cs).find? (fun g => !cfg.groups.contains g.name) <;> rfl
  · rw [List.take_append_of_le_length (by omega)]

/-- The first key records carry, one more read. -/
theorem key_snoc (l : List Record) (rec : Record) :
    ((l ++ [rec]).filterMap Record.key).head? = ((l.filterMap Record.key).head? <|> rec.key) := by
  rw [List.filterMap_append, List.head?_append]
  cases (l.filterMap Record.key).head? <;> cases hk : rec.key <;> simp [hk]

/-- **The journal being read**: scanner state `st`, the records read counted, the commits noted. Also the first group
they carry the configuration lacks, and the key, the first one a record carries. -/
structure SC (cfg : Config) (J : Bytes) (ns : List Name) (st : St) (r : RSt) : Prop where
  phase : r.phase = 3
  scan : r.scan = st
  valid : Valid J st
  records : r.records = st.acc.length
  commits : r.commits = commitsOf st.acc.reverse
  unknown : r.unknown = unknownGroup? cfg ((commitsOf st.acc.reverse).take capacity)
  key : st.key = (st.acc.reverse.filterMap Record.key).head?
  jsize : r.jsize = J.length
  kept : FPK ns r

/-- The journal read to its end, clean or torn: what was read, and the end next. -/
structure EndSC (cfg : Config) (J : Bytes) (ns : List Name) (sc : Scan) (r : RSt) : Prop where
  kept : FPK ns r
  jsize : r.jsize = J.length
  records : r.records = sc.records.length
  commits : r.commits = commitsOf sc.records
  unknown : r.unknown = unknownGroup? cfg ((commitsOf sc.records).take capacity)
  key : r.scan.key = (sc.records.filterMap Record.key).head?
  phase : phase cfg J r = scanned r (cutOf sc.ending)

/-- **Reading the journal**, the host giving the octets wanted: corruption found, or the end with what was read. That is
as `scanFrom` reads it. -/
theorem scan_drives (ns : List Name) {h : Host} {x : Except Fault (Store × List Action)} : ∀ (f : Nat) (st : St)
    (F : Nat) (r : RSt), SC cfg J ns st r → st.left J < f → J.length - st.pos < F →
    (∀ p w, (scanFrom spec F (J.drop st.pos) st.pos st.key st.acc).ending = .corrupt p w →
      Drives cfg img J r h (.error (.journal p w))) ∧
    ((∀ p w, (scanFrom spec F (J.drop st.pos) st.pos st.key st.acc).ending ≠ .corrupt p w) →
      (∀ r', EndSC cfg J ns (scanFrom spec F (J.drop st.pos) st.pos st.key st.acc) r' → Drives cfg img J r' h x) →
      Drives cfg img J r h x)
  | 0, _, _, _, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | f + 1, st, F, r, hs, hf, hF => by
    obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    have hph := phase_scanning (cfg := cfg) (J := J) hs.phase
    rw [scanning] at hph
    rw [hs.scan] at hph
    have hend : ∀ e, stepSpec J st = .stop e → (∀ p w, e ≠ .corrupt p w) →
        EndSC cfg J ns ⟨st.acc.reverse, e⟩ r := fun e he hne => by
      refine ⟨hs.kept, hs.jsize, by rw [hs.records, List.length_reverse], hs.commits, hs.unknown,
        by rw [hs.scan]; exact hs.key, ?_⟩
      rw [hph, he]
      cases e with
      | clean => rfl
      | torn p => rfl
      | corrupt p w => exact absurd rfl (hne p w)
    rcases step_cases (J := J) st F with ⟨hst, hsc⟩ | ⟨e, hst, hsc⟩ | ⟨rec, st', hst, hk, ha, hsc⟩ |
      ⟨st', n, hst, hp, hk, ha⟩
    · rw [hsc]
      refine ⟨fun p w e => (by cases e), fun _ k => k r ⟨hs.kept, hs.jsize, by rw [hs.records, List.length_reverse],
        hs.commits, hs.unknown, by rw [hs.scan]; exact hs.key, by rw [hph, hst]; rfl⟩⟩
    · rw [hsc]
      refine ⟨fun p w he => ?_, fun hne k => k r (hend e hst fun p w => hne p w)⟩
      cases he
      exact drives_refused (by rw [hph, hst])
    · have hv' := ScanRun.valid_record hs.valid hst
      rw [hsc]
      have ih := scan_drives ns (h := h) (x := x) f st' F
        (recordRead cfg { r with scan := st', records := r.records + 1 } rec)
        (by
          refine ⟨by cases rec <;> exact hs.phase, by cases rec <;> rfl, hv'.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [ha]; cases rec <;> simp [recordRead, hs.records]
          · rw [ha, List.reverse_cons, commitsOf_append]; cases rec <;> simp [recordRead, hs.commits, commitsOf]
          · rw [ha, List.reverse_cons, commitsOf_append]
            cases rec with
            | commit c => simp only [recordRead, hs.commits, hs.unknown, unknown_snoc, commitsOf,
                List.filterMap_cons, List.filterMap_nil]
            | _ => simp [recordRead, hs.unknown, commitsOf]
          · rw [hk, ha, List.reverse_cons, key_snoc, hs.key]
          · cases rec <;> exact hs.jsize
          · cases rec <;> exact { hs.kept with })
        (by have := hv'.2.1; omega) (by have := hv'.2.2; omega)
      exact ⟨fun p w he => drives_go (by rw [hph, hst]) (ih.1 p w he),
        fun hne k => drives_go (by rw [hph, hst]) (ih.2 hne k)⟩
    · obtain ⟨hn, hm⟩ := ScanRun.valid_want hs.valid hst
      obtain ⟨hv', hl⟩ := hm n hn (Nat.le_refl _)
      have ih := scan_drives ns (h := h) (x := x) f (st'.fill n) (F + 1) { r with scan := st'.fill n }
        ⟨hs.phase, rfl, hv', by rw [hs.records]; simp [ScanRun.St.fill, ha],
          by simp [ScanRun.St.fill, ha, hs.commits],
          by simp [ScanRun.St.fill, ha, hs.unknown], by simp [ScanRun.St.fill, hk, ha, hs.key], hs.jsize,
          { hs.kept with }⟩
        (by omega) (by simp only [ScanRun.St.fill]; rw [hp]; exact hF)
      have e1 : scanFrom spec (F + 1) (J.drop st.pos) st.pos st.key st.acc =
          scanFrom spec (F + 1) (J.drop (st'.fill n).pos) (st'.fill n).pos (st'.fill n).key (st'.fill n).acc := by
        simp only [ScanRun.St.fill, hp, hk, ha]
      rw [e1]
      exact ⟨fun p w he => drives_out (r' := { r with scan := st' }) (o := .askOctets n) (by rw [hph, hst]) rfl
        (ih.1 p w he), fun hne k => drives_out (r' := { r with scan := st' }) (o := .askOctets n)
          (by rw [hph, hst]) rfl (ih.2 hne k)⟩

/-! ## Numbers -/

/-- The number after every one the names and the commits carry, as `nextSeq` counts it. -/
theorem next_eq (cs : List Commit) (ns : List Name) :
    (cs.map (·.seq)).foldl max ((ns.filterMap seqOf).foldl max 0) + 1 = nextSeq cs ns := by
  rw [nextSeq, List.foldl_append, foldl_max_start (cs.map (·.seq)),
    foldl_max_start (ns.filterMap seqOf) ((cs.map (·.seq)).foldl max 0)]
  omega

/-! ## Names -/

/-- A name set aside is in the directory as the names that read show. -/
theorem quarantine_found {s : Nat} (hs : s < 2 ^ 64) :
    (img.lookup (quarantineName s)).isSome = (img.filterMap (parseName ·.1)).contains (.quarantine s) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.lookup_isSome_iff]
  simp only [beq_iff_eq, List.contains_iff_mem, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, e⟩
    exact ⟨p, hp, by rw [← e]; exact parseName_bytes (.quarantine s) (by simpa [Name.valid] using hs)⟩
  · rintro ⟨p, hp, e⟩
    exact ⟨p, hp, (parseName_inv e).symm⟩

/-- A final name is a commit's when its number is. -/
theorem recorded_eq (cs : List Commit) (hc : ∀ c ∈ cs, c.seq < 2 ^ 64) {s : Nat} (hs : s < 2 ^ 64) :
    (cs.map (finalName ·.seq)).contains (finalName s) = (cs.map (·.seq)).contains s := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨c, hc', e⟩
    have := names_injective (.final c.seq) (.final s) (by simpa [Name.valid] using hc c hc')
      (by simpa [Name.valid] using hs) e
    exact ⟨c, hc', by cases this; rfl⟩
  · rintro ⟨c, hc', rfl⟩
    exact ⟨c, hc', rfl⟩

/-! ## After the journal: the rules, the files, the numbers -/

/-- What the phases after the journal read and keep. -/
structure Core where
  /-- how many names the first pass read -/
  names : Nat
  /-- the highest number a name carries -/
  maxSeq : Nat
  /-- whether a tail is kept -/
  tails : Bool
  /-- the highest number a kept tail carries -/
  maxTail : Nat
  /-- whether the store starts new -/
  fresh : Bool
  /-- the journal's commits -/
  commits : List Commit
  /-- whether the journal ends torn -/
  torn : Bool
  /-- where the torn tail starts -/
  cut : Nat
  /-- where the journal ends -/
  journalEnd : Nat
  /-- the journal's key -/
  key : Option Bytes

/-- What phases after the journal read keep of a state: the names' count and numbers, whether the store is new. Also the
commits, the torn tail, the journal's end and its key. A state with another phase or counter keeps it, by `rfl`. -/
def RSt.core (r : RSt) : Core :=
  ⟨r.names, r.maxSeq, r.tails, r.maxTail, r.fresh, r.commits, r.torn, r.cut, r.journalEnd, r.scan.key⟩

/-- **Each commit's file**, asked about in journal order: the first missing or of another size is refused. Otherwise the
numbers come next. -/
theorem files_drives {cs : List Commit} {h : Host} {x : Except Fault (Store × List Action)} :
    ∀ (n i : Nat) (r : RSt), n + i = cs.length → r.phase = 5 → r.commits = cs → r.i = i → r.wait = false →
    (∀ f, fileFault? img (cs.drop i) = some f → Drives cfg img J r h (.error f)) ∧
    (fileFault? img (cs.drop i) = none →
      (∀ r', r'.phase = 6 → r'.core = r.core → r'.tidied = r.tidied → Drives cfg img J r' h x) →
      Drives cfg img J r h x)
  | 0, i, r, hn, hph, hc, hi, _ => by
    have hd : cs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    have hp : phase cfg J r = ({ r with phase := 6 }, none) := by
      rw [phase_files hph, files, hc, hi, List.getElem?_eq_none (by omega)]
    rw [hd]
    exact ⟨fun f e => (by cases e), fun _ k => drives_go hp (k _ rfl rfl rfl)⟩
  | n + 1, i, r, hn, hph, hc, hi, hw => by
    have hlt : i < cs.length := by omega
    have hd : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hlt
    have hcs : cs[i]? = some cs[i] := List.getElem?_eq_getElem hlt
    have hp : phase cfg J r = ({ r with seq := cs[i].seq, wait := true }, some (.askFile cs[i].seq)) := by
      rw [phase_files hph, files, hc, hi, hcs, hw]; rfl
    have ih := files_drives (cs := cs) (h := h) (x := x) n (i + 1)
    have hgo : ∀ fl : Bytes, fl.length = cs[i].fileSize →
        phase cfg J { r with seq := cs[i].seq, wait := true, found := true, fileSize := fl.length } =
          ({ r with seq := cs[i].seq, wait := false, found := true, fileSize := fl.length, i := i + 1 }, none) :=
      fun fl hsz => by
        rw [phase_files (r := { r with seq := cs[i].seq, wait := true, found := true, fileSize := fl.length }) hph,
          files]
        simp [hc, hi, hcs, hsz]
    have hsize : ∀ fl : Bytes, fl.length ≠ cs[i].fileSize →
        phase cfg J { r with seq := cs[i].seq, wait := true, found := true, fileSize := fl.length } =
          ({ r with seq := cs[i].seq, wait := false, found := true, fileSize := fl.length },
            some (.refused (.wrongSize cs[i].seq))) :=
      fun fl hsz => by
        rw [phase_files (r := { r with seq := cs[i].seq, wait := true, found := true, fileSize := fl.length }) hph,
          files]
        simp [hc, hi, hcs, hsz]
    have hmiss : phase cfg J { r with seq := cs[i].seq, wait := true, found := false, fileSize := 0 } =
        ({ r with seq := cs[i].seq, wait := false, found := false, fileSize := 0 },
          some (.refused (.missingFile cs[i].seq))) := by
      rw [phase_files (r := { r with seq := cs[i].seq, wait := true, found := false, fileSize := 0 }) hph, files]
      simp [hc, hi, hcs]
    refine ⟨fun f e => ?_, fun e k => ?_⟩ <;> refine drives_out hp rfl ?_ <;> rw [hd] at e <;>
      simp only [fileFault?] at e <;> cases hl : img.lookup (finalName cs[i].seq) <;> simp only [hl] at e <;>
      simp only [answer, hl]
    · cases e
      exact drives_refused hmiss
    · rename_i fl
      split at e
      · rename_i hsz
        let r2 : RSt := { r with seq := cs[i].seq, wait := false, found := true, fileSize := fl.length, i := i + 1 }
        exact drives_go (hgo fl hsz) ((ih r2 (by omega) hph hc rfl rfl).1 _ e)
      · rename_i hsz
        cases e
        exact drives_refused (hsize fl hsz)
    · cases e
    · rename_i fl
      split at e
      · rename_i hsz
        let r2 : RSt := { r with seq := cs[i].seq, wait := false, found := true, fileSize := fl.length, i := i + 1 }
        exact drives_go (hgo fl hsz) ((ih r2 (by omega) hph hc rfl rfl).2 e fun r' h1 h2 h3 => k r' h1 h2 h3)
      · cases e

/-- **The next number**: none left refused; else the numbers before and after a torn tail. -/
theorem numbered_drives {r : RSt} {h : Host} {x : Except Fault (Store × List Action)} (hph : r.phase = 6)
    (hb : (r.commits.map (·.seq)).foldl max r.maxSeq < 2 ^ 64) :
    (2 ^ 64 ≤ (r.commits.map (·.seq)).foldl max r.maxSeq + 1 + (if r.torn then 1 else 0) →
      Drives cfg img J r h (.error .exhausted)) ∧
    ((r.commits.map (·.seq)).foldl max r.maxSeq + 1 + (if r.torn then 1 else 0) < 2 ^ 64 →
      (∀ r', r'.phase = 7 → r'.i = 0 → r'.core = r.core → r'.tidied = r.tidied →
        r'.next0 = (r.commits.map (·.seq)).foldl max r.maxSeq + 1 →
        r'.next = (r.commits.map (·.seq)).foldl max r.maxSeq + 1 + (if r.torn then 1 else 0) →
        Drives cfg img J r' h x) →
      Drives cfg img J r h x) := by
  obtain ⟨m, hm⟩ : ∃ m, m = (r.commits.map (·.seq)).foldl max r.maxSeq := ⟨_, rfl⟩
  rw [← hm] at hb ⊢
  have hp := phase_numbered (cfg := cfg) (J := J) hph
  simp only [numbered] at hp
  rw [← hm] at hp
  let r7 : RSt := { r with next0 := m + 1, next := m + 1 + (if r.torn then 1 else 0), i := 0, phase := 7 }
  refine ⟨fun hx => drives_refused (by rw [hp, if_pos (by cases ht : r.torn <;> simp [ht] at hx ⊢ <;> omega)]),
    fun hx k => drives_go (r' := r7) (by rw [hp, if_neg (by cases ht : r.torn <;> simp [ht] at hx ⊢ <;> omega)])
      (k r7 rfl rfl rfl rfl rfl rfl)⟩

/-- The actions a torn tail takes: kept, the directory synced, the journal cut. -/
def tailActs (cfg : Config) (J : Bytes) (r : RSt) : List Action :=
  if r.torn then [actOf cfg J (.keep r.next0 r.cut), .syncDir, .cut r.cut] else []

/-- **A torn tail** kept under the next number, the directory synced, the journal cut. Then the first name of the second
pass is asked for. -/
theorem tail_drives {r : RSt} {h : Host} {x : Except Fault (Store × List Action)} (hph : r.phase = 7) (hi : r.i = 0)
    (k : ∀ r', r'.phase = 8 → r'.first = true → r'.core = r.core → r'.tidied = r.tidied →
      r'.next0 = r.next0 → r'.next = r.next →
      Drives cfg img J (answer cfg img J r' { h with acts := h.acts ++ tailActs cfg J r } .askName).1
        (answer cfg img J r' { h with acts := h.acts ++ tailActs cfg J r } .askName).2 x) :
    Drives cfg img J r h x := by
  cases ht : r.torn with
  | false =>
    refine drives_out (r' := { r with first := true, phase := 8 }) (o := .askName)
      (by rw [phase_tail hph, tail]; simp [ht]) rfl ?_
    have := k { r with first := true, phase := 8 } rfl rfl rfl rfl rfl rfl
    simpa [tailActs, ht] using this
  | true =>
    refine drives_out (r' := { r with i := 1 }) (o := .gives (.keep r.next0 r.cut))
      (by rw [phase_tail hph, tail]; simp [ht, hi]) rfl ?_
    simp only [answer]
    refine drives_out (r' := { r with i := 2 }) (o := .gives .syncDir)
      (by rw [phase_tail (r := { r with i := 1 }) hph, tail]; simp [ht]) rfl ?_
    simp only [answer]
    refine drives_out (r' := { r with i := 3 }) (o := .gives (.cut r.cut))
      (by rw [phase_tail (r := { r with i := 2 }) hph, tail]; simp [ht]) rfl ?_
    simp only [answer]
    refine drives_out (r' := { r with i := 3, first := true, phase := 8 }) (o := .askName)
      (by rw [phase_tail (r := { r with i := 3 }) hph, tail]; simp [ht]) rfl ?_
    have := k { r with i := 3, first := true, phase := 8 } rfl rfl rfl rfl rfl rfl
    simpa [answer, tailActs, ht, actOf] using this

/-- **Recovery done**: the directory synced after names are tidied, the torn tail's number set aside. -/
theorem finish_drives {r : RSt} {h : Host} (hph : r.phase = 11) (hi : r.i = 0) :
    Drives cfg img J r h (.ok (storeAt cfg r { h with aside := h.aside ++ if r.torn then [r.next0] else [] },
      h.acts ++ if 0 < r.tidied then [.syncDir] else [])) := by
  by_cases htd : 0 < r.tidied
  · refine drives_out (r' := { r with i := 1 }) (o := .gives .syncDir)
      (by rw [phase_finish hph, finish]; simp [hi, htd]) rfl ?_
    simp only [answer]
    by_cases ht : r.torn = true
    · refine drives_out (r' := { r with i := 2 }) (o := .givesAside r.next0)
        (by rw [phase_finish (r := { r with i := 1 }) hph, finish]; simp [ht]) rfl ?_
      simp only [answer]
      have := drives_done (cfg := cfg) (img := img) (J := J)
        (h := { h with acts := h.acts ++ [actOf cfg J .syncDir], aside := h.aside ++ [r.next0] })
        (r' := { r with i := 3 })
        (by rw [phase_finish (r := { r with i := 2 }) hph, finish]; simp)
      simpa [storeAt, actOf, ht, htd] using this
    · have := drives_done (cfg := cfg) (img := img) (J := J) (h := { h with acts := h.acts ++ [actOf cfg J .syncDir] })
        (r' := { r with i := 2 }) (by rw [phase_finish (r := { r with i := 1 }) hph, finish]; simp [ht])
      simpa [storeAt, actOf, ht, htd] using this
  · by_cases ht : r.torn = true
    · refine drives_out (r' := { r with i := 2 }) (o := .givesAside r.next0)
        (by rw [phase_finish hph, finish]; simp [hi, htd, ht]) rfl ?_
      simp only [answer]
      have := drives_done (cfg := cfg) (img := img) (J := J) (h := { h with aside := h.aside ++ [r.next0] })
        (r' := { r with i := 3 }) (by rw [phase_finish (r := { r with i := 2 }) hph, finish]; simp)
      simpa [storeAt, ht, htd] using this
    · have := drives_done (cfg := cfg) (img := img) (J := J) (h := h) (r' := { r with i := 1 })
        (by rw [phase_finish hph, finish]; simp [hi, htd, ht])
      simpa [storeAt, ht, htd] using this

/-! ## The second pass -/

/-- **A name of the second pass**: what recovery does to it and sets aside, as `tidyName` and `asideOf` say. -/
theorem name_drives {cs : List Commit} {ns : List Name} {torn : Bool} {x : Except Fault (Store × List Action)}
    (n : Name) (hv : n.valid = true) {r : RSt} {h : Host} (hph : r.phase = 8) (hend : r.ended = false)
    (hname : parseName r.name = some n) (hc : r.commits = cs)
    (hsa : ∀ s, (r.torn || (r.tails && decide (s < r.maxTail))) = setsAside ns torn s)
    (hrec : ∀ s, s < 2 ^ 64 → (cs.map (·.seq)).contains s = (cs.map (finalName ·.seq)).contains (finalName s))
    (hq : ∀ s, s < 2 ^ 64 → (img.lookup (quarantineName s)).isSome = ns.contains (.quarantine s))
    (k : ∀ r' h', r'.phase = 8 → r'.first = false → r'.core = r.core → r'.next0 = r.next0 →
      r'.next = r.next →
      r'.tidied = r.tidied + (tidyName (cs.map (finalName ·.seq)) ns torn n).toList.length →
      h'.acts = h.acts ++ (tidyName (cs.map (finalName ·.seq)) ns torn n).toList →
      h'.aside = h.aside ++ (asideOf (cs.map (finalName ·.seq)) ns torn n).toList → h'.cursor = h.cursor →
      Drives cfg img J (answer cfg img J r' h' .askName).1 (answer cfg img J r' h' .askName).2 x) :
    Drives cfg img J r h x := by
  have hp : phase cfg J r = secondName { r with first := false } (some n) := by
    rw [phase_secondPass hph, secondPass, if_neg (by simp [hend]), hname]
  -- the next name asked for, once the phase is at 13
  have h13 : ∀ (r' : RSt) (h' : Host), r'.phase = 13 → r'.core = r.core → r'.next0 = r.next0 →
      r'.next = r.next →
      r'.tidied = r.tidied + (tidyName (cs.map (finalName ·.seq)) ns torn n).toList.length →
      h'.acts = h.acts ++ (tidyName (cs.map (finalName ·.seq)) ns torn n).toList →
      h'.aside = h.aside ++ (asideOf (cs.map (finalName ·.seq)) ns torn n).toList → h'.cursor = h.cursor →
      Drives cfg img J r' h' x := fun r' h' p13 h1 h2 h0 h3 h4 h5 h6 =>
    drives_out (r' := { r' with first := false, phase := 8 }) (o := .askName) (phase_askNext p13) rfl
      (k _ h' rfl rfl h1 h2 h0 h3 h4 h5 h6)
  cases n with
  | journal =>
    exact drives_out (r' := { r with first := false }) (o := .askName) (by rw [hp]; rfl) rfl
      (k _ h hph rfl rfl rfl rfl (by simp [tidyName]) (by simp [tidyName]) (by simp [asideOf_journal]) rfl)
  | temp s =>
    refine drives_out (r' := { r with first := false, seq := s, tidied := r.tidied + 1, phase := 13 })
      (o := .gives (.remove s true)) (by rw [hp]; rfl) rfl ?_
    exact h13 _ _ rfl rfl rfl rfl (by simp [answer, tidyName]) (by simp [answer, actOf, tidyName])
      (by simp [answer, asideOf_temp]) rfl
  | quarantine s | tail s =>
    refine drives_out (r' := { r with first := false, seq := s, phase := 13 }) (o := .givesAside s)
      (by rw [hp]; rfl) rfl ?_
    exact h13 _ _ rfl rfl rfl rfl (by simp [answer, tidyName]) (by simp [answer, tidyName])
      (by simp [answer, asideOf_quarantine, asideOf_tail])
      rfl
  | final s =>
    have hs64 : s < 2 ^ 64 := by simpa [Name.valid] using hv
    have hrs := hrec s hs64
    have hqs := hq s hs64
    by_cases hr : (cs.map (·.seq)).contains s = true
    · have hrf : (cs.map (finalName ·.seq)).contains (finalName s) = true := hrs ▸ hr
      exact drives_out (r' := { r with first := false, seq := s }) (o := .askName)
        (by rw [hp]; simp only [secondName, hc ▸ hr, ↓reduceIte]) rfl
        (k _ h hph rfl rfl rfl rfl
          (by simp only [tidyName, hrf, ↓reduceIte, Option.toList_none, List.length_nil, Nat.add_zero])
          (by simp only [tidyName, hrf, ↓reduceIte, Option.toList_none, List.append_nil])
          (by simp only [asideOf_final, hrf, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            Option.toList_none, List.append_nil]) rfl)
    have hr0 : (cs.map (·.seq)).contains s = false := by rwa [Bool.not_eq_true] at hr
    have hrr : (r.commits.map (·.seq)).contains s = false := hc ▸ hr0
    have hrf : (cs.map (finalName ·.seq)).contains (finalName s) = false := by rw [← hrs]; exact hr0
    by_cases hset : (r.torn || (r.tails && decide (s < r.maxTail))) = true
    · have hset' := (hsa s).symm.trans hset
      let r9 : RSt := { r with first := false, seq := s, phase := 9 }
      let rf : RSt := { r9 with found := (img.lookup (quarantineName s)).isSome }
      refine drives_out (r' := r9) (o := .askAside s)
        (by rw [hp]; simp only [secondName, hrr, hset, Bool.false_eq_true, ↓reduceIte]; rfl) rfl ?_
      show Drives cfg img J rf h x
      by_cases hf : (img.lookup (quarantineName s)).isSome = true
      · have hqn : ns.contains (.quarantine s) = true := hqs ▸ hf
        let r13 : RSt := { rf with tidied := r.tidied + 1, phase := 13 }
        refine drives_out (r' := r13) (o := .gives (.remove s false))
          (by rw [phase_asideGiven (r := rf) rfl, asideGiven]; exact if_pos hf) rfl ?_
        exact h13 _ _ rfl rfl rfl rfl
          (by simp only [answer, tidyName, hrf, hqn, Bool.true_or, Bool.false_eq_true, ↓reduceIte, Option.toList_some,
            List.length_singleton]; rfl)
          (by simp only [answer, actOf, tidyName, hrf, hqn, Bool.true_or, Bool.false_eq_true, ↓reduceIte,
            Option.toList_some, Bool.false_eq_true])
          (by simp only [answer, asideOf_final, hrf, hqn, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, Option.toList_none, List.append_nil]) rfl
      · have hf0 : (img.lookup (quarantineName s)).isSome = false := by rwa [Bool.not_eq_true] at hf
        have hqn : ns.contains (.quarantine s) = false := hqs ▸ hf0
        let r12 : RSt := { rf with tidied := r.tidied + 1, phase := 12 }
        let r13 : RSt := { rf with tidied := r.tidied + 1, phase := 13 }
        refine drives_out (r' := r12) (o := .gives (.rename s))
          (by rw [phase_asideGiven (r := rf) rfl, asideGiven]; exact if_neg hf) rfl ?_
        show Drives cfg img J r12 { h with acts := h.acts ++ [actOf cfg J (.rename s)] } x
        refine drives_out (r' := r13) (o := .givesAside s) (phase_renamed rfl) rfl ?_
        exact h13 _ _ rfl rfl rfl rfl
          (by simp only [answer, tidyName, hrf, hqn, hset', Bool.false_or, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, Option.toList_some, List.length_singleton]; rfl)
          (by simp only [answer, actOf, tidyName, hrf, hqn, hset', Bool.false_or, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, Option.toList_some])
          (by simp only [answer, asideOf_final, hrf, hqn, hset', Bool.not_false, Bool.true_and, ↓reduceIte,
            Option.toList_some]) rfl
    · have hset0 : (r.torn || (r.tails && decide (s < r.maxTail))) = false := by rwa [Bool.not_eq_true] at hset
      have hset' : setsAside ns torn s = false := by rw [← hsa]; exact hset0
      refine drives_out (r' := { r with first := false, seq := s, tidied := r.tidied + 1, phase := 13 })
        (o := .gives (.remove s false))
        (by rw [hp]; simp only [secondName, hrr, hset0, Bool.false_eq_true, ↓reduceIte]) rfl ?_
      exact h13 _ _ rfl rfl rfl rfl
        (by simp only [answer, tidyName, hrf, hset', Bool.not_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte,
          Option.toList_some, List.length_singleton])
        (by simp only [answer, actOf, tidyName, hrf, hset', Bool.not_false, Bool.or_true, Bool.false_eq_true,
          ↓reduceIte, Option.toList_some])
        (by simp only [answer, asideOf_final, hrf, hset', Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          Option.toList_none, List.append_nil]) rfl

/-- One element's image. -/
theorem filterMap_single {α β : Type} (f : α → Option β) (a : α) : [a].filterMap f = (f a).toList := by
  cases e : f a <;> simp [e]

/-- Two states that keep the same: field by field. -/
structure SameCore (r r' : RSt) : Prop where
  names : r'.names = r.names
  maxSeq : r'.maxSeq = r.maxSeq
  tails : r'.tails = r.tails
  maxTail : r'.maxTail = r.maxTail
  fresh : r'.fresh = r.fresh
  commits : r'.commits = r.commits
  torn : r'.torn = r.torn
  cut : r'.cut = r.cut
  journalEnd : r'.journalEnd = r.journalEnd
  key : r'.scan.key = r.scan.key

/-- States with what they keep equal are the same, field by field. -/
theorem sameCore {r r' : RSt} (h : r'.core = r.core) : SameCore r r' :=
  ⟨congrArg Core.names h, congrArg Core.maxSeq h, congrArg Core.tails h, congrArg Core.maxTail h,
    congrArg Core.fresh h, congrArg Core.commits h, congrArg Core.torn h, congrArg Core.cut h,
    congrArg Core.journalEnd h, congrArg Core.key h⟩

/-- **The second pass** over names that all parse: each tidied and set aside as `tidyName` and `asideOf` say. Then
recovery's end. -/
theorem second_drives {cs : List Commit} {ns : List Name} {torn : Bool} {acts0 : List Action}
    {x : Except Fault (Store × List Action)} (hvalid : ∀ n ∈ ns, n.valid = true)
    (hrec : ∀ s, s < 2 ^ 64 → (cs.map (·.seq)).contains s = (cs.map (finalName ·.seq)).contains (finalName s))
    (hq : ∀ s, s < 2 ^ 64 → (img.lookup (quarantineName s)).isSome = ns.contains (.quarantine s)) :
    ∀ (suf : Image) (pre ms : List Name) (r : RSt) (h : Host), r.phase = 8 →
    (if r.first then 0 else h.cursor) = pre.length → pre.length ≤ img.length → img.drop pre.length = suf →
    suf.mapM nameOf = .ok ms → pre ++ ms = ns → r.commits = cs →
    (∀ s, (r.torn || (r.tails && decide (s < r.maxTail))) = setsAside ns torn s) →
    r.tidied = (pre.filterMap (tidyName (cs.map (finalName ·.seq)) ns torn)).length →
    h.acts = acts0 ++ pre.filterMap (tidyName (cs.map (finalName ·.seq)) ns torn) →
    h.aside = pre.filterMap (asideOf (cs.map (finalName ·.seq)) ns torn) →
    (∀ r' h', r'.phase = 11 → r'.i = 0 → r'.core = r.core → r'.next0 = r.next0 → r'.next = r.next →
      r'.tidied = (ns.filterMap (tidyName (cs.map (finalName ·.seq)) ns torn)).length →
      h'.acts = acts0 ++ ns.filterMap (tidyName (cs.map (finalName ·.seq)) ns torn) →
      h'.aside = ns.filterMap (asideOf (cs.map (finalName ·.seq)) ns torn) → Drives cfg img J r' h' x) →
    Drives cfg img J (answer cfg img J r h .askName).1 (answer cfg img J r h .askName).2 x
  | [], pre, ms, r, h, hph, hc, hle, hd, hm, hpre, hcs, hsa, ht, ha, hs, k => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm
    subst hm
    rw [List.append_nil] at hpre
    subst hpre
    have hl := drop_nil hd hle
    rw [answer_name hc, List.getElem?_eq_none (by omega)]
    dsimp only
    exact drives_go (r' := { r with ended := true, i := 0, phase := 11 })
      (by rw [phase_secondPass (r := { r with ended := true }) hph, secondPass, if_pos rfl])
      (k _ _ rfl rfl rfl rfl rfl ht ha hs)
  | p :: suf, pre, ms, r, h, hph, hc, hle, hd, hm, hpre, hcs, hsa, ht, ha, hs, k => by
    obtain ⟨n, ms', hp, hs', rfl⟩ := mapM_cons_ok hm
    obtain ⟨hget, hl, hd'⟩ := drop_cons hd
    rw [answer_name hc, hget]
    dsimp only
    have hn : n ∈ ns := by rw [← hpre]; simp
    refine name_drives (cs := cs) (ns := ns) (torn := torn) n (hvalid n hn) hph rfl hp hcs hsa hrec hq ?_
    intro r' h' h1 h2 h3 h4 h0 h5 h6 h7 h8
    have c3 := sameCore h3
    refine second_drives hvalid hrec hq suf (pre ++ [n]) ms' r' h' h1 (by simp [h2, h8]) (by simpa using hl)
      (by simpa using hd') hs' (by simpa using hpre)
      (by rw [c3.commits]; exact hcs) (fun s => by rw [c3.tails, c3.maxTail, c3.torn]; exact hsa s)
      (by rw [h5, ht, List.filterMap_append, List.length_append, filterMap_single])
      (by rw [h6, List.filterMap_append, filterMap_single, ← List.append_assoc, ← ha])
      (by rw [h7, List.filterMap_append, filterMap_single, ← hs]) fun r'' h'' g1 g2 g3 g4 g0 g5 g6 g7 =>
        k r'' h'' g1 g2 (g3.trans h3) (g4.trans h4) (g0.trans h0) g5 g6 g7

/-! ## Recovery from the journal's records -/

/-- The torn tail's actions the step gives are those `recoverRecords` lists. -/
theorem tailActs_eq {r7 : RSt} {cut : Option Nat} {n0 : Nat} (ht : r7.torn = cut.isSome)
    (hcut : ∀ p, cut = some p → r7.cut = p) (hn : r7.next0 = n0) : tailActs cfg J r7 = cutActs J cut n0 := by
  cases cut with
  | none => simp [tailActs, cutActs, ht]
  | some x => simp [tailActs, cutActs, ht, hcut x rfl, hn, actOf]

/-- **From the journal's commits on**: the rules, the files, the next number, the torn tail and the names tidied. All as
`recoverRecords` says. -/
theorem records_drives {ns : List Name} {cs : List Commit} {k : Bytes} {cut : Option Nat} {r : RSt}
    (hall : img.mapM nameOf = .ok ns) (hns : ns = img.filterMap (parseName ·.1))
    (hvalid : ∀ n ∈ ns, n.valid = true) (hseq : ∀ c ∈ cs, c.seq < 2 ^ 64)
    (hph : r.phase = 4) (hc : r.commits = cs) (hu : r.unknown = unknownGroup? cfg (cs.take capacity))
    (hms : r.maxSeq = (ns.filterMap seqOf).foldl max 0) (htl : r.tails = !(ns.filterMap tailOf).isEmpty)
    (hmt : r.maxTail = (ns.filterMap tailOf).foldl max 0) (hfr : r.fresh = false) (htd : r.tidied = 0)
    (ht : r.torn = cut.isSome) (hcut : ∀ p, cut = some p → r.cut = p) (hje : r.journalEnd = cut.getD J.length)
    (hk : r.scan.key = some k) :
    Drives cfg img J r ⟨img.length, [], []⟩ (recoverRecords cfg img ns J k cs cut) := by
  unfold recoverRecords
  by_cases hcap : capacity < cs.length
  · rw [if_pos hcap]; exact drives_refused (by rw [phase_rules hph, rules, hc, if_pos (by omega)])
  rw [if_neg hcap]
  have hu' : r.unknown = unknownGroup? cfg cs := by rw [hu, List.take_of_length_le (by omega)]
  have hcap' : ¬ capacity + 1 ≤ r.commits.length := by rw [hc]; omega
  cases h1 : seqTwice? cs with
  | some s =>
    exact drives_refused (by rw [phase_rules hph, rules, if_neg hcap', hc, h1])
  | none =>
  cases h2 : idTwice? cs with
  | some m => exact drives_refused (by rw [phase_rules hph, rules, if_neg hcap', hc, h1, h2])
  | none =>
  cases h3 : unknownGroup? cfg cs with
  | some g => exact drives_refused (by rw [phase_rules hph, rules, if_neg hcap', hc, h1, h2, hu', h3])
  | none =>
  cases h4 : notAbove? [] cs with
  | some gn =>
    obtain ⟨g, n⟩ := gn
    exact drives_refused (by rw [phase_rules hph, rules, if_neg hcap', hc, h1, h2, hu', h3, h4])
  | none =>
  have hp4 : phase cfg J r = ({ r with i := 0, wait := false, phase := 5, unknown := none }, none) := by
    rw [phase_rules hph, rules, if_neg hcap', show seqTwice? r.commits = none from hc ▸ h1,
      show idTwice? r.commits = none from hc ▸ h2, show r.unknown = none from hu'.trans h3,
      show notAbove? [] r.commits = none from hc ▸ h4]
  have hfiles := fun x => files_drives (cfg := cfg) (img := img) (J := J) (cs := cs) (h := ⟨img.length, [], []⟩)
    (x := x) cs.length 0 { r with i := 0, wait := false, phase := 5, unknown := none } (by simp) rfl hc rfl rfl
  cases h5 : fileFault? img cs with
  | some f => exact drives_go hp4 ((hfiles (.error f)).1 f (by simpa using h5))
  | none =>
  dsimp only
  refine drives_go hp4 ((hfiles _).2 (by simpa using h5) fun r6 g1 g2 g3 => ?_)
  have c6 := sameCore g2
  have hall' : ∀ x ∈ cs.map (·.seq) ++ ns.filterMap seqOf, x < 2 ^ 64 := fun x hx => by
    simp only [List.mem_append, List.mem_map, List.mem_filterMap] at hx
    rcases hx with ⟨c, hc', rfl⟩ | ⟨n, hn, hs⟩
    · exact hseq c hc'
    · exact name_seq_valid n (hvalid n hn) x hs
  have hnext : nextSeq cs ns ≤ 2 ^ 64 := by
    have := foldl_max_lt _ hall' (by decide); rw [nextSeq]; omega
  have hm : (r6.commits.map (·.seq)).foldl max r6.maxSeq + 1 = nextSeq cs ns := by
    rw [c6.commits, hc, c6.maxSeq, hms]; exact next_eq cs ns
  have htr : r6.torn = cut.isSome := c6.torn.trans ht
  have hb : (r6.commits.map (·.seq)).foldl max r6.maxSeq < 2 ^ 64 := by omega
  have hnb := fun x => numbered_drives (cfg := cfg) (img := img) (J := J) (h := ⟨img.length, [], []⟩) (x := x) g1 hb
  by_cases hx : 2 ^ 64 ≤ (if cut.isSome = true then nextSeq cs ns + 1 else nextSeq cs ns)
  · rw [if_pos hx]
    refine (hnb (.error .exhausted)).1 ?_
    rw [htr, hm]; cases hcs : cut.isSome <;> simp [hcs] at hx ⊢ <;> omega
  rw [if_neg hx]
  refine (hnb _).2 (by rw [htr, hm]; cases hcs : cut.isSome <;> simp [hcs] at hx ⊢ <;> omega)
    fun r7 f1 f2 f3 f4 f5 f6 => ?_
  rw [hm] at f5
  rw [hm, htr] at f6
  refine tail_drives f1 f2 fun r8 i1 i2 i3 i4 i5 i6 => ?_
  have c8 : r8.core = r.core := i3.trans (f3.trans g2)
  have kc := sameCore c8
  have hsa : ∀ s, (r8.torn || (r8.tails && decide (s < r8.maxTail))) = setsAside ns cut.isSome s := fun s => by
    rw [kc.torn, kc.tails, kc.maxTail, ht, htl, hmt, setsAside_eq]
  have hrec : ∀ s, s < 2 ^ 64 → (cs.map (·.seq)).contains s = (cs.map (finalName ·.seq)).contains (finalName s) :=
    fun s hs => (recorded_eq cs hseq hs).symm
  have hq : ∀ s, s < 2 ^ 64 → (img.lookup (quarantineName s)).isSome = ns.contains (.quarantine s) :=
    fun s hs => by rw [hns]; exact quarantine_found hs
  refine second_drives (acts0 := tailActs cfg J r7) (torn := cut.isSome) hvalid hrec hq img [] ns r8 _ i1
    (by rw [i2]; rfl) (Nat.zero_le _) rfl hall rfl (by rw [kc.commits, hc]) hsa (by rw [i4, f4, g3, htd]; rfl) (by simp)
    rfl fun r11 h11 j1 j2 j3 j4 j0 j5 j6 j7 => ?_
  have c11 : r11.core = r.core := j3.trans c8
  have l := sameCore c11
  have hfin := finish_drives (cfg := cfg) (img := img) (J := J) (h := h11) j1 j2
  have hn0 : r11.next0 = nextSeq cs ns := by rw [j4, i5, f5]
  have hnx : r11.next = (if cut.isSome = true then nextSeq cs ns + 1 else nextSeq cs ns) := by
    rw [j0, i6, f6]; cases cut.isSome <;> simp
  have m := sameCore (f3.trans g2)
  have hta := tailActs_eq (cfg := cfg) (J := J) (m.torn.trans ht) (fun p hp => m.cut.trans (hcut p hp)) f5
  have e : (.ok (storeAt cfg r11 { h11 with aside := h11.aside ++ if r11.torn then [r11.next0] else [] },
      h11.acts ++ if 0 < r11.tidied then [.syncDir] else []) : Except Fault (Store × List Action)) =
      .ok (⟨k, cs, ns.filterMap (asideOf (cs.map (finalName ·.seq)) ns cut.isSome) ++
          (if cut.isSome = true then [nextSeq cs ns] else []),
        if cut.isSome = true then nextSeq cs ns + 1 else nextSeq cs ns, cut.getD J.length⟩,
        cutActs J cut (nextSeq cs ns) ++ ns.filterMap (tidyName (cs.map (finalName ·.seq)) ns cut.isSome) ++
        if (ns.filterMap (tidyName (cs.map (finalName ·.seq)) ns cut.isSome)).isEmpty = true then []
        else [Action.syncDir]) := by
    rw [j7, j6, j5, hn0, l.torn, ht, hta]
    simp only [storeAt, l.fresh, hfr, l.key, hk, l.commits, hc, l.journalEnd, hje, hnx, Bool.false_eq_true,
      ↓reduceIte, Option.getD_some]
    congr 3
    cases (ns.filterMap (tidyName (cs.map (finalName ·.seq)) ns cut.isSome)) <;> simp
  exact e ▸ hfin

/-! ## Recovery -/

/-- The journal is among the names that read when the directory holds it. -/
theorem journal_found {ns : List Name} (hns : ns = img.filterMap (parseName ·.1)) :
    (img.lookup journalName).isSome = ns.contains .journal := by
  rw [hns]
  apply Bool.eq_iff_iff.mpr
  rw [List.lookup_isSome_iff]
  simp only [beq_iff_eq, List.contains_iff_mem, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, e⟩; exact ⟨p, hp, by rw [← e]; exact parse_journal⟩
  · rintro ⟨p, hp, e⟩; exact ⟨p, hp, (parseName_inv e).symm⟩

/-- The journal read to its end, records in it: the rules next. -/
theorem scanned_go {r : RSt} {t : Option Nat} (h : r.records ≠ 0) :
    scanned r t = (match t with
      | some p => { r with journalEnd := p, torn := true, cut := p, phase := 4 }
      | none => { r with journalEnd := r.jsize, phase := 4 }, none) := by
  unfold scanned; rw [if_neg h]; cases t <;> rfl

/-- Phase 0 leaves the first pass's state with no name read, whatever the area held. -/
theorem fp_begin (r : RSt) : FP [] (begin r).1 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- The journal read, no record in it: a new store when the journal is the directory's one file. -/
theorem end_nil {ns : List Name} {e : End} {r : RSt} (hE : EndSC cfg J ns ⟨[], e⟩ r)
    (hlen : ns.length = img.length) :
    Drives cfg img J r ⟨img.length, [], []⟩
      (if img.length = 1 then .ok (fresh cfg, [.create cfg.key]) else .error .noJournal) := by
  have hp := hE.phase
  unfold scanned at hp
  rw [if_pos (by rw [hE.records]; rfl)] at hp
  by_cases hn1 : img.length = 1
  · rw [if_pos hn1]
    rw [if_pos (by rw [hE.kept.names, hlen, hn1])] at hp
    have := fresh_drives (cfg := cfg) (img := img) (J := J) (h := ⟨img.length, [], []⟩) (r := r) false
      (by rw [hE.commits]; rfl) rfl rfl
    exact drives_go hp (by simpa using this)
  · rw [if_neg hn1]
    rw [if_neg (by rw [hE.kept.names, hlen]; exact hn1)] at hp
    exact drives_refused hp

/-- The journal read, its format first: recovery from its commits, as `recoverRecords` says. -/
theorem end_records {ns : List Name} {e : End} {key : Bytes} {rest : List Record} {r : RSt}
    (hE : EndSC cfg J ns ⟨.format key :: rest, e⟩ r) (hne : ∀ p w, e ≠ .corrupt p w)
    (hall : img.mapM nameOf = .ok ns) (hns : ns = img.filterMap (parseName ·.1))
    (hvalid : ∀ n ∈ ns, n.valid = true)
    (hok : ∀ c, .commit c ∈ rest → c.ok = true) :
    Drives cfg img J r ⟨img.length, [], []⟩ (recoverRecords cfg img ns J key (commitsOf rest) (cutOf e)) := by
  have hseq : ∀ c ∈ commitsOf rest, c.seq < 2 ^ 64 := fun c hc => by
    have hc' : .commit c ∈ rest := by
      simp only [commitsOf, List.mem_filterMap] at hc
      obtain ⟨r', hr', e'⟩ := hc
      cases r' <;> simp_all
    exact Commit.ok_seq (hok c hc')
  have hrec : r.records ≠ 0 := by rw [hE.records]; simp
  have hp := hE.phase
  rw [scanned_go hrec] at hp
  have hu : r.unknown = unknownGroup? cfg ((commitsOf rest).take capacity) := by rw [hE.unknown]; simp [commitsOf]
  have hcs : r.commits = commitsOf rest := by rw [hE.commits]; simp [commitsOf]
  have hk : r.scan.key = some key := by rw [hE.key]; simp [Record.key]
  have K := hE.kept
  cases e with
  | corrupt p w => exact absurd rfl (hne p w)
  | clean =>
    simp only [cutOf] at hp
    exact drives_go hp (records_drives hall hns hvalid hseq rfl hcs hu
      K.maxSeq K.tails K.maxTail K.fresh K.tidied K.torn (fun _ h => by cases h) (by rw [hE.jsize]; rfl) hk)
  | torn p =>
    simp only [cutOf] at hp
    exact drives_go hp (records_drives hall hns hvalid hseq rfl hcs hu
      K.maxSeq K.tails K.maxTail K.fresh K.tidied rfl (fun _ h => by cases h; rfl) rfl hk)

/-- **Recovery's steps find what `recover` does.** The host reads directory `img`: names in order, journal octets as
wanted, final files and sizes, names set aside. From phase 0 they reach `recover`'s corruption, or its store and first
actions, for a key of 16 octets. -/
theorem drives_recover (cfg : Config) (img : Image) (hkey : cfg.key.length = keyLength) {r0 : RSt}
    (h0 : r0.phase = 0) : Drives cfg img ((img.lookup journalName).getD []) r0 Host.start (recover cfg img) := by
  obtain ⟨J, hJ⟩ : ∃ J, J = (img.lookup journalName).getD [] := ⟨_, rfl⟩
  rw [← hJ, recover, if_pos hkey]
  unfold recoverWith
  refine drives_out (r' := (begin r0).1) (o := .askName) (by rw [phase_begin h0]; rfl) rfl ?_
  cases hm : img.mapM nameOf with
  | error f => exact first_err img [] _ (fp_begin r0) rfl rfl (Nat.zero_le _) rfl hm
  | ok ns =>
  obtain ⟨hall, hns⟩ := mapM_nameOf img ns hm
  have hvalid : ∀ n ∈ ns, n.valid = true := fun n hn => by
    rw [hns] at hn
    obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp hn
    exact parseName_valid _ _ hp
  have hlen : ns.length = img.length := by rw [hns]; exact List.filterMap_length_eq_length.mpr hall
  refine first_ok img [] ns _ (fp_begin r0) rfl rfl (Nat.zero_le _) rfl hm fun r1 hfp hph hend => ?_
  rw [List.nil_append] at hfp
  have hp1 := phase_firstPass (cfg := cfg) (J := J) hph
  rw [firstPass] at hp1
  rw [if_pos hend] at hp1
  have hjf := journal_found (img := img) hns
  cases hl : img.lookup journalName with
  | none =>
    have hj : r1.journal = false := by rw [hfp.journal, ← hjf, hl]; rfl
    rw [if_neg (by simp [hj])] at hp1
    by_cases he : img.isEmpty = true
    · rw [if_pos he]
      have hn0 : r1.names = 0 := by rw [hfp.names, hlen, List.isEmpty_iff.mp he]; rfl
      rw [if_pos hn0] at hp1
      have := fresh_drives (cfg := cfg) (img := img) (J := J) (h := ⟨img.length, [], []⟩) (r := r1) true hfp.commits
        rfl rfl
      exact drives_go hp1 (by simpa using this)
    · rw [if_neg he]
      have hn0 : ¬ r1.names = 0 := by
        rw [hfp.names, hlen]; intro e; exact he (List.isEmpty_iff.mpr (List.eq_nil_of_length_eq_zero e))
      rw [if_neg hn0] at hp1
      exact drives_refused hp1
  | some content =>
  have hJc : J = content := by rw [hJ, hl]; rfl
  subst hJc
  have hj : r1.journal = true := by rw [hfp.journal, ← hjf, hl]; rfl
  rw [if_pos hj] at hp1
  refine drives_out hp1 rfl ?_
  simp only [answer]
  refine drives_go (phase_journalGiven rfl) ?_
  let r3 : RSt := { r1 with phase := 3, jsize := J.length, scan := St.start }
  have hsc : SC cfg J ns St.start r3 :=
    ⟨rfl, rfl, valid_start _, hfp.records, by simp [r3, hfp.commits, St.start, commitsOf],
      by simp [r3, hfp.unknown, St.start, commitsOf, unknownGroup?], rfl, rfl,
      { hfp.toFPK with }⟩
  have hsd := fun x => scan_drives (cfg := cfg) (img := img) (J := J) ns (h := ⟨img.length, [], []⟩) (x := x)
    (2 * J.length + 1) St.start (J.length + 1) r3 hsc
    (by simp only [ScanRun.St.left, St.start]; omega) (by simp only [St.start]; omega)
  have hscan : scanFrom spec (J.length + 1) (J.drop St.start.pos) St.start.pos St.start.key St.start.acc =
      scan J := by simp [scan, scanWith, St.start]
  simp only [hscan] at hsd
  have hok := scanFrom_ok (J.length + 1) J 0 none [] (fun _ h => by cases h)
  change ∀ c, .commit c ∈ (scan J).records → c.ok = true at hok
  show Drives cfg img J r3 ⟨img.length, [], []⟩ _
  cases he : (scan J).ending with
  | corrupt p w => exact (hsd (.error (.journal p w))).1 p w he
  | clean | torn _ =>
    cases hr : (scan J).records with
    | nil =>
      exact (hsd _).2 (fun p w e => by rw [he] at e; cases e) fun r' hE => by
        rw [show scan J = ⟨(scan J).records, (scan J).ending⟩ from rfl, he, hr] at hE; exact end_nil hE hlen
    | cons rec rest =>
      obtain ⟨key, rfl⟩ := scan_first hr
      exact (hsd _).2 (fun p w e => by rw [he] at e; cases e) fun r' hE => by
        rw [show scan J = ⟨(scan J).records, (scan J).ending⟩ from rfl, he, hr] at hE
        exact end_records hE (fun p w e => by cases e) hm hns hvalid fun c hc => hok c (by rw [hr]; simp [hc])

/-! ## The premises can hold -/

section Witness

/-- A configuration with a key of sixteen octets and no group. -/
def cfg0 : Config := ⟨[], List.replicate 16 0⟩

/-- What the first pass keeps can hold. -/
theorem fp_witness : FP [] (begin RSt.start).1 := fp_begin _

/-- …and what it finds. -/
theorem fpk_witness : FPK [] RSt.start := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The journal being read can hold. -/
theorem sc_witness : SC cfg0 [] [] St.start { RSt.start with phase := 3 } :=
  ⟨rfl, rfl, valid_start _, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The journal read to its end can hold. -/
theorem endSC_witness : EndSC cfg0 [] [] (scan []) { RSt.start with phase := 3 } :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- States that keep the same can be. -/
theorem sameCore_witness : SameCore RSt.start RSt.start := sameCore rfl

/-- A step can end. -/
theorem steps_witness : Steps cfg0 [] RSt.start { RSt.start with first := true, phase := 1 } .askName := .out rfl

/-- An empty directory recovers to a new store. -/
theorem drives_witness : Drives cfg0 [] [] RSt.start Host.start (recover cfg0 []) := drives_recover cfg0 [] rfl rfl

end Witness

end DN.News.RecoverSpec
