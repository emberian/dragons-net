-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverLate
import DN.News.RecoverRules

/-!
# DN.News.RecoverRun

Recovery's step as the program runs it (`RecoverProg.stepWith`) is `RecoverSpec`'s: phases in turn until one asks
or gives.
-/

namespace DN.News.RecoverArea

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.News.Journal DN.News.Recovery
open DN.News.RecoverProg
open DN.News.RecoverSpec (RSt ROut runPhases runPhases_succ_none steps_end)
open DN.News.ScanRun (Kept at_ vals_lookup kept_has kept_set kept_widen frag_if)
open DN.News.FramerCode (bw ev_var)

variable {σ : Type}

/-- What a phase's start keeps of the step's: the base, the area, and the step going on. -/
theorem pin_of {A : Word} {cfg : Config} {J : Bytes} {q : RSt} {s0 u : PancakeState σ} (h : PBase A s0)
    (hJ : J.length < 2 ^ 62) (hk : Kept stepLocals (RAreaW A) s0 u) (ha : RAt A cfg J q u)
    (hg : u.locals "rgo" = some 1) : PIn A cfg J q u :=
  ⟨⟨h.hA, by rw [hk.memaddrs]; exact h.dom, rsc_kept h hk, jsc_kept h hk, jz_kept h hk,
    fun y hy => kept_has hk (h.bound y hy)⟩, hg, ha, hJ⟩

/-- A phase run from where the step got to. -/
theorem from_phase (o : Oracle σ) {prog : List Syntax.PStmt} (hl : LowKK prog) {A : Word} {cfg : Config}
    {J : Bytes} {q : RSt} {s0 : PancakeState σ} {p : RSt × Option ROut} {X : Assn σ}
    (h : ∀ s, PIn A cfg J q s → Frag o prog (Like s) (POut A cfg J s p)) :
    Frag o prog (fun u => PIn A cfg J q u ∧ Kept stepLocals (RAreaW A) s0 u ∧ X u) (POut A cfg J s0 p) :=
  frag_each o hl fun s ⟨hs, hk, _⟩ => frag_conseq (h s hs) (fun _ h => h) fun _ hu => ⟨ScanRun.kept_trans hk hu.1, hu.2⟩

/-- What phases need of a start state: numbers below a word, the journal's length once given. No new journal while it is
read, commits of its format, the index's capacity once the rules hold. Groups known when none lacks and all are indexed;
files' counter within commits; a torn tail in the scanner's window. -/
structure PhaseOk (cfg : Config) (J : Bytes) (q : RSt) : Prop where
  phase : q.phase < 2 ^ 64
  names : q.names < 2 ^ 64
  maxSeq : q.maxSeq < 2 ^ 64
  maxTail : q.maxTail < 2 ^ 64
  records : q.records + 1 < 2 ^ 64
  jsize : 2 ≤ q.phase → q.phase ≤ 3 → q.jsize = J.length
  fresh : 3 ≤ q.phase → q.phase ≤ 7 → q.fresh = false
  ok : ∀ c ∈ q.commits, c.ok = true
  commits : q.commits.length < 2 ^ 62
  held : 5 ≤ q.phase → q.commits.length ≤ capacity
  known : q.phase = 4 → q.commits.length ≤ capacity → q.unknown = none →
    ∀ c ∈ q.commits, ∀ g ∈ c.groups, cfg.groups.contains g.name = true
  files : q.phase = 5 → q.i ≤ q.commits.length ∧ (q.wait = true → q.i < q.commits.length ∧ q.fileSize < 2 ^ 64)
  i : 5 ≤ q.phase → q.i < 2 ^ 63
  tidied : q.tidied < 2 ^ 63
  torn : q.phase = 7 → q.torn = true → q.scan.base ≤ q.cut ∧ q.cut ≤ J.length ∧ J.length ≤ q.scan.base + q.scan.len

theorem lowKK_scanning {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (scanning fail) :=
  lowKK_append (ScanRun.lowKK_step hfl) (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rest hfl)))

theorem lowKK_rules {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (rules fail) :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl)
      (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ruleChecks hfl)))

theorem lowKK_files {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (files fail) :=
  lowKK_append (lowKK_append (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_kept hfl _ _))
    (lowK_any _ (k := .skip) (c := _) rfl)) (lowKK_ite rfl (lowKK_append (xs := [_]) (lowKK_kept hfl _ _)
      (lowK_any _ (k := .skip) (c := _) rfl)) (lowK_any _ (k := .skip) (c := _) rfl))

/-- Each program of `l` lowered. -/
def LowAll : List (Nat × List Syntax.PStmt) → Prop
  | [] => True
  | (_, t) :: l => LowKK t ∧ LowAll l

/-- What each program of `l` needs for `dispatch`: its number below a word, no declaration. And `P` to `Q` where the
phase is its number. -/
def DispOk (o : Oracle σ) (ph : Nat) (P Q : Assn σ) : List (Nat × List Syntax.PStmt) → Prop
  | [] => True
  | (k, t) :: l => (k < 2 ^ 64 ∧ declared t = [] ∧ (ph = k → Frag o t P Q)) ∧ DispOk o ph P Q l

theorem lowKK_dispatch {e : List Syntax.PStmt} (he : LowKK e) :
    ∀ {l : List (Nat × List Syntax.PStmt)}, LowAll l → LowKK (dispatch l e)
  | [], _ => he
  | _ :: _, ⟨h1, h2⟩ => lowKK_ite rfl h1 (lowKK_dispatch he h2)

/-- **The program of the phase in `rph`**, by `dispatch`. -/
theorem dispatch_frag (o : Oracle σ) {P Q : Assn σ} (hQ : Safe.ClockFree Q) {ph : Nat} (hph : ph < 2 ^ 64)
    (hP : ∀ u, P u → u.locals "rph" = some (.ofNat 64 ph)) {e : List Syntax.PStmt} (hle : LowKK e)
    (hde : declared e = []) : ∀ (l : List (Nat × List Syntax.PStmt)), LowAll l → DispOk o ph P Q l →
      ((∀ p ∈ l, ph ≠ p.1) → Frag o e P Q) → Frag o (dispatch l e) P Q
  | [], _, _, he => he fun _ h => nomatch h
  | (k, t) :: l, ⟨hlt, hlw⟩, ⟨⟨hk, hdt, ht⟩, hl⟩, he =>
    frag_if o (C := .cmp .equal (.var "rph") (.const (.ofNat 64 k))) rfl hlt (lowKK_dispatch hle hlw) hdt
      (by cases l <;> first | rfl | exact hde) hQ (b := decide (ph = k))
      (fun u hu => FramerCode.eval_eq hph hk (ev_var (hP u hu)) rfl) (fun e => ht (of_decide_eq_true e))
      fun e => dispatch_frag o hQ hph hP hle hde l hlw hl fun hn => he fun p hp => by
        rcases List.mem_cons.1 hp with rfl | hp
        · exact of_decide_eq_false e
        · exact hn p hp

theorem lowAll_phases {fail : List Syntax.PStmt} (hfl : LowKK fail) :
    LowAll (phaseTable fail) :=
  ⟨lowK_any _ (k := .skip) (c := _) rfl, lowK_any _ (k := .skip) (c := _) rfl, lowK_any _ (k := .skip) (c := _) rfl,
    lowKK_scanning hfl, lowKK_rules hfl, lowKK_files hfl, lowK_any _ (k := .skip) (c := _) rfl,
    lowK_any _ (k := .skip) (c := _) rfl, lowK_any _ (k := .skip) (c := _) rfl, lowK_any _ (k := .skip) (c := _) rfl,
    lowK_any _ (k := .skip) (c := _) rfl, lowK_any _ (k := .skip) (c := _) rfl, lowK_any _ (k := .skip) (c := _) rfl,
    trivial⟩

theorem lowKK_phases {fail : List Syntax.PStmt} (hfl : LowKK fail) : LowKK (phases fail) :=
  lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowKK_dispatch (lowK_any _ (k := .skip) (c := _) rfl) (lowAll_phases hfl))

/-- **One phase**, the one the area's phase word names: the specification's. -/
theorem phases_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {q : RSt} {s0 : PancakeState σ} (h : PBase A s0) (hJ : J.length < 2 ^ 62)
    (hok : PhaseOk cfg J q) :
    Frag o (phases fail) (POut A cfg J s0 (q, none)) (POut A cfg J s0 (RecoverSpec.phase cfg J q)) := by
  have hq : q.phase < 2 ^ 64 := hok.phase
  unfold phases
  refine frag_append (xs := [_]) (M := fun u => PIn A cfg J q u ∧ Kept stepLocals (RAreaW A) s0 u ∧
    u.locals "rph" = some (.ofNat 64 q.phase)) (frag_conseq (mid_assign o h (y := "rph") (by decide)
      (rw_lower (by decide)) (r := q) (ws := scalars cfg q) (os := []) (l := [("rgo", 1)]) (val := .ofNat 64 q.phase)
      fun u hu => by rw [mid_rw h hu (by decide) (rw_lower (by decide))]; rfl)
    (fun u ⟨hk, ha, hg⟩ => ⟨hk, ha.words, (fun _ h => nomatch h), (fun _ h => nomatch h), ha.rest, fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact hg⟩)
    fun u hu => ⟨pin_of h hJ hu.kept ⟨hu.words, hu.rest⟩ (vals_lookup hu.vals rfl), hu.kept,
      vals_lookup hu.vals rfl⟩) ?_
  refine dispatch_frag o pout_clock hq (fun u hu => hu.2.2) (lowK_any _ (k := .skip) (c := _) rfl) rfl _
    (lowAll_phases hfl) ⟨⟨by decide, rfl, fun e => ?_⟩, ⟨by decide, rfl, fun e => ?_⟩, ⟨by decide, rfl, fun e => ?_⟩,
      ⟨by decide, rfl, fun e => ?_⟩, ⟨by decide, rfl, fun e => ?_⟩, ⟨by decide, rfl, fun e => ?_⟩,
      ⟨by decide, rfl, fun e => ?_⟩, ⟨by decide, rfl, fun e => ?_⟩, ⟨by decide, rfl, fun e => ?_⟩,
      ⟨by decide, rfl, fun e => ?_⟩, ⟨by decide, rfl, fun e => ?_⟩, ⟨by decide, rfl, fun e => ?_⟩,
      ⟨by decide, rfl, fun e => ?_⟩, trivial⟩ fun hn => ?_
  · rw [RecoverSpec.phase_begin e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs => begin_frag o hs
  · rw [RecoverSpec.phase_firstPass e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs =>
      firstPass_frag o hs e hok.names hok.maxSeq hok.maxTail
  · rw [RecoverSpec.phase_journalGiven e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs =>
      journalGiven_frag o hs e (hok.jsize (by omega) (by omega))
  · rw [RecoverSpec.phase_scanning e]
    exact from_phase o (lowKK_scanning hfl) fun s hs =>
      scanning_frag o hfl hfd hs e (hok.fresh (by omega) (by omega)) hok.names hok.records
        (hok.jsize (by omega) (by omega)) hok.commits
  · rw [RecoverSpec.phase_rules e]
    exact from_phase o (lowKK_rules hfl) fun s hs =>
      rules_frag o hfl hfd hs e (hok.fresh (by omega) (by omega)) hok.ok hok.commits (hok.known e)
  · rw [RecoverSpec.phase_files e]
    exact from_phase o (lowKK_files hfl) fun s hs =>
      files_frag o hfl hfd hs e hok.ok (hok.held (by omega)) (hok.files e).1 (hok.files e).2
  · rw [RecoverSpec.phase_numbered e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs =>
      numbered_frag o hs e (hok.held (by omega)) (fun c hc => (ok_bounds (hok.ok c hc)).1) hok.maxSeq
  · rw [RecoverSpec.phase_tail e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs =>
      tail_frag o hs e (by have := hok.i (by omega); omega) (hok.fresh (by omega) (by omega)) (hok.torn e)
  · rw [RecoverSpec.phase_secondPass e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs =>
      secondPass_frag o hs e hok.ok (hok.held (by omega)) hok.maxTail
  · rw [RecoverSpec.phase_asideGiven e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs => asideGiven_frag o hs e
  · rw [RecoverSpec.phase_created e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs =>
      created_frag o hs e (by have := hok.i (by omega); omega)
  · rw [RecoverSpec.phase_finish e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs =>
      finish_frag o hs e (hok.i (by omega)) hok.tidied
  · rw [RecoverSpec.phase_renamed e]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs => renamed_frag o hs e
  · simp only [phaseTable, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hn
    rw [RecoverSpec.phase_late (by omega)]
    exact from_phase o (lowK_any _ (k := .skip) (c := _) rfl) fun s hs => askNext_frag o hs (by omega)

/-- **The phases in turn** until one asks or gives: what `Steps` gives, where each state they pass is `PhaseOk`. -/
theorem loop_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PBase A s0) (hJ : J.length < 2 ^ 62)
    {r' : RSt} {o' : ROut} (hs : RecoverSpec.Steps cfg J r r' o')
    (hok : ∀ k q, runPhases cfg J k r = (q, none) → PhaseOk cfg J q) :
    Frag o [.while (Syntax.v "rgo") (phases fail)] (POut A cfg J s0 (r, none)) (POut A cfg J s0 (r', some o')) := by
  let I (k : Nat) : Assn σ := POut A cfg J s0 (runPhases cfg J k r)
  refine frag_conseq (frag_count o (c := Syntax.v "rgo") (C := .var "rgo") rfl (lowKK_phases hfl)
    (fun _ => pout_clock) (fun k => noDecl (P' := I k) _ rfl) (g := fun k => (runPhases cfg J k r).2.isNone)
    (fun k u hu => ?_) (fun k hk => ?_) 0) (fun u hu => hu) fun u ⟨k, hu, hg⟩ => ?_
  · have hu' : POut A cfg J s0 (runPhases cfg J k r) u := hu
    show u.locals "rgo" = some (bw (runPhases cfg J k r).2.isNone)
    cases hr : runPhases cfg J k r with
    | mk q oo =>
      rw [hr] at hu'
      cases oo with
      | none => exact hu'.2.2
      | some _ => exact hu'.2.2.1
  · cases hr : runPhases cfg J k r with
    | mk q oo =>
      cases oo with
      | some _ => simp [hr] at hk
      | none =>
        rw [runPhases_succ_none hr]
        exact phases_frag o hfl hfd h hJ (hok k q hr)
  · have hsome : (runPhases cfg J k r).2.isSome := by
      cases e : (runPhases cfg J k r).2 with
      | none => simp [e] at hg
      | some _ => rfl
    have hu' : POut A cfg J s0 (runPhases cfg J k r) u := hu
    rwa [steps_end hs hsome] at hu'

/-- **A step of recovery**, run by the program: from the area holding `r`, the area ends as `Steps` leaves it. The step
gives what `Steps` asks or gives, each state the phases pass being `PhaseOk`. The locals but the step's and the memory
but the area stay as they were. -/
theorem step_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s : PancakeState σ} (hA : A.toNat % 8 = 0)
    (hd : RDom A s.memaddrs) (hrsc : s.locals "rsc" = some A) (hjz : s.locals "jz" = some 0)
    (hbd : ∀ y ∈ RecoverProg.locals, ∃ v, s.locals y = some v) (ha : RAt A cfg J r s) (hJ : J.length < 2 ^ 62)
    {r' : RSt} {o' : ROut} (hs : RecoverSpec.Steps cfg J r r' o')
    (hok : ∀ k q, runPhases cfg J k r = (q, none) → PhaseOk cfg J q) :
    Frag o (stepWith fail) (Like s) (fun u => Kept RecoverProg.locals (RAreaW A) s u ∧ RAt A cfg J r' u ∧
      u.locals "rgo" = some 0 ∧ OutR A J r' o' u) := by
  let P1 (t : PancakeState σ) : Prop := Kept RecoverProg.locals (RAreaW A) s t ∧ PBase A t ∧ RAt A cfg J r t ∧
    t.locals "rgo" = some 1
  have hjsc : "jsc" ∈ RecoverProg.locals := by decide
  have hrgo : "rgo" ∈ RecoverProg.locals := by decide
  refine frag_append (xs := [_, _]) (M := P1) (frag_append (xs := [_])
    (M := fun t => Kept RecoverProg.locals (RAreaW A) s t ∧ t.locals "jsc" = some (at_ A rScan) ∧ RAt A cfg J r t)
    (set_frag o (E := .op .add (.var "rsc") (.const (.ofNat 64 rScan))) rfl
      (fun _ _ ⟨h1, h2, h3⟩ => ⟨{ h1 with }, h2, rat_congr h3 rfl rfl rfl⟩) fun t ht => ?_)
    (set_frag o (E := .op .add (.var "jz") (.const (.ofNat 64 1))) rfl
      (fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨{ h1 with }, { h2 with }, rat_congr h3 rfl rfl rfl, h4⟩) fun t ht => ?_)) ?_
  · refine ⟨at_ A rScan, by simp only [eval, ht.locals, hrsc]; rfl, by rw [ht.locals]; exact hbd _ hjsc,
      kept_set (ScanRun.kept_of_like ht) hjsc _, by simp [setL, setLocal], rat_congr ha ht.memory ht.memaddrs ht.be⟩
  · obtain ⟨hk, hj, hr⟩ := ht
    have hjz' : t.locals "jz" = some 0 := by rw [hk.locals _ (by decide)]; exact hjz
    refine ⟨1, by simp only [eval, hjz']; rfl, kept_has hk (hbd _ hrgo), kept_set hk hrgo _,
      ⟨hA, by rw [show (setL t "rgo" 1).memaddrs = s.memaddrs from hk.memaddrs]; exact hd,
        by simp only [setL, setLocal]; rw [hk.locals _ (by decide)]; exact hrsc,
        by simp only [setL, setLocal]; exact hj, by simp only [setL, setLocal]; exact hjz', fun y hy => ?_⟩,
      rat_congr hr rfl rfl rfl, by simp [setL, setLocal]⟩
    by_cases e : y = "rgo"
    · subst e; exact ⟨1, by simp [setL, setLocal]⟩
    · obtain ⟨v, hv⟩ := kept_has hk (hbd y hy)
      exact ⟨v, by simp only [setL, setLocal]; rw [if_neg e]; exact hv⟩
  · exact frag_each o (lowKK_while rfl (lowKK_phases hfl)) fun t ht => frag_conseq
      (loop_frag o hfl hfd ht.2.1 hJ hs hok)
      (fun u hu => ⟨ScanRun.kept_of_like hu, rat_congr ht.2.2.1 hu.memory hu.memaddrs hu.be,
        by rw [hu.locals]; exact ht.2.2.2⟩)
      fun u ⟨hk, ha', hg, hout⟩ => ⟨ScanRun.kept_trans ht.1 (kept_widen hk (fun x hx => (List.mem_filter.1 hx).1)
        fun _ h => h), ha', hg, hout⟩

/-! ## Witnesses -/

/-- Phase 5 with one commit, its file asked about next. -/
def r5 : RSt := { RSt.start with phase := 5, commits := [oCommit] }

theorem phaseOk_witness : PhaseOk oCfg [] r5 where
  phase := by decide
  names := by decide
  maxSeq := by decide
  maxTail := by decide
  records := by decide
  jsize := fun _ h => absurd h (by decide)
  fresh := fun _ _ => rfl
  ok := fun c hc => by simp only [r5, List.mem_singleton] at hc; subst hc; exact oCommit_ok
  commits := by decide
  held := fun _ => by decide
  known := fun h => absurd h (by decide)
  files := fun _ => ⟨by decide, fun h => nomatch h⟩
  i := fun _ => by decide
  tidied := by decide
  torn := fun h => absurd h (by decide)

/-- The start of a step from a fresh area, a journal of one octet given. -/
theorem phaseOk_start : PhaseOk wCfg [0] RSt.start where
  phase := by decide
  names := by decide
  maxSeq := by decide
  maxTail := by decide
  records := by decide
  jsize := fun h => absurd h (by decide)
  fresh := fun h => absurd h (by decide)
  ok := fun _ h => nomatch h
  commits := by decide
  held := fun h => absurd h (by decide)
  known := fun h => absurd h (by decide)
  files := fun h => absurd h (by decide)
  i := fun h => absurd h (by decide)
  tidied := by decide
  torn := fun h => absurd h (by decide)

/-- Phase 3, a journal of one octet given. -/
def rJ3 : RSt := { RSt.start with phase := 3, jsize := 1 }

theorem phaseOk_read : PhaseOk wCfg [0] rJ3 where
  phase := by decide
  names := by decide
  maxSeq := by decide
  maxTail := by decide
  records := by decide
  jsize := fun _ _ => rfl
  fresh := fun _ _ => rfl
  ok := fun _ h => nomatch h
  commits := by decide
  held := fun h => absurd h (by decide)
  known := fun h => absurd h (by decide)
  files := fun h => absurd h (by decide)
  i := fun h => absurd h (by decide)
  tidied := by decide
  torn := fun h => absurd h (by decide)

/-- Phase 4 with one commit, its group the configuration's. -/
def r4 : RSt := { RSt.start with phase := 4, commits := [oCommit] }

theorem phaseOk_rules : PhaseOk oCfg [0] r4 where
  phase := by decide
  names := by decide
  maxSeq := by decide
  maxTail := by decide
  records := by decide
  jsize := fun _ h => absurd h (by decide)
  fresh := fun _ _ => rfl
  ok := fun c hc => by simp only [r4, List.mem_singleton] at hc; subst hc; exact oCommit_ok
  commits := by decide
  held := fun h => absurd h (by decide)
  known := fun _ _ _ c hc g hg => by
    simp only [r4, List.mem_singleton] at hc; subst hc
    simp only [oCommit, List.mem_singleton] at hg; subst hg; decide
  files := fun h => absurd h (by decide)
  i := fun h => absurd h (by decide)
  tidied := by decide
  torn := fun h => absurd h (by decide)

/-- Phase 7 with a torn tail at the journal's start, the window holding its one octet. -/
def r7 : RSt := { RSt.start with phase := 7, torn := true, scan := { ScanRun.St.start with len := 1 } }

theorem phaseOk_tail : PhaseOk wCfg [0] r7 where
  phase := by decide
  names := by decide
  maxSeq := by decide
  maxTail := by decide
  records := by decide
  jsize := fun _ h => absurd h (by decide)
  fresh := fun _ _ => rfl
  ok := fun _ h => nomatch h
  commits := by decide
  held := fun _ => by decide
  known := fun h => absurd h (by decide)
  files := fun h => absurd h (by decide)
  i := fun _ => by decide
  tidied := by decide
  torn := fun _ _ => ⟨by decide, by decide, by decide⟩

theorem fitsCfg_witness : FitsCfg oCfg oCommit := ⟨by decide, by decide⟩

theorem rising_witness : Rising [oCommit] := fun i hi g hg => by
  simp only [List.length_singleton, Nat.lt_one_iff] at hi
  subst hi
  simp only [List.getElem_singleton, oCommit, List.mem_singleton] at hg
  subst hg
  decide

theorem highIs_witness : HighIs 0 (fun _ => 0) wState := fun _ _ => rfl

theorem within_witness : Within [("rgo", (1 : Value))] [("rgo", 1)] := ⟨rfl, trivial⟩

theorem lowAll_witness : LowAll [(0, RecoverProg.begin)] := ⟨lowK_any _ (k := .skip) (c := _) rfl, trivial⟩

theorem dispOk_witness :
    DispOk (σ := Unit) Oracle.idle 0 (fun _ => True) (fun _ => True) [(0, [])] :=
  ⟨⟨by decide, rfl, fun _ => frag_nil _ fun _ h => h⟩, trivial⟩

end DN.News.RecoverArea
