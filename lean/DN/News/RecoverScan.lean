-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverCommit

/-!
# DN.News.RecoverScan

Recovery's phase 3 as the program runs it (`RecoverProg.scanning`) is `RecoverSpec.scanning`: a step of the
journal's scanner (`DN.News.ScanStop.step_frag`) in recovery's area, then octets asked for, a record counted and a
commit noted in its slot, the journal refused, or the journal read to its end.
-/

namespace DN.News.RecoverArea

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.Compiler.Bytes DN.News.Journal DN.News.Recovery
open DN.News.RecoverProg
open DN.News.RecoverSpec (RSt)
open DN.News.ScanRun (St AreaAt Kept Valid at_ align_at vals_lookup kept_widen stepSpec without lookup_cons_ne
  lookup_without frag_if putBytes load_putBytes load_putBytes_other load_eq)
open DN.News.FramerCode (bw)

variable {σ : Type}

/-- **`Rest` outside the scanner's area**: what holds there of `r` holds of `r` with the scanner at `st'` where only
the scanner's area changed and `st'` is in it. -/
theorem rest_outside {A : Word} (hA : A.toNat % 8 = 0) {cfg : Config} {J : Bytes} {r : RSt} {u u' : PancakeState σ}
    (h : Rest A cfg J r u)
    (hm : ∀ y, (y < rScan ∨ rSlots ≤ y) → y < RecoverProg.size → u'.memory (at_ A y) = u.memory (at_ A y))
    (hd : u'.memaddrs = u.memaddrs) (hb : u'.be = u.be) {st' : St}
    (hscan : 3 ≤ r.phase → r.fresh = false → AreaAt (at_ A rScan) J st' u' ∧ Valid J st') :
    Rest A cfg J { r with scan := st' } u' :=
  rest_frame hA h (fun y hy => hm y (reads_lt hy).2 (reads_lt hy).1) hd hb hscan

/-- **The scanner's step in recovery's area**: from a phase's start, the scanner's state `r.scan` in its area, the
step's state with the scanner where `stepSpec` takes it. -/
theorem scanStep_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PIn A cfg J r s0) (hp : r.phase = 3)
    (hfr : r.fresh = false) :
    Frag o (ScanProg.stepWith fail) (Like s0)
      (fun u => Kept stepLocals (RAreaW A) s0 u ∧ ScanRun.OutAt (at_ A rScan) J r.scan (stepSpec J r.scan) u ∧
        Words A (scalars cfg r) u ∧ u.locals "rgo" = some 1 ∧
        ∀ st', (3 ≤ r.phase → r.fresh = false → AreaAt (at_ A rScan) J st' u ∧ Valid J st') →
          Rest A cfg J { r with scan := st' } u) := by
  have hn := nums
  obtain ⟨ha, hv⟩ := h.area.rest.scan (by omega) hfr
  have hin : ScanRun.StepIn (at_ A rScan) J r.scan s0 :=
    ⟨at_aligned h.hA (by decide), scan_dom h.dom, h.jsc, h.jz, ha, hv, h.short,
      fun y hy => h.bound y (scan_locals y hy)⟩
  refine frag_conseq (ScanRun.step_frag o hin hfl hfd) (fun _ h => h) fun u ⟨hk, hout⟩ => ?_
  have hm : ∀ y, (y < rScan ∨ rSlots ≤ y) → y < RecoverProg.size → u.memory (at_ A y) = s0.memory (at_ A y) :=
    fun y hy hys => hk.memory _ (not_scanW hy (by omega))
  refine ⟨kept_widen hk scan_step fun a ⟨x, hx, e⟩ => ⟨rScan + x, by omega, by rw [e, at_at]⟩, hout,
    fun x hx => ?_, by rw [hk.locals _ (by decide)]; exact h.rgo, fun st' hs =>
      rest_outside h.hA h.area.rest hm hk.memaddrs hk.be hs⟩
  have := (free_scalar x hx).1
  simp only [Free] at this
  rw [hm x (by omega) (by omega)]; exact h.area.words x hx

/-- Words of the scanner's area at its offsets `xs`, each holding what `xs` says. -/
def ScanAt (A : Word) (u : PancakeState σ) : List (Nat × Word) → Prop
  | [] => True
  | q :: xs => u.memory (at_ (at_ A rScan) q.1) = q.2 ∧ ScanAt A u xs

theorem scanAt_mem {A : Word} {u : PancakeState σ} : ∀ {xs : List (Nat × Word)}, ScanAt A u xs →
    ∀ q ∈ xs, u.memory (at_ (at_ A rScan) q.1) = q.2
  | _ :: _, ⟨h1, h2⟩, _, hq => (List.mem_cons.1 hq).elim (fun e => e ▸ h1) (scanAt_mem h2 _)

/-- **After the scanner's step**, a state between stores: the scanner's words `xs` known. -/
theorem mid_after {A : Word} {cfg : Config} {J : Bytes} {r r' : RSt} {s0 u : PancakeState σ}
    (hk : Kept stepLocals (RAreaW A) s0 u) (hw : Words A (scalars cfg r) u) (hrgo : u.locals "rgo" = some 1)
    (hr : Rest A cfg J r' u) {xs : List (Nat × Word)} (hxs : ScanAt A u xs)
    (hb : (xs.map Prod.fst).all (· < ScanProg.size) = true) :
    Mid A cfg J r' s0 (scalars cfg r) (xs.map fun q => (rScan + q.1, q.2)) [("rgo", 1)] u := by
  have e : rScan + ScanProg.size = rSlots := rfl
  refine ⟨hk, hw, fun q hq => ?_, fun q hq => ?_, hr, fun q hq => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    rw [← at_at]; exact scanAt_mem hxs p hp
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    have := of_decide_eq_true (List.all_eq_true.1 hb p.1 (List.mem_map_of_mem hp))
    exact .inr (.inl ⟨Nat.le_add_right _ _, by omega⟩)
  · simp only [List.mem_singleton] at hq; subst hq; exact hrgo

theorem valid_want0 {J : Bytes} {st st' : St} {n : Nat} (hv : Valid J st) (h : stepSpec J st = .want st' n) :
    Valid J st' := by
  simp only [stepSpec] at h
  split at h
  · cases h
  split at h
  · simp only [ScanRun.Out.want.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := hv.base
    have := hv.pos
    have := hv.stop
    have := hv.len
    exact ⟨Nat.le_refl _, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, hv.keyed, hv.count⟩
  · split at h
    · split at h <;> cases h
    · cases h
    · cases h

/-- What follows a status other than octets wanted lowers. -/
theorem lowKK_rest {fail : List Syntax.PStmt} (hfl : LowKK fail) :
    LowKK [.ite (Syntax.eEq (Syntax.v "rst") (Syntax.n ScanProg.record))
      [rset rRecords (Syntax.eAdd (rw rRecords) (Syntax.n 1)),
       .ite (Syntax.eEq (sw ScanProg.sType) (Syntax.n commitType)) (commitRead fail) []]
      [.ite (Syntax.eEq (Syntax.v "rst") (Syntax.n ScanProg.corrupt))
        (refuse (.journal 0 .short) [rset rFaultA (sw ScanProg.sPos), rset rFaultB (sw ScanProg.sWhy)])
        [.ite (Syntax.eEq (rw rRecords) (Syntax.n 0))
          [.ite (Syntax.eEq (rw rNames) (Syntax.n 1)) (RecoverProg.fresh false) (refuse .noJournal [])]
          [rset rJournalEnd (sw ScanProg.sSize),
           .ite (Syntax.eEq (Syntax.v "rst") (Syntax.n ScanProg.torn))
             [rset rTorn (Syntax.n 1), rset rCut (sw ScanProg.sPos), rset rJournalEnd (sw ScanProg.sPos)] [],
           next 4]]]] :=
  lowKK_ite rfl (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowKK_ite rfl (lowKK_commitRead hfl) (fun k => ⟨k, rfl⟩))) (lowK_any _ (k := .skip) (c := _) rfl)

theorem rst_eval {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} {ws : Nat → Word}
    {os : List (Nat × Word)} {l : List (String × Value)} {code : Nat} (hc : code < 2 ^ 64) {k : Nat} (hk : k < 2 ^ 64)
    (u : PancakeState σ) (hu : Mid A cfg J r s0 ws os (("rst", .ofNat 64 code) :: l) u) :
    eval u (.cmp .equal (.var "rst") (.const (.ofNat 64 k))) = some (bw (decide (code = k))) :=
  FramerCode.eval_eq (t := u) (a := .var "rst") (b := .const _) hc hk (vals_lookup hu.vals (by simp)) rfl

/-- **The journal read to its end**, torn at `t` if it is: none records, the store new or no journal; else the rules
next. -/
theorem ended_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hp : r.phase = 3) (hnm : r.names < 2 ^ 64) (hj : r.jsize = J.length)
    (hrc : r.records < 2 ^ 64) {t : Option Nat} {os : List (Nat × Word)} {l : List (String × Value)}
    (hrst : l.lookup "rst" = some (.ofNat 64 (if t.isSome then ScanProg.torn else ScanProg.clean)))
    (hrgo : l.lookup "rgo" = some 1)
    (hsz : (rScan + ScanProg.sSize, .ofNat 64 J.length) ∈ os)
    (hpos : ∀ p, t = some p → (rScan + ScanProg.sPos, .ofNat 64 p) ∈ os)
    (hk : ∀ q ∈ os, rScan ≤ q.1 ∧ q.1 < rSlots) :
    Frag o [.ite (Syntax.eEq (rw rRecords) (Syntax.n 0))
        [.ite (Syntax.eEq (rw rNames) (Syntax.n 1)) (RecoverProg.fresh false) (refuse .noJournal [])]
        [rset rJournalEnd (sw ScanProg.sSize),
         .ite (Syntax.eEq (Syntax.v "rst") (Syntax.n ScanProg.torn))
           [rset rTorn (Syntax.n 1), rset rCut (sw ScanProg.sPos), rset rJournalEnd (sw ScanProg.sPos)] [],
         next 4]]
      (Mid A cfg J r s0 (scalars cfg r) os l) (POut A cfg J s0 (RecoverSpec.scanned r t)) := by
  have hn := nums
  have hko : ∀ x ∈ outOffs, ∀ q ∈ os, q.1 ≠ x := fun x hx q hq => by
    have := out_range x hx; have := hk q hq; omega
  unfold RecoverSpec.scanned
  refine frag_if o (C := .cmp .equal (rwE rRecords) (.const (.ofNat 64 0))) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
    (b := decide (r.records = 0)) (fun u hu => FramerCode.eval_eq (t := u) (x := r.records) (y := 0) hrc (by decide)
      (mid_rw h hu (by decide) (rw_lower (by decide))) rfl) (fun h0 => ?_) fun h0 => ?_
  · rw [if_pos (of_decide_eq_true h0)]
    refine frag_if o (C := .cmp .equal (rwE rNames) (.const (.ofNat 64 1))) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
      (b := decide (r.names = 1)) (fun u hu => FramerCode.eval_eq (t := u) (x := r.names) (y := 1) hnm (by decide)
        (mid_rw h hu (by decide) (rw_lower (by decide))) rfl) (fun h1 => ?_) fun h1 => ?_
    · -- the journal the directory's one file: a new store
      rw [if_pos (of_decide_eq_true h1)]
      refine frag_conseq (fresh_frag o h (by omega) false) (fun _ h => h) fun u ⟨hu, hz⟩ =>
        mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => ⟨fun h9 => by simp [RecoverSpec.startNew] at h9,
          hr.nameLen, hr.name, hr.unknown, hr.config, fun _ hf => by simp [RecoverSpec.startNew] at hf, hr.slots,
          fun _ x hx => by simpa [RecoverSpec.startNew, highOf] using hz x hx⟩) ?_
      exact vals_lookup hu.vals (by rw [lookup_cons_ne (by decide), lookup_without (by decide), hrgo])
    · -- other files and no record: no journal
      rw [if_neg (by simpa using h1)]
      refine frag_append (xs := [_]) (mid_out o h (x := rFault) (by decide) (hko _ (by decide))
        (E := .const (.ofNat 64 (faultCode .noJournal))) rfl fun _ _ => rfl) ?_
      exact frag_conseq (stop_frag o h refused (fun q hq => by
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · decide
          · exact hko _ (by decide) q hq)) (fun _ h => h)
        fun u hu => mid_end hu (fun _ _ => rfl) (fun hr => hr) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
          outs_lookup hu.outs rfl, trivial⟩
  · -- records: the journal's end, and a torn tail's place
    rw [if_neg (by simpa using h0)]
    have hRest : ∀ u : PancakeState σ, Rest A cfg J r u → ∀ r' : RSt,
        r'.phase = 4 → r'.name = r.name → r'.unknown = r.unknown →
        r'.scan = r.scan → r'.fresh = r.fresh → r'.commits = r.commits → Rest A cfg J r' u :=
            fun u hr r' e1 e2 e3 e4 e5 e6 =>
      ⟨fun h9 => by omega, e2 ▸ hr.nameLen, e2 ▸ hr.name, e3 ▸ hr.unknown, hr.config,
        fun _ hf => e4 ▸ hr.scan (by omega) (e5 ▸ hf), e6 ▸ hr.slots, fun h5 => by omega⟩
    refine frag_append (xs := [_]) (mid_set o h (x := rJournalEnd) (by decide) (sw_lower _)
      (val := .ofNat 64 r.jsize) fun u hu => by rw [mid_swOut h hu hsz (by decide) (by decide), hj]) ?_
    cases t with
    | none =>
      refine frag_append (xs := [_]) (frag_if o (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.torn)))
        rfl (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl mid_clock (b := false)
        (fun u hu => FramerCode.eval_eq (t := u) (a := .var "rst") (b := .const _) (x := ScanProg.clean)
          (y := ScanProg.torn) (by decide) (by decide) (vals_lookup hu.vals hrst) rfl) (fun e => absurd e (by decide))
        fun _ => frag_nil o fun _ h => h) ?_
      exact frag_conseq (mid_set o h (x := rPhase) (by decide) (E := .const (.ofNat 64 4)) rfl fun _ _ => rfl)
        (fun _ h => h) fun u hu => mid_end hu (offs_all (by and_intros <;> rfl))
          (fun hr => hRest u hr _ rfl rfl rfl rfl rfl rfl) (vals_lookup hu.vals hrgo)
    | some p =>
      have hp' := hpos p rfl
      refine frag_append (xs := [_]) (M := Mid A cfg J r s0 (upd (upd (upd (upd (scalars cfg r) rJournalEnd
        (.ofNat 64 r.jsize)) rTorn (.ofNat 64 1)) rCut (.ofNat 64 p)) rJournalEnd (.ofNat 64 p)) os l) (frag_if o
            (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.torn)))
        rfl (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl mid_clock (b := true)
        (fun u hu => FramerCode.eval_eq (t := u) (a := .var "rst") (b := .const _) (x := ScanProg.torn)
          (y := ScanProg.torn) (by decide) (by decide) (vals_lookup hu.vals hrst) rfl) (fun _ => ?_)
          fun e => absurd e (by decide)) ?_
      · refine frag_append (xs := [_]) (mid_set o h (x := rTorn) (by decide) (E := .const (.ofNat 64 1)) rfl
          fun _ _ => rfl) ?_
        refine frag_append (xs := [_]) (mid_set o h (x := rCut) (by decide) (sw_lower _) (val := .ofNat 64 p)
          fun u hu => mid_swOut h hu hp' (by decide) (by decide)) ?_
        exact mid_set o h (x := rJournalEnd) (by decide) (sw_lower _) (val := .ofNat 64 p)
          fun u hu => mid_swOut h hu hp' (by decide) (by decide)
      · exact frag_conseq (mid_set o h (x := rPhase) (by decide) (E := .const (.ofNat 64 4)) rfl fun _ _ => rfl)
          (fun _ h => h) fun u hu => mid_end hu (offs_all (by and_intros <;> rfl))
            (fun hr => hRest u hr _ rfl rfl rfl rfl rfl rfl) (vals_lookup hu.vals hrgo)

/-- A status other than octets wanted or a record read. -/
theorem otherStatus_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) {A : Word} {cfg : Config}
    {J : Bytes}
    {r : RSt} {s0 : PancakeState σ} {ws : Nat → Word} {os : List (Nat × Word)}
    {l : List (String × Value)} {code : Nat} (hc : code < 2 ^ 64) (hw : code ≠ ScanProg.wanted)
    (hr : code ≠ ScanProg.record) {rest : List Syntax.PStmt} {Q : Assn σ} (hQ : Safe.ClockFree Q)
    (h3 : Frag o rest (Mid A cfg J r s0 ws os (("rst", .ofNat 64 code) :: l)) Q) (hl3 : LowKK rest)
    (hd3 : declared rest = []) :
    Frag o [.ite (Syntax.eEq (Syntax.v "rst") (Syntax.n ScanProg.wanted)) (stop asksOctets)
      [.ite (Syntax.eEq (Syntax.v "rst") (Syntax.n ScanProg.record))
        [rset rRecords (Syntax.eAdd (rw rRecords) (Syntax.n 1)),
         .ite (Syntax.eEq (sw ScanProg.sType) (Syntax.n commitType)) (commitRead fail) []] rest]]
      (Mid A cfg J r s0 ws os (("rst", .ofNat 64 code) :: l)) Q := by
  refine frag_if o (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.wanted))) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_ite rfl (lowKK_append (xs := [_]) (lowK_any _ (k := .skip)
        (c := _) rfl)
      (lowKK_ite rfl (lowKK_commitRead hfl) (fun k => ⟨k, rfl⟩))) hl3) rfl rfl hQ (b := false)
    (fun u hu => by rw [rst_eval hc (by decide) u hu]; simp [hw]) (fun e => absurd e (by decide)) fun _ => ?_
  exact frag_if o (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.record))) rfl
    (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl)
      (lowKK_ite rfl (lowKK_commitRead hfl) (fun k => ⟨k, rfl⟩))) hl3 rfl hd3 hQ (b := false)
    (fun u hu => by rw [rst_eval hc (by decide) u hu]; simp [hr]) (fun e => absurd e (by decide)) fun _ => h3

/-- **Phase 3**: a step of the scanner, and what follows of what it gives. -/
theorem scanning_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PIn A cfg J r s0) (hp : r.phase = 3)
    (hfr : r.fresh = false) (hnm : r.names < 2 ^ 64) (hrc : r.records + 1 < 2 ^ 64) (hj : r.jsize = J.length)
    (hcm : r.commits.length < 2 ^ 62) :
    Frag o (RecoverProg.scanning fail) (Like s0) (POut A cfg J s0 (RecoverSpec.scanning cfg J r)) := by
  have hn := nums
  have hsn := snums
  have hb := h.toPBase
  obtain ⟨-, hv0⟩ := h.area.rest.scan (by omega) hfr
  rw [RecoverSpec.scanning]
  refine frag_append (scanStep_frag o hfl hfd h hp hfr) ?_
  have hst : ∀ (r' : RSt) (os : List (Nat × Word)) (code : Nat),
      (rScan + ScanProg.sStatus, BitVec.ofNat 64 code) ∈ os →
      Frag o [.assign "rst" (sw ScanProg.sStatus)] (Mid A cfg J r' s0 (scalars cfg r) os [("rgo", 1)])
        (Mid A cfg J r' s0 (scalars cfg r) os (("rst", .ofNat 64 code) :: without "rst" [("rgo", 1)])) :=
    fun r' os code hmem => mid_assign o hb (y := "rst") (by decide) (sw_lower _) fun u hu => by
      have e := hu.outs _ hmem
      dsimp only at e
      rw [mid_sw hb hu (by omega) (by omega), e]
  cases hs : stepSpec J r.scan <;> try dsimp only
  case want st' n =>
    refine frag_conseq (P0 := Mid A cfg J { r with scan := st' } s0 (scalars cfg r)
      [(rScan + ScanProg.sStatus, .ofNat 64 ScanProg.wanted), (rScan + ScanProg.sWant, .ofNat 64 n)] [("rgo", 1)]) ?_
      (fun u ⟨hk, ⟨hs1, ha, hs2⟩, hw, hrgo, hr⟩ => mid_after hk hw hrgo (hr st' fun _ _ => ⟨ha, valid_want0 hv0 hs⟩)
        (xs := [(ScanProg.sStatus, _), (ScanProg.sWant, _)]) ⟨hs1, hs2, trivial⟩ rfl) fun _ h => h
    refine frag_append (xs := [_]) (hst _ _ ScanProg.wanted (by simp)) ?_
    refine frag_if o (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.wanted))) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rest hfl) rfl rfl pout_clock
      (b := true) (fun u hu => rst_eval (by decide) (by decide) u hu) (fun _ => ?_) fun e => absurd e (by decide)
    exact frag_conseq (stop_frag o hb asksOctets (apart_of (by rfl))) (fun _ h => h)
      fun u hu => mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => hr)
        ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩
  case record rec st' =>
    obtain ⟨hb1, hb2, hbp, hfr', hlen', hrec⟩ := record_facts hv0 hs
    have hv' := (ScanRun.valid_record hv0 hs).1
    obtain ⟨pl, hpl⟩ : ∃ x, x = ScanRun.payloadOf (J.drop r.scan.pos) := ⟨_, rfl⟩
    obtain ⟨o', ho'⟩ : ∃ x, x = r.scan.pos - r.scan.base := ⟨_, rfl⟩
    rw [← hpl] at hfr' hlen' hrec
    have hfit : o' + 13 + pl.length ≤ ScanProg.windowMax := by have := hv0.len; omega
    let r1 : RSt := { r with scan := st', records := r.records + 1 }
    -- the commit's payload in the window
    have hplw : ∀ u : PancakeState σ, AreaAt (at_ A rScan) J st' u →
        BytesAt A (rScan + ScanProg.sWindow + o' + 13) pl u :=
      fun u ha k hk => by
        have hw := ha.window (o' + 13 + k) (by rw [hb2]; omega)
        rw [at_at, hb1] at hw
        rw [show rScan + ScanProg.sWindow + o' + 13 + k = rScan + (ScanProg.sWindow + (o' + 13 + k)) by omega, hw]
        congr 1
        have hk' : 13 + k < (J.drop r.scan.pos).length := by omega
        subst hpl
        rw [ScanRun.payload_get k hk hk', List.getElem_drop, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp at hk'; omega)]
        simp only [Option.getD_some]
        congr 1; omega
    refine frag_conseq (P0 := fun u => Mid A cfg J r1 s0 (scalars cfg r)
      [(rScan + ScanProg.sStatus, .ofNat 64 ScanProg.record), (rScan + ScanProg.sType, .ofNat 64 rec.type)]
      [("rgo", 1)] u ∧
      (∀ c, rec = .commit c → CommitIn A o' pl c u)) ?_
      (fun u ⟨hk, ⟨hs1, ha, hs2, hc⟩, hw, hrgo, hr⟩ => ⟨mid_after (r' := r1) hk hw hrgo
        { hr st' fun _ _ => ⟨ha, hv'⟩ with } (xs := [(ScanProg.sStatus, _), (ScanProg.sType, _)])
        ⟨hs1, hs2, trivial⟩ rfl, fun c e => ⟨by rw [ho', hpl]; exact hc c e, hplw u ha⟩⟩) fun _ h => h
    let CFr (u : PancakeState σ) : Prop := ∀ c, rec = .commit c → CommitIn A o' pl c u
    have hCFc : Safe.ClockFree CFr := fun _ _ h => h
    refine frag_append (xs := [_]) (mid_assign_and o hb (y := "rst") (by decide) (sw_lower _)
      (val := .ofNat 64 ScanProg.record) (fun u hu => by
        have e := hu.outs (rScan + ScanProg.sStatus, .ofNat 64 ScanProg.record) (by simp)
        dsimp only at e
        rw [mid_sw hb hu (by decide) (by omega), e]) hCFc (fun _ h => h)) ?_
    refine frag_if o (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.wanted))) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rest hfl) rfl rfl pout_clock (b := false)
      (fun u ⟨hu, _⟩ => by rw [rst_eval (by decide) (by decide) u hu]; rfl) (fun e => absurd e (by decide)) fun _ => ?_
    refine frag_if o (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.record))) rfl
      (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl)
        (lowKK_ite rfl (lowKK_commitRead hfl) (fun k => ⟨k, rfl⟩))) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl
      pout_clock (b := true) (fun u ⟨hu, _⟩ => by rw [rst_eval (by decide) (by decide) u hu]; rfl)
      (fun _ => ?_) fun e => absurd e (by decide)
    -- the record counted
    refine frag_append (xs := [_]) (mid_set_and o hb (x := rRecords) (by decide)
      (E := .op .add (rwE rRecords) (.const (.ofNat 64 1))) rfl (val := .ofNat 64 (r.records + 1))
      (F := CFr) (fun u hu _ => by
        simp only [eval, mid_rw hb hu (x := rRecords) (by decide) (rw_lower (by decide))]
        rw [show scalars cfg r rRecords = .ofNat 64 r.records from rfl, BitVec.ofNat_add]) hCFc
      fun u v hf c e => commitIn_stW h.hA (hf c e) (by
        cases e; obtain ⟨-, -, -, hgc, -⟩ := ok_bounds (decodeCommit_ok (ScanRun.recordOf_commit hrec)); exact hgc) hfit
        (.inl (by omega)) (by omega) v) ?_
    -- a commit noted
    have hws1 : ∀ x ∈ scalarOffs, upd (scalars cfg r) rRecords (.ofNat 64 (r.records + 1)) x = scalars cfg r1 x :=
      offs_all (by and_intros <;> rfl)
    cases rec with
    | commit c =>
      have hdec := ScanRun.recordOf_commit hrec
      refine frag_if o (C := .cmp .equal (swE ScanProg.sType) (.const (.ofNat 64 commitType)))
        (by simp [sw_lower, Lower.lowerExp, Syntax.eEq, Syntax.n]) (lowKK_commitRead hfl) (fun k => ⟨k, rfl⟩) rfl rfl
        pout_clock (b := true) (fun u ⟨hu, _⟩ => by
          have e := hu.outs (rScan + ScanProg.sType, .ofNat 64 (Record.commit c).type) (by simp)
          dsimp only at e
          exact FramerCode.eval_eq (t := u) (x := commitType) (y := commitType) (by decide) (by decide)
            (by rw [mid_sw hb hu (by decide) (by omega), e]; rfl) rfl) (fun _ => ?_) fun e => absurd e (by decide)
      exact frag_conseq (commitRead_frag o hfl hfd hb (r1 := r1) hp hws1 (fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl <;> exact ⟨by dsimp only; omega, by dsimp only; omega⟩) (by
          rw [lookup_cons_ne (by decide), lookup_without (by decide)]; rfl) (by
          simp [ScanRun.Outside, crNames, ScanRun.sipNames, without]) (decodeCommit_ok hdec) hdec hfit hcm)
        (fun u ⟨hu, hf⟩ => ⟨hu, hf c rfl⟩) fun _ h => h
    | format k =>
      refine frag_if o (C := .cmp .equal (swE ScanProg.sType) (.const (.ofNat 64 commitType)))
        (by simp [sw_lower, Lower.lowerExp, Syntax.eEq, Syntax.n]) (lowKK_commitRead hfl) (fun k => ⟨k, rfl⟩) rfl rfl
        pout_clock (b := false) (fun u ⟨hu, _⟩ => by
          have e := hu.outs (rScan + ScanProg.sType, .ofNat 64 (Record.format k).type) (by simp)
          dsimp only at e
          exact FramerCode.eval_eq (t := u) (x := formatType) (y := commitType) (by decide) (by decide)
            (by rw [mid_sw hb hu (by decide) (by omega), e]; rfl) rfl) (fun e => absurd e (by decide)) fun _ => ?_
      exact frag_nil o fun u ⟨hu, _⟩ => mid_end hu hws1 (fun hr => hr) (vals_lookup hu.vals rfl)
    | start =>
      refine frag_if o (C := .cmp .equal (swE ScanProg.sType) (.const (.ofNat 64 commitType)))
        (by simp [sw_lower, Lower.lowerExp, Syntax.eEq, Syntax.n]) (lowKK_commitRead hfl) (fun k => ⟨k, rfl⟩) rfl rfl
        pout_clock (b := false) (fun u ⟨hu, _⟩ => by
          have e := hu.outs (rScan + ScanProg.sType, .ofNat 64 Record.start.type) (by simp)
          dsimp only at e
          exact FramerCode.eval_eq (t := u) (x := startType) (y := commitType) (by decide) (by decide)
            (by rw [mid_sw hb hu (by decide) (by omega), e]; rfl) rfl) (fun e => absurd e (by decide)) fun _ => ?_
      exact frag_nil o fun u ⟨hu, _⟩ => mid_end hu hws1 (fun hr => hr) (vals_lookup hu.vals rfl)

  case clean =>
    refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r)
      [(rScan + ScanProg.sStatus, .ofNat 64 ScanProg.clean), (rScan + ScanProg.sSize, .ofNat 64 J.length)]
      [("rgo", 1)]) ?_ (fun u ⟨hk, ⟨hs1, ha⟩, hw, hrgo, hr⟩ => mid_after hk hw hrgo
        (hr r.scan fun _ _ => ⟨ha, hv0⟩ : Rest A cfg J r u) (xs := [(ScanProg.sStatus, _), (ScanProg.sSize, _)])
        ⟨hs1, ha.size, trivial⟩ rfl) fun _ h => h
    refine frag_append (xs := [_]) (hst _ _ ScanProg.clean (by simp)) ?_
    refine otherStatus_frag o hfl (code := ScanProg.clean) (by decide) (by decide) (by decide) pout_clock ?_
      (lowK_any _ (k := .skip) (c := _) rfl) rfl
    refine frag_if o (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.corrupt))) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := false)
      (fun u hu => by rw [rst_eval (by decide) (by decide) u hu]; rfl) (fun e => absurd e (by decide)) fun _ => ?_
    exact ended_frag o hb hp hnm hj (by omega) (t := none)
      (os := [(rScan + ScanProg.sStatus, .ofNat 64 ScanProg.clean), (rScan + ScanProg.sSize, .ofNat 64 J.length)])
      (l := ("rst", .ofNat 64 ScanProg.clean) :: without "rst" [("rgo", 1)]) rfl rfl (by simp)
      (fun _ e => nomatch e) fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  case stop e =>
    cases e <;> try dsimp only
    case clean => exact frag_unsat (lowKK_append (xs := [_]) (lowK_any _ (k := .skip) (c := _) rfl)
        (lowKK_ite rfl (lowK_any _ (k := .skip) (c := _) rfl) (lowKK_rest hfl))) fun u hu => hu.2.1
    case torn p =>
      refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r)
        [(rScan + ScanProg.sStatus, .ofNat 64 ScanProg.torn), (rScan + ScanProg.sPos, .ofNat 64 p),
         (rScan + ScanProg.sSize, .ofNat 64 J.length)] [("rgo", 1)]) ?_
        (fun u ⟨hk, ⟨hs1, hs2, ha, _⟩, hw, hrgo, hr⟩ => mid_after hk hw hrgo
          (hr r.scan fun _ _ => ⟨ha, hv0⟩ : Rest A cfg J r u)
          (xs := [(ScanProg.sStatus, _), (ScanProg.sPos, _), (ScanProg.sSize, _)])
          ⟨hs1, hs2, ha.size, trivial⟩ rfl) fun _ h => h
      refine frag_append (xs := [_]) (hst _ _ ScanProg.torn (by simp)) ?_
      refine otherStatus_frag o hfl (code := ScanProg.torn) (by decide) (by decide) (by decide) pout_clock ?_
        (lowK_any _ (k := .skip) (c := _) rfl) rfl
      refine frag_if o (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.corrupt))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := false)
        (fun u hu => by rw [rst_eval (by decide) (by decide) u hu]; rfl) (fun e => absurd e (by decide)) fun _ => ?_
      exact ended_frag o hb hp hnm hj (by omega) (t := some p)
        (os := [(rScan + ScanProg.sStatus, .ofNat 64 ScanProg.torn), (rScan + ScanProg.sPos, .ofNat 64 p),
          (rScan + ScanProg.sSize, .ofNat 64 J.length)])
        (l := ("rst", .ofNat 64 ScanProg.torn) :: without "rst" [("rgo", 1)]) rfl rfl
        (by simp) (fun _ e => by cases e; simp) fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl <;> exact ⟨by dsimp only; omega, by dsimp only; omega⟩
    case corrupt p w =>
      refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r)
        [(rScan + ScanProg.sStatus, .ofNat 64 ScanProg.corrupt), (rScan + ScanProg.sPos, .ofNat 64 p),
         (rScan + ScanProg.sWhy, .ofNat 64 (ScanProg.whyCode w))] [("rgo", 1)]) ?_
        (fun u ⟨hk, ⟨hs1, hs2, hs3, ha⟩, hw, hrgo, hr⟩ => mid_after hk hw hrgo
          (hr r.scan fun _ _ => ⟨ha, hv0⟩ : Rest A cfg J r u)
          (xs := [(ScanProg.sStatus, _), (ScanProg.sPos, _), (ScanProg.sWhy, _)])
          ⟨hs1, hs2, hs3, trivial⟩ rfl) fun _ h => h
      refine frag_append (xs := [_]) (hst _ _ ScanProg.corrupt (by simp)) ?_
      refine otherStatus_frag o hfl (code := ScanProg.corrupt) (by decide) (by decide) (by decide) pout_clock ?_
        (lowK_any _ (k := .skip) (c := _) rfl) rfl
      refine frag_if o (C := .cmp .equal (.var "rst") (.const (.ofNat 64 ScanProg.corrupt))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := true)
        (fun u hu => by rw [rst_eval (by decide) (by decide) u hu]; rfl) (fun _ => ?_) fun e => absurd e (by decide)
      refine frag_append (xs := [_]) (mid_out o hb (x := rFaultA) (by decide)
        (apart_of (by rfl)) (sw_lower _) (val := .ofNat 64 p)
        fun u hu => mid_swOut hb hu (by simp) (by decide) (by decide)) ?_
      refine frag_append (xs := [_]) (mid_out o hb (x := rFaultB) (by decide)
        (apart_of (by rfl)) (sw_lower _) (val := .ofNat 64 (ScanProg.whyCode w))
        fun u hu => mid_swOut hb hu (by simp) (by decide) (by decide)) ?_
      refine frag_append (xs := [_]) (mid_out o hb (x := rFault) (by decide)
        (apart_of (by rfl)) (E := .const (.ofNat 64 (faultCode (.journal 0 .short)))) rfl
        fun _ _ => rfl) ?_
      exact frag_conseq (stop_frag o hb refused (apart_of (by rfl))) (fun _ h => h)
        fun u hu => mid_end hu (fun _ _ => rfl) (fun hr => hr) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
          outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩

/-! ## The premises can hold -/

section Witness

/-- The step's locals at a phase's start, the area at 0. -/
def wLocals (x : String) : Option Value :=
  if x = "jsc" then some (at_ 0 rScan) else if x = "rgo" then some 1 else some 0

/-- A state of the area all zero, every word addressable. -/
def wState : PancakeState Unit := { bareState () with locals := wLocals }

/-- A configuration of no group, its key all zero. -/
def wCfg : Config := ⟨[], List.replicate 16 0⟩

theorem load_zero (be : Bool) (a : Word) : memLoadByte (fun _ => 0) (fun _ => true) be a = some 0 := by
  simp [memLoadByte, getByte]

theorem rdom_witness : RDom 0 wState.memaddrs := fun _ _ => rfl

theorem words_witness : Words 0 (scalars wCfg RSt.start) wState := offs_all (p := fun x => _ = _)
  (by and_intros <;> rfl)

theorem outs_witness : Outs 0 [] wState := fun _ h => nomatch h

theorem bytesAt_witness : BytesAt 0 rKey (List.replicate 16 0) wState := fun i hi => by
  simp only [List.length_replicate] at hi
  rw [List.getElem_replicate]; exact load_zero _ _

theorem cfgAt_witness : CfgAt 0 wCfg wState :=
  ⟨bytesAt_witness, rfl, by decide, fun _ h => absurd h (by simp [wCfg]), fun _ h => absurd h (by simp [wCfg]),
    fun _ h => absurd h (by simp [wCfg])⟩

theorem rest_witness : Rest 0 wCfg [] RSt.start wState :=
  ⟨fun h => by simp [RSt.start] at h, by decide, fun _ h => absurd h (by simp [RSt.start]),
    fun _ h => by simp [RSt.start] at h, cfgAt_witness, fun h => absurd h (by decide),
    fun _ h => absurd h (by simp [RSt.start]), fun h => absurd h (by decide)⟩

theorem rat_witness : RAt 0 wCfg [] RSt.start wState := ⟨words_witness, rest_witness⟩

theorem pbase_witness : PBase 0 wState :=
  ⟨by decide, rdom_witness, rfl, rfl, rfl, fun y _ => by
    simp only [wState, wLocals]; split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩⟩

theorem pin_witness : PIn 0 wCfg [] RSt.start wState := ⟨pbase_witness, rfl, rat_witness, by decide⟩

theorem mid_witness : Mid 0 wCfg [] RSt.start wState (scalars wCfg RSt.start) [] [] wState :=
  ⟨ScanRun.kept_refl _ _ _, words_witness, outs_witness, (fun _ h => nomatch h), rest_witness, (fun _ h => nomatch h)⟩

theorem known_witness : Known rStatus := .inl (by decide)

theorem far_witness : Far RSt.start rUnknownLen := .inl ⟨Nat.le_refl _, by decide, rfl⟩

theorem away_witness : Away RSt.start rStatus := .inl (.inl (by decide))

theorem highZ_witness : HighZ 0 wState := fun _ _ => rfl

theorem octetsAt_witness : OctetsAt 0 rFaultAt rFaultLen [] wState :=
  ⟨0, rfl, rfl, by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The area of a step done. -/
def wDone : PancakeState Unit := { wState with memory := fun a => if a = at_ 0 rStatus then .ofNat 64 done else 0 }

theorem outR_witness : OutR 0 [] RSt.start .done wDone := by simp [OutR, wDone]

/-- The area at phase 3 with no journal read yet: the phase's word, all else zero. -/
def w3State : PancakeState Unit :=
  { wState with memory := fun a => if a = at_ 0 rPhase then .ofNat 64 3 else 0 }

/-- The state of phase 3 the area holds. -/
def r3 : RSt := { RSt.start with phase := 3 }

theorem w3_zero {a : Word} (h : a ≠ at_ 0 rPhase) : w3State.memory a = 0 := if_neg h

theorem pin3_witness : PIn 0 wCfg [] r3 w3State := by
  have e1 : RecoverProg.size = 1730792 := rfl
  have e2 : rPhase = 8 := rfl
  have e3 : rKey = 616 := rfl
  have hz : ∀ x, x < RecoverProg.size → x ≠ rPhase → w3State.memory (at_ 0 x) = 0 := fun x hx hne =>
    w3_zero (ScanRun.at_ne (by omega) (by decide) hne)
  have hload : ∀ x, x < RecoverProg.size → x / 8 * 8 ≠ rPhase →
      memLoadByte w3State.memory w3State.memaddrs w3State.be (at_ 0 x) = some 0 := fun x hx hne => by
    simp only [memLoadByte, align_at (by decide : (0 : Word).toNat % 8 = 0)]
    rw [hz _ (by omega) hne]; simp [w3State, wState, bareState, getByte]
  refine ⟨⟨by decide, rdom_witness, rfl, rfl, rfl, pbase_witness.bound⟩, rfl, ⟨?_, ?_⟩, by decide⟩
  · refine offs_all (p := fun x => w3State.memory (at_ 0 x) = scalars wCfg r3 x) ?_
    and_intros <;> first | (simp [w3State]; rfl) | (rw [hz _ (by decide) (by decide)]; rfl)
  · refine ⟨fun h => by simp [r3, RSt.start] at h, by decide, fun i hi => absurd hi (by simp [r3, RSt.start]),
      fun _ h => by simp [r3, RSt.start] at h, ⟨fun i hi => ?_, rfl, by decide, fun _ h => absurd h (by simp [wCfg]),
        fun _ h => absurd h (by simp [wCfg]), fun _ h => absurd h (by simp [wCfg])⟩, fun _ _ => ⟨?_, ?_⟩,
      fun _ h => absurd h (by simp [r3, RSt.start]), fun h => absurd h (by decide)⟩
    · show memLoadByte _ _ _ _ = some (List.replicate 16 (0 : BitVec 8))[i]
      simp only [wCfg, List.length_replicate] at hi
      rw [List.getElem_replicate]; exact hload _ (by omega) (by omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ h => absurd h (by simp [r3, RSt.start, St.start]),
        fun _ h => by simp [r3, RSt.start, St.start] at h⟩ <;> rw [at_at, hz _ (by decide) (by decide)] <;> rfl
    · exact ScanRun.valid_start []

/-- A configuration of the group `[97]`, its key all zero. -/
def oCfg : Config := ⟨[[97]], List.replicate 16 0⟩

/-- An area holding that configuration: the group's length word and its name. -/
def gState : PancakeState Unit :=
  { wState with memory := fun a => if a = at_ 0 rGroups then 1 else putBytes (fun _ => 0) 0 (rGroups + 8) [97] a }

theorem cfgAt_group_witness : CfgAt 0 oCfg gState := by
  have e1 : rGroups = 640 := rfl
  have e2 : rKey = 616 := rfl
  have hload : ∀ x, x < 2 ^ 60 → x / 8 * 8 ≠ rGroups → memLoadByte gState.memory gState.memaddrs gState.be (at_ 0 x) =
      memLoadByte (putBytes (fun _ => 0) 0 (rGroups + 8) [97]) (fun _ => true) false (at_ 0 x) := fun x hx hne =>
    load_eq (by rw [align_at (by decide)]; exact if_neg (ScanRun.at_ne (by omega) (by decide) hne))
  refine ⟨fun i hi => ?_, rfl, by decide, fun g hg => ?_, fun g hg => ?_, fun g hg => ?_⟩
  · show memLoadByte _ _ _ _ = some (List.replicate 16 (0 : BitVec 8))[i]
    have hi : i < 16 := hi
    rw [List.getElem_replicate, hload _ (by omega) (by omega), load_putBytes_other (.inl (by omega)) (by decide)
      (by omega)]
    exact load_zero _ _
  · match g, hg with
    | 0, _ =>
      show (if at_ 0 (rGroups + 0 * rGroupSlot) = at_ 0 rGroups then (1 : Word) else
        putBytes (fun _ => 0) 0 (rGroups + 8) [97] (at_ 0 (rGroups + 0 * rGroupSlot))) = BitVec.ofNat 64 1
      rw [if_pos (by rw [Nat.zero_mul, Nat.add_zero])]; rfl
    | _ + 1, h => exact absurd h (by simp [oCfg])
  · match g, hg with
    | 0, _ => show [97].length ≤ groupNameMax; decide
    | _ + 1, h => exact absurd h (by simp [oCfg])
  · match g, hg with
    | 0, _ =>
      show BytesAt 0 (rGroups + 8) [97] gState
      intro i hi
      have hi' : i < 1 := hi
      rw [hload _ (by omega) (by omega)]
      exact load_putBytes (by decide) i hi
    | _ + 1, h => exact absurd h (by simp [oCfg])

/-- A commit of one group, as the store writes it. -/
def oCommit : Commit := ⟨1, [60], [⟨[97], 1⟩], 0, 0, 0⟩

theorem oCommit_ok : oCommit.ok = true := by decide

theorem oCommit_dec : decodeCommit oCommit.payload = some oCommit := decode_payload _ oCommit_ok

/-- Where the payload starts: the window's start, past the frame's header. -/
def oBase : Nat := rScan + ScanProg.sWindow + 0 + 13

/-- That commit read by the scanner and noted in slot 0: the scanner's words and payload, the slot's words, its
Message-ID. -/
def oMem (a : Word) : Word :=
  if a = at_ 0 (rScan + ScanProg.sSeq) then 1 else
  if a = at_ 0 (rScan + ScanProg.sIdAt) then 22 else
  if a = at_ 0 (rScan + ScanProg.sIdLen) then 1 else
  if a = at_ 0 (rScan + ScanProg.sGroupCount) then 1 else
  if a = at_ 0 (rScan + ScanProg.sGroups) then 25 else
  if a = at_ 0 (rScan + ScanProg.sGroups + 8) then 1 else
  if a = at_ 0 (rScan + ScanProg.sGroups + 16) then 1 else
  if a = at_ 0 (slotAt 0 + slotSeq) then 1 else
  if a = at_ 0 (slotAt 0 + slotSizes) then (BitVec.ofNat 64 0 <<< 32) ||| .ofNat 64 0 else
  if a = at_ 0 (slotAt 0 + slotMisc) then
    ((BitVec.ofNat 64 0 <<< 16) ||| (BitVec.ofNat 64 1 <<< 8)) ||| .ofNat 64 1 else
  if a = at_ 0 (slotAt 0 + slotTag) then (SipHash.tag oCfg.key oCommit.messageId).toBitVec else
  if a = at_ 0 (slotAt 0 + slotGroups) then (BitVec.ofNat 64 (groupIx oCfg [97]) <<< 32) ||| .ofNat 64 1 else
  putBytes (putBytes (fun _ => 0) 0 oBase oCommit.payload) 0 (slotAt 0 + slotId) oCommit.messageId a

/-- The area with that commit read and noted. -/
def oRead : PancakeState Unit := { wState with memory := oMem }

/-- The memory of the two writes of octets. -/
def oPut : Word → Word :=
  putBytes (putBytes (fun _ => 0) 0 oBase oCommit.payload) 0 (slotAt 0 + slotId) oCommit.messageId

/-- Past the words of the scanner's and the slot's, the octets written. -/
theorem oMem_put {w : Nat} (hw : 7600 ≤ w ∧ w < 7800 ∨ w = 27016) : oMem (at_ 0 w) = oPut (at_ 0 w) := by
  have e1 : rScan = 5760 := rfl
  have e2 : slotAt 0 = 26856 := rfl
  have f1 : ScanProg.sSeq = 80 := rfl
  have f2 : ScanProg.sIdAt = 88 := rfl
  have f3 : ScanProg.sIdLen = 96 := rfl
  have f4 : ScanProg.sGroupCount = 104 := rfl
  have f5 : ScanProg.sGroups = 136 := rfl
  have f6 : slotSeq = 0 := rfl
  have f7 : slotSizes = 8 := rfl
  have f8 : slotMisc = 16 := rfl
  have f9 : slotTag = 152 := rfl
  have f10 : slotGroups = 24 := rfl
  simp only [oMem]
  rw [if_neg (ScanRun.at_ne (x := w) (y := rScan + ScanProg.sSeq) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := rScan + ScanProg.sIdAt) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := rScan + ScanProg.sIdLen) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := rScan + ScanProg.sGroupCount) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := rScan + ScanProg.sGroups) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := rScan + ScanProg.sGroups + 8) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := rScan + ScanProg.sGroups + 16) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := slotAt 0 + slotSeq) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := slotAt 0 + slotSizes) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := slotAt 0 + slotMisc) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := slotAt 0 + slotTag) (by omega) (by decide) (by omega)),
    if_neg (ScanRun.at_ne (x := w) (y := slotAt 0 + slotGroups) (by omega) (by decide) (by omega))]
  rfl

theorem load_oRead {z : Nat} (hz : 7600 ≤ z / 8 * 8 ∧ z / 8 * 8 < 7800 ∨ z / 8 * 8 = 27016) :
    memLoadByte oRead.memory oRead.memaddrs oRead.be (at_ 0 z) = memLoadByte oPut (fun _ => true) false (at_ 0 z) :=
  load_eq (by rw [align_at (by decide)]; exact oMem_put hz)

theorem commitIn_witness : CommitIn 0 0 oCommit.payload oCommit oRead :=
  ⟨⟨by decide, by decide, by decide, by decide, fun g hg => by
      obtain rfl : g = 0 := by simp [oCommit] at hg; omega
      exact ⟨12, by decide, by decide +revert, by decide +revert, by decide +revert, by decide +revert⟩, by decide,
      by decide, by decide⟩,
    fun i hi => by
      have hl : oCommit.payload.length = 29 := by decide
      have hb : oBase = 7701 := rfl
      rw [hl] at hi
      show memLoadByte oRead.memory oRead.memaddrs oRead.be (at_ 0 (oBase + i)) = _
      rw [load_oRead (by omega)]
      unfold oPut
      have e3 : slotAt 0 + slotId = 27016 := rfl
      rw [load_putBytes_other (.inl (by omega)) (by decide) (by omega), load_putBytes (by omega) i (by omega)]⟩

theorem scanAt_witness : ScanAt 0 oRead [(ScanProg.sSeq, 1)] := ⟨by decide, trivial⟩

theorem slotWords_witness : SlotWords 0 (slotAt 0) oCommit oRead := ⟨by decide, by decide, by decide⟩

theorem headIn_witness : HeadIn 0 0 oCommit.payload (slotAt 0) oCommit oRead :=
  ⟨commitIn_witness, slotWords_witness, fun i hi => by
    have hl : oCommit.messageId.length = 1 := rfl
    rw [hl] at hi
    have e2 : slotAt 0 + slotId = 27016 := rfl
    rw [load_oRead (by omega)]
    unfold oPut
    exact load_putBytes (by decide) i (by omega)⟩

theorem tagIn_witness : TagIn 0 oCfg 0 oCommit.payload (slotAt 0) oCommit oRead := by
  refine ⟨headIn_witness, ?_⟩
  show oMem (at_ 0 (slotAt 0 + slotTag)) = _
  simp only [oMem]
  have hne : ∀ y, y < 2 ^ 60 → y ≠ slotAt 0 + slotTag → ¬at_ 0 (slotAt 0 + slotTag) = at_ 0 y :=
    fun y hy h => ScanRun.at_ne (by decide) (by omega) (Ne.symm h)
  rw [if_neg (hne (rScan + ScanProg.sSeq) (by decide) (by decide)),
    if_neg (hne (rScan + ScanProg.sIdAt) (by decide) (by decide)),
    if_neg (hne (rScan + ScanProg.sIdLen) (by decide) (by decide)),
    if_neg (hne (rScan + ScanProg.sGroupCount) (by decide) (by decide)),
    if_neg (hne (rScan + ScanProg.sGroups) (by decide) (by decide)),
    if_neg (hne (rScan + ScanProg.sGroups + 8) (by decide) (by decide)),
    if_neg (hne (rScan + ScanProg.sGroups + 16) (by decide) (by decide)),
    if_neg (hne (slotAt 0 + slotSeq) (by decide) (by decide)),
    if_neg (hne (slotAt 0 + slotSizes) (by decide) (by decide)),
    if_neg (hne (slotAt 0 + slotMisc) (by decide) (by decide)), if_pos trivial]

theorem groupsIn_witness : GroupsIn 0 oCfg (slotAt 0) oCommit 1 oRead := fun g hg _ => by
  revert g; decide

theorem slotR_witness : SlotR 0 oCfg 0 oCommit oRead :=
  ⟨slotWords_witness.1, slotWords_witness.2.1, slotWords_witness.2.2, tagIn_witness.2, by decide,
    headIn_witness.2.2, by decide, fun g hg => groupsIn_witness g hg (by simp [oCommit] at hg; omega)⟩

theorem reads_witness : Reads RSt.start rName := .inr (.inl ⟨Nat.le_refl _, by decide⟩)

theorem unkNoted_witness : UnkNoted 0 RSt.start (some []) wState := fun x hx _ => by
  cases hx
  exact ⟨rfl, by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

end Witness

end DN.News.RecoverArea
