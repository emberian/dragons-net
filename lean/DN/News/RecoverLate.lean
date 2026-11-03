-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverSlots

/-!
# DN.News.RecoverLate

Recovery's phases 5 to 13 as the program runs them are `RecoverSpec`'s. Files, next number, torn tail, second pass, a
final set aside, a new journal and the end.
-/

namespace DN.News.RecoverArea

open DN.Compiler DN.Compiler.Wp DN.Compiler.Frag DN.News.Journal DN.News.Recovery
open DN.News.RecoverProg
open DN.News.RecoverSpec (RSt)
open DN.News.ScanRun (St AreaAt Valid at_ vals_lookup kept_has without frag_if kept_skip e_ne)
open DN.News.FramerCode (bw ev_var ult_eval)

variable {σ : Type}

/-- **Phase 5**, each commit's final file, there and of its size, in the journal's order. -/
theorem files_frag (o : Oracle σ) {fail : List Syntax.PStmt} (hfl : LowKK fail) (hfd : declared fail = [])
    {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ} (h : PIn A cfg J r s0)
    (hp : r.phase = 5) (hok : ∀ c ∈ r.commits, c.ok = true) (hcap : r.commits.length ≤ capacity)
    (hil : r.i ≤ r.commits.length) (hw : r.wait = true → r.i < r.commits.length ∧ r.fileSize < 2 ^ 64) :
    Frag o (RecoverProg.files fail) (Like s0) (POut A cfg J s0 (RecoverSpec.files r)) := by
  have hb := h.toPBase
  have hn := nums
  refine from_start h ?_
  unfold RecoverProg.files
  rw [List.append_assoc]
  refine frag_append (xs := [_]) (mid_assign o hb (y := "ri") (by decide) (rw_lower (by decide))
    (val := .ofNat 64 r.i) fun u hu => by rw [mid_rw hb hu (by decide) (rw_lower (by decide))]; rfl) ?_
  refine frag_append (xs := [_]) (kept_skip o hfl hfd (by decide) mid_clock fun u hu =>
    ⟨r.i, vals_lookup hu.vals rfl, by have : capacity = 4096 := rfl; omega⟩) ?_
  refine frag_append (xs := held "rcm") (held_frag o hb rfl hcap) ?_
  refine frag_if o (C := rwE rWait) (rw_lower (by decide)) (lowKK_append (xs := [_]) (lowKK_kept hfl _ _)
    (lowK_any _ (k := .skip) (c := _) rfl)) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := r.wait)
    (fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) (fun hw' => ?_) fun hw' => ?_
  · -- a file asked about: there, and of its size
    obtain ⟨hi, hfs⟩ := hw hw'
    have hic : r.i < capacity := by omega
    rw [RecoverSpec.files, List.getElem?_eq_getElem hi]
    simp only [hw', if_true]
    obtain ⟨-, -, -, -, -, hfsz, -, -⟩ := ok_bounds (hok _ (List.getElem_mem hi))
    refine frag_append (xs := [_]) (kept_skip o hfl hfd (by decide) mid_clock fun u hu =>
      ⟨r.i, vals_lookup hu.vals rfl, by have : capacity = 4096 := rfl; omega⟩) ?_
    refine frag_append (xs := [_]) (mid_slotAt o hb (y := "rsl") (by decide) (x := "ri") (i := r.i) rfl) ?_
    refine frag_append (xs := [_]) (mid_set o hb (x := rWait) (by decide) (E := .const (.ofNat 64 0)) rfl
      (val := .ofNat 64 0) fun _ _ => rfl) ?_
    have hr' : ∀ (u : PancakeState σ) (r' : RSt), r'.phase = r.phase → r'.seq = r.seq → r'.name = r.name →
        r'.unknown = r.unknown → r'.scan = r.scan → r'.fresh = r.fresh → r'.commits = r.commits →
        Rest A cfg J r u → Rest A cfg J r' u := fun u r' e1 e2 e3 e4 e5 e6 e7 hr =>
      rest_phase hr (by omega) (fun h9 => ⟨e2, e1 ▸ h9⟩) e3 e4 e5 e6 e7
    cases hf : r.found
    · -- missing
      simp only [Bool.not_false, if_true]
      refine frag_if o (C := .cmp .equal (rwE rFound) (.const (.ofNat 64 0))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := true)
        (fun u hu => FramerCode.eval_eq (x := 0) (y := 0) (by decide) (by decide)
          (by rw [mid_rw hb hu (by decide) (rw_lower (by decide))]; show some (bw r.found) = _; rw [hf]; rfl) rfl)
        (fun _ => ?_) fun e => absurd e (by decide)
      refine frag_append (xs := [_]) (mid_out o hb (x := rFaultA) (by decide) apart_nil (E := slotWE slotSeq)
        (slotW_lower _) (val := .ofNat 64 r.commits[r.i].seq) fun u hu =>
          (slotP_eval hb hu hic (p := "rsl") rfl (by decide) (by decide)).trans
              (congrArg some (hu.rest.slots r.i hi hic).seq)) ?_
      refine frag_conseq (refused_frag o hb (.missingFile 0) (by rfl)) (fun _ h => h) fun u hu => ?_
      exact mid_end hu (offs_all (by and_intros <;> first | rfl | (show bw r.found = _; rw [hf]; rfl)))
        (hr' u _ rfl rfl rfl rfl rfl rfl rfl)
        ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      refine frag_if o (C := .cmp .equal (rwE rFound) (.const (.ofNat 64 0))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := false)
        (fun u hu => FramerCode.eval_eq (x := 1) (y := 0) (by decide) (by decide)
          (by rw [mid_rw hb hu (by decide) (rw_lower (by decide))]; show some (bw r.found) = _; rw [hf]; rfl) rfl)
        (fun e => absurd e (by decide)) fun _ => ?_
      refine frag_if o (C := .cmp .equal (.cmp .equal (rwE rFileSize)
          (.op .and_ (slotWE slotSizes) (.const (.ofNat 64 (2 ^ 32 - 1))))) (.const 0)) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
        (b := decide (r.fileSize ≠ r.commits[r.i].fileSize))
        (fun u hu => e_ne hfs (by omega) (mid_rw hb hu (by decide) (rw_lower (by decide))) (by
          simp only [eval, slotP_eval hb hu hic (p := "rsl") rfl (x := slotSizes) (by decide) (by decide)]
          rw [(hu.rest.slots r.i hi hic).sizes, sizes_low hfsz])) (fun e => ?_) fun e => ?_
      · rw [if_pos (of_decide_eq_true e)]
        refine frag_append (xs := [_]) (mid_out o hb (x := rFaultA) (by decide) apart_nil (E := slotWE slotSeq)
          (slotW_lower _) (val := .ofNat 64 r.commits[r.i].seq) fun u hu =>
            (slotP_eval hb hu hic (p := "rsl") rfl (by decide) (by decide)).trans
                (congrArg some (hu.rest.slots r.i hi hic).seq)) ?_
        refine frag_conseq (refused_frag o hb (.wrongSize 0) (by rfl)) (fun _ h => h) fun u hu => ?_
        exact mid_end hu (offs_all (by and_intros <;> first | rfl | (show bw r.found = _; rw [hf]; rfl)))
          (hr' u _ rfl rfl rfl rfl rfl rfl rfl)
          ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩
      · rw [if_neg (by simpa using of_decide_eq_false e)]
        refine frag_conseq (mid_set o hb (x := rI) (by decide) (E := .op .add (.var "ri") (.const (.ofNat 64 1))) rfl
          (val := .ofNat 64 (r.i + 1)) fun u hu => by
            simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add]) (fun _ h => h) fun u hu => ?_
        exact mid_end hu (offs_all (by and_intros <;> first | rfl | (show bw r.found = _; rw [hf]; rfl)))
          (hr' u _ rfl rfl rfl rfl rfl rfl rfl) (vals_lookup hu.vals rfl)
  · -- the next file asked about, or the next phase
    have hw0 : r.wait = false := by simpa using hw'
    refine frag_if o (C := .cmp .less (.var "ri") (.var "rcm")) rfl (lowK_any _ (k := .skip) (c := _) rfl)
      (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := decide (r.i < r.commits.length))
      (fun u hu => FramerCode.eval_lt (x := r.i) (y := r.commits.length) (by omega) (by omega)
        (ev_var (vals_lookup hu.vals rfl)) (ev_var (vals_lookup hu.vals rfl))) (fun e => ?_) fun e => ?_
    · have hi : r.i < r.commits.length := of_decide_eq_true e
      have hic : r.i < capacity := by omega
      rw [RecoverSpec.files, List.getElem?_eq_getElem hi]
      simp only [hw0, Bool.false_eq_true, if_false]
      refine frag_append (xs := [_]) (mid_slotAt o hb (y := "rsl") (by decide) (x := "ri") (i := r.i) rfl) ?_
      refine frag_append (xs := [_]) (mid_seq o hb (by omega) apart_nil (E := slotWE slotSeq) (slotW_lower _)
        (val := .ofNat 64 r.commits[r.i].seq) fun u hu =>
          (slotP_eval hb hu hic (p := "rsl") rfl (by decide) (by decide)).trans
              (congrArg some (hu.rest.slots r.i hi hic).seq)) ?_
      refine frag_append (xs := [_]) (mid_set o hb (x := rWait) (by decide) (E := .const (.ofNat 64 1)) rfl
        (val := .ofNat 64 1) fun _ _ => rfl) ?_
      refine frag_conseq (stop_frag o hb asksFile (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
      exact mid_end hu (offs_all (by and_intros <;> rfl))
        (fun hr => rest_phase hr (by omega) (fun h9 => absurd h9 (by dsimp only; omega)) rfl rfl rfl rfl rfl)
        ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩
    · have hi : r.i = r.commits.length := by have := of_decide_eq_false e; omega
      rw [RecoverSpec.files, List.getElem?_eq_none (by omega)]
      refine frag_conseq (mid_set o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 6)) rfl
        (val := .ofNat 64 6) fun _ _ => rfl) (fun _ h => h) fun u hu => ?_
      exact mid_end hu (offs_all (by and_intros <;> rfl))
        (fun hr => rest_phase hr (by omega) (fun h9 => absurd h9 (by dsimp only; omega)) rfl rfl rfl rfl rfl)
        (vals_lookup hu.vals rfl)

/-- **Phase 6**, the next sequence number, while numbers last. -/
theorem numbered_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : r.phase = 6) (hcap : r.commits.length ≤ capacity)
    (hsq : ∀ c ∈ r.commits, c.seq < 2 ^ 64) (hms : r.maxSeq < 2 ^ 64) :
    Frag o RecoverProg.numbered (Like s0) (POut A cfg J s0 (RecoverSpec.numbered r)) := by
  have hb := h.toPBase
  have hn := nums
  obtain ⟨n, hn'⟩ : ∃ n, n = r.commits.length := ⟨_, rfl⟩
  refine from_start h ?_
  refine frag_append (held_frag o hb rfl hcap) ?_
  refine frag_append (xs := [_]) (mid_assign o hb (y := "rm") (by decide) (rw_lower (by decide))
    (val := .ofNat 64 r.maxSeq) fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) ?_
  refine frag_append (xs := [_]) (mid_assign o hb (y := "ri") (by decide) (E := .op .add (.var "jz") (.const 0))
    rfl (val := .ofNat 64 0) fun u hu => by simp [eval, jz_kept hb hu.kept]) ?_
  let L (j : Nat) : List (String × Value) := [("ri", .ofNat 64 j),
    ("rm", .ofNat 64 (seqMax r.maxSeq r.commits j)), ("rcm", .ofNat 64 r.commits.length), ("rgo", 1)]
  let I (j : Nat) : Assn σ := fun u => Mid A cfg J r s0 (scalars cfg r) [] (L j) u ∧ j ≤ r.commits.length
  have hIc : ∀ j, Safe.ClockFree (I j) := fun _ s k ⟨h1, h2⟩ => ⟨mid_clock s k h1, h2⟩
  refine frag_append (xs := [_]) (M := I r.commits.length) (frag_conseq (frag_count o
    (c := Syntax.eLt (Syntax.v "ri") (Syntax.v "rcm")) (C := .cmp .less (.var "ri") (.var "rcm")) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) hIc (fun j => noDecl (P' := I j) _ rfl)
    (g := fun j => decide (j < r.commits.length)) (fun j u ⟨hu, _⟩ => by
      rw [FramerCode.eval_lt (t := u) (a := .var "ri") (b := .var "rcm") (x := j) (y := r.commits.length)
        (by omega) (by omega) (ev_var (vals_lookup hu.vals rfl)) (ev_var (vals_lookup hu.vals rfl))]
      rfl) (fun j hj => ?_) 0) (fun u hu => ⟨mid_vals hu fun q hq => by
        simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> simp [without, seqMax], Nat.zero_le _⟩) fun u ⟨j, hu, hgj⟩ => by
      have : j = r.commits.length := by have := hu.2; simp only [decide_eq_false_iff_not] at hgj; omega
      subst this; exact hu) ?_
  · have hj' : j < r.commits.length := of_decide_eq_true hj
    have hjc : j < capacity := by omega
    refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r) [] (L j)) (P0' := Mid A cfg J r s0 (scalars cfg r) []
      (("ri", .ofNat 64 (j + 1)) :: without "ri" (("rm", .ofNat 64 (max (seqMax r.maxSeq r.commits j)
          r.commits[j].seq)) ::
        without "rm" (("rsl", at_ A (slotAt j)) :: without "rsl" (L j))))) ?_ (fun _ h => h.1) fun u hu => ⟨?_, hj'⟩
    rotate_left
    · exact mid_vals hu fun q hq => by
        simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> simp [L, without, seqMax_succ _ _ hj']
    refine frag_append (xs := [_]) (mid_slotAt o hb (y := "rsl") (by decide) (x := "ri") (i := j) rfl) ?_
    refine frag_append (xs := [_]) (mid_raise o hb (seqMax_lt hms hsq j) (hsq _ (List.getElem_mem hj')) rfl
      (slotW_lower slotSeq) fun u hu => (slotP_eval hb hu hjc (p := "rsl") rfl (by decide) (by decide)).trans
        (congrArg some ((hu.rest.slots j hj' hjc).seq))) ?_
    exact mid_assign o hb (y := "ri") (by decide) (E := .op .add (.var "ri") (.const (.ofNat 64 1))) rfl
      (val := .ofNat 64 (j + 1)) fun u hu => by simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add]
  obtain ⟨M, hM⟩ : ∃ M, M = (r.commits.map (·.seq)).foldl max r.maxSeq := ⟨_, rfl⟩
  have hML : seqMax r.maxSeq r.commits r.commits.length = M := by
    rw [hM, seqMax, List.take_of_length_le (Nat.le_refl _)]
  have hM64 : M < 2 ^ 64 := hML ▸ seqMax_lt hms hsq _
  have hspec : RecoverSpec.numbered r = if M = 2 ^ 64 - 1 ∨ (r.torn ∧ M = 2 ^ 64 - 2) then
      (r, some (.refused .exhausted)) else
      ({ r with next0 := M + 1, next := M + 1 + (if r.torn then 1 else 0), i := 0, phase := 7 }, none) := by
    rw [RecoverSpec.numbered, ← hM]
  rw [hspec]
  have hrm : ∀ (ws : Nat → Word) (os : List (Nat × Word)) (u : PancakeState σ),
      Mid A cfg J r s0 ws os (L r.commits.length) u → u.locals "rm" = some (.ofNat 64 M) :=
    fun _ _ u hu => by rw [← hML]; exact vals_lookup hu.vals rfl
  refine frag_conseq (P0 := Mid A cfg J r s0 (scalars cfg r) [] (L r.commits.length)) ?_ (fun _ h => h.1) fun _ h => h
  refine frag_if o (C := FramerCode.or2E (.cmp .equal (.var "rm") (.const (.ofNat 64 (2 ^ 64 - 1))))
      (.op .and_ (rwE rTorn) (.cmp .equal (.var "rm") (.const (.ofNat 64 (2 ^ 64 - 2)))))) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
    (b := decide (M = 2 ^ 64 - 1) || (r.torn && decide (M = 2 ^ 64 - 2)))
    (fun u hu => FramerCode.eval_or2 (FramerCode.eval_eq hM64 (by decide) (hrm _ _ u hu) rfl)
      (FramerCode.eval_and (mid_rw hb hu (by decide) (rw_lower (by decide)))
        (FramerCode.eval_eq hM64 (by decide) (hrm _ _ u hu) rfl))) (fun e => ?_) fun e => ?_
  · rw [if_pos (by simpa using e)]
    refine frag_conseq (refused_frag o hb .exhausted (by rfl)) (fun _ h => h) fun u hu => ?_
    exact mid_end hu (fun _ _ => rfl) (fun hr => hr) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
      outs_lookup hu.outs rfl, trivial⟩
  · rw [if_neg (by simpa using e)]
    refine frag_append (xs := [_]) (mid_set o hb (x := rNext0) (by decide)
      (E := .op .add (.var "rm") (.const (.ofNat 64 1))) rfl (val := .ofNat 64 (M + 1)) fun u hu => by
        simp only [eval, hrm _ _ u hu, BitVec.ofNat_add]) ?_
    refine frag_append (xs := [_]) (mid_set o hb (x := rNext) (by decide)
      (E := .op .add (.op .add (.var "rm") (.const (.ofNat 64 1))) (rwE rTorn)) rfl
      (val := .ofNat 64 (M + 1 + if r.torn then 1 else 0)) fun u hu => by
        simp only [eval, hrm _ _ u hu, mid_rw hb hu (x := rTorn) (by decide) (rw_lower (by decide))]
        rw [show upd (scalars cfg r) rNext0 (.ofNat 64 (M + 1)) rTorn = bw r.torn from rfl, bw_nat,
          BitVec.ofNat_add, BitVec.ofNat_add]) ?_
    refine frag_append (xs := [_, _]) (mid_consts o hb [(rI, 0), (rPhase, 7)] _ (by decide)) ?_
    exact frag_nil o fun u hu => mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr (by omega)
      (fun h => by simp at h) rfl rfl rfl rfl rfl) (vals_lookup hu.vals rfl)

/-- **The torn tail's octets**, in the scanner's window. That holds where the window holds the journal to its end from
at or before the cut. -/
theorem tail_octets {A : Word} {J : Bytes} {st : St} {cut : Nat} {u : PancakeState σ}
    (ha : AreaAt (at_ A rScan) J st u) (hv : Valid J st) (hb : st.base ≤ cut) (hc : cut ≤ J.length)
    (he : J.length ≤ st.base + st.len) :
    rScan + ScanProg.sWindow + (cut - st.base) + (J.drop cut).length ≤ RecoverProg.size ∧
      BytesAt A (rScan + ScanProg.sWindow + (cut - st.base)) (J.drop cut) u := by
  have hn := nums
  have hs := snums
  have hl := hv.len
  have hst := hv.stop
  refine ⟨by simp only [List.length_drop, ScanProg.windowMax, Journal.maxFrame, ScanProg.chunk] at *; omega,
    fun i hi => ?_⟩
  simp only [List.length_drop] at hi
  rw [show rScan + ScanProg.sWindow + (cut - st.base) + i = rScan + (ScanProg.sWindow + (cut - st.base + i)) by omega,
    ← at_at, ha.window (cut - st.base + i) (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some, List.getElem_drop]
  congr 2; omega

/-- The counter's word one more: the words of `r` with it. -/
theorem words_i (cfg : Config) (r : RSt) :
    ∀ x ∈ scalarOffs, upd (scalars cfg r) rI (.ofNat 64 (r.i + 1)) x = scalars cfg { r with i := r.i + 1 } x :=
  offs_all (by and_intros <;> rfl)

/-- `Rest` of a later phase, another counter given. -/
theorem rest_i {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {u : PancakeState σ} (hp : 5 ≤ r.phase) (k : Nat)
    (h : Rest A cfg J r u) : Rest A cfg J { r with i := k } u :=
  rest_phase h hp (fun h => ⟨rfl, h⟩) rfl rfl rfl rfl rfl

/-- **Phase 7**, a torn tail kept under the next number, the directory synced, the journal cut; then the second
pass. -/
theorem tail_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : r.phase = 7) (hi : r.i < 2 ^ 64) (hfr : r.fresh = false)
    (htn : r.torn = true → r.scan.base ≤ r.cut ∧ r.cut ≤ J.length ∧ J.length ≤ r.scan.base + r.scan.len) :
    Frag o RecoverProg.tail (Like s0) (POut A cfg J s0 (RecoverSpec.tail r)) := by
  have hb := h.toPBase
  refine from_start h ?_
  refine frag_append (xs := [_]) (mid_assign o hb (y := "ri") (by decide) (rw_lower (by decide))
    (val := .ofNat 64 r.i) fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) ?_
  refine frag_if o (C := FramerCode.or2E (.cmp .equal (rwE rTorn) (.const (.ofNat 64 0)))
      (.cmp .equal (.var "ri") (.const (.ofNat 64 3)))) rfl (lowK_any _ (k := .skip) (c := _) rfl)
    (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := !r.torn || decide (r.i = 3))
    (fun u hu => FramerCode.eval_or2 ?_ (FramerCode.eval_eq hi (by decide) (vals_lookup hu.vals rfl) rfl)) (fun e => ?_)
    fun e => ?_
  · have e1 := mid_rw hb hu (x := rTorn) (by decide) (rw_lower (by decide))
    cases ht : r.torn <;> simp only [scalars, scalarList, ht] at e1 <;> simp [eval, e1] <;> rfl
  · refine frag_append (xs := [_, _]) (mid_consts o hb [(rFirst, 1), (rPhase, 8)] _ (by decide)) ?_
    refine frag_conseq (stop_frag o hb asksName apart_nil) (fun _ h => h) fun u hu => ?_
    rw [RecoverSpec.tail, if_pos (by simpa using e)]
    exact mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr (by omega) (fun h => by simp at h)
      rfl rfl rfl rfl rfl) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl⟩
  have ht : r.torn = true := by cases h' : r.torn <;> simp_all
  have e3 : r.i ≠ 3 := by simpa [ht] using e
  have hs1 : RecoverSpec.tail r = if r.i = 0 then ({ r with i := r.i + 1 }, some (.gives (.keep r.next0 r.cut)))
      else if r.i = 1 then ({ r with i := r.i + 1 }, some (.gives .syncDir))
      else ({ r with i := r.i + 1 }, some (.gives (.cut r.cut))) := by
    rw [RecoverSpec.tail, if_neg (by simp [ht, e3])]
  obtain ⟨hbc, hcj, hje⟩ := htn ht
  have hJ := h.short
  rw [hs1]
  refine frag_append (xs := [_]) (mid_set o hb (x := rI) (by decide) (E := .op .add (.var "ri") (.const (.ofNat 64 1)))
    rfl (val := .ofNat 64 (r.i + 1)) fun u hu => by
      simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add]) ?_
  refine frag_if o (C := .cmp .equal (.var "ri") (.const (.ofNat 64 0))) rfl (lowK_any _ (k := .skip) (c := _) rfl)
    (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := decide (r.i = 0))
    (fun u hu => FramerCode.eval_eq hi (by decide) (vals_lookup hu.vals rfl) rfl) (fun e => ?_) fun e => ?_
  · rw [if_pos (of_decide_eq_true e)]
    have hsc : ∀ (ws : Nat → Word) (os : List (Nat × Word)) (l : List (String × Value)) (u : PancakeState σ),
        Mid A cfg J r s0 ws os l u → AreaAt (at_ A rScan) J r.scan u ∧ Valid J r.scan :=
      fun _ _ _ u hu => hu.rest.scan (by omega) hfr
    refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) apart_nil
      (E := .const (.ofNat 64 actKeep)) rfl fun _ _ => rfl) ?_
    refine frag_append (xs := [_]) (mid_out o hb (x := rActA) (by decide) (apart_of (by rfl))
      (E := rwE rNext0) (rw_lower (by decide)) fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) ?_
    refine frag_append (xs := [_]) (mid_out o hb (x := rActB) (by decide) (apart_of (by rfl))
      (E := rwE rCut) (rw_lower (by decide)) fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) ?_
    refine frag_append (xs := [_]) (mid_out o hb (x := rActAt) (by decide) (apart_of (by rfl))
      (E := .op .add (.const (.ofNat 64 (rScan + ScanProg.sWindow))) (.op .sub (rwE rCut) (swE ScanProg.sBase))) rfl
      (val := .ofNat 64 (rScan + ScanProg.sWindow + (r.cut - r.scan.base))) fun u hu => by
        have e1 := (hsc _ _ _ u hu).1.base
        rw [at_at] at e1
        simp only [eval, mid_rw hb hu (x := rCut) (by decide) (rw_lower (by decide)),
          mid_sw hb hu (x := ScanProg.sBase) (by decide) (by decide), e1]
        rw [show upd (scalars cfg r) rI (.ofNat 64 (r.i + 1)) rCut = .ofNat 64 r.cut from rfl,
            SipHashCode.ofNat_sub_ofNat hbc (by omega),
          ← BitVec.ofNat_add]) ?_
    refine frag_append (xs := [_]) (mid_out o hb (x := rActLen) (by decide) (apart_of (by rfl))
      (E := .op .sub (swE ScanProg.sSize) (rwE rCut)) rfl
      (val := .ofNat 64 (J.length - r.cut)) fun u hu => by
        have e1 := (hsc _ _ _ u hu).1.size
        rw [at_at] at e1
        simp only [eval, mid_rw hb hu (x := rCut) (by decide) (rw_lower (by decide)),
          mid_sw hb hu (x := ScanProg.sSize) (by decide) (by decide), e1]
        rw [show upd (scalars cfg r) rI (.ofNat 64 (r.i + 1)) rCut = .ofNat 64 r.cut from rfl,
            SipHashCode.ofNat_sub_ofNat hcj (by omega)]) ?_
    refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
    obtain ⟨ha, hv⟩ := hsc _ _ _ u hu
    obtain ⟨hx, hby⟩ := tail_octets ha hv hbc hcj hje
    exact mid_end hu (words_i cfg r) (rest_i (by omega) _) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
        outs_lookup hu.outs rfl,
      outs_lookup hu.outs rfl, outs_lookup hu.outs rfl,
      ⟨_, outs_lookup hu.outs rfl, by rw [outs_lookup hu.outs rfl, List.length_drop], hx, hby⟩⟩
  have e0 : r.i ≠ 0 := of_decide_eq_false e
  rw [if_neg e0]
  refine frag_if o (C := .cmp .equal (.var "ri") (.const (.ofNat 64 1))) rfl (lowK_any _ (k := .skip) (c := _) rfl)
    (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := decide (r.i = 1))
    (fun u hu => FramerCode.eval_eq hi (by decide) (vals_lookup hu.vals rfl) rfl) (fun e => ?_) fun e => ?_
  · rw [if_pos (of_decide_eq_true e)]
    refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) apart_nil
      (E := .const (.ofNat 64 actSyncDir)) rfl fun _ _ => rfl) ?_
    refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
    exact mid_end hu (words_i cfg r) (rest_i (by omega) _) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
        outs_lookup hu.outs rfl⟩
  · rw [if_neg (of_decide_eq_false e)]
    refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) apart_nil
      (E := .const (.ofNat 64 actCut)) rfl fun _ _ => rfl) ?_
    refine frag_append (xs := [_]) (mid_out o hb (x := rActA) (by decide) (apart_of (by rfl))
      (E := rwE rCut) (rw_lower (by decide)) fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) ?_
    refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
    exact mid_end hu (words_i cfg r) (rest_i (by omega) _) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
        outs_lookup hu.outs rfl,
      outs_lookup hu.outs rfl⟩

/-- Whether one of the first `j` commits has the number `s`. -/
def seqSeen (cs : List Commit) (s j : Nat) : Bool := (cs.take j).any (·.seq == s)

theorem seqSeen_succ {cs : List Commit} {s j : Nat} (hj : j < cs.length) :
    seqSeen cs s (j + 1) = (seqSeen cs s j || cs[j].seq == s) := by
  simp only [seqSeen, List.take_succ_eq_append_getElem hj, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem seqSeen_all (cs : List Commit) (s : Nat) : seqSeen cs s cs.length = (cs.map (·.seq)).contains s := by
  simp only [seqSeen, List.take_length]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, beq_iff_eq, List.contains_iff_mem, List.mem_map]

theorem seqSeen_mono {cs : List Commit} {s j : Nat} (h : seqSeen cs s j = true) : seqSeen cs s cs.length = true := by
  simp only [seqSeen, List.take_length, List.any_eq_true] at h ⊢
  obtain ⟨c, hc, e⟩ := h
  exact ⟨c, List.mem_of_mem_take hc, e⟩

/-- **Whether a commit has the number in `rv`**, into `rok`. -/
theorem recorded_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PBase A s0) (hsq : ∀ c ∈ r.commits, c.seq < 2 ^ 64) (hcap : r.commits.length ≤ capacity) {s : Nat}
    (hs : s < 2 ^ 64) {ws : Nat → Word} (hws : ws rCommits = .ofNat 64 r.commits.length) {os : List (Nat × Word)} :
    Frag o recorded (Mid A cfg J r s0 ws os [("rv", .ofNat 64 s), ("rgo", 1)])
      (Mid A cfg J r s0 ws os [("rok", bw ((r.commits.map (·.seq)).contains s)), ("rv", .ofNat 64 s), ("rgo", 1)]) := by
  have hn := nums
  let n := r.commits.length
  let L (j : Nat) : List (String × Value) := [("ri", .ofNat 64 j), ("rok", bw (seqSeen r.commits s j)),
    ("rcm", .ofNat 64 n), ("rv", .ofNat 64 s), ("rgo", 1)]
  let I (j : Nat) : Assn σ := fun u => Mid A cfg J r s0 ws os (L j) u ∧ j ≤ n
  have hIc : ∀ j, Safe.ClockFree (I j) := fun _ s c ⟨h1, h2⟩ => ⟨mid_clock s c h1, h2⟩
  refine frag_append (xs := held "rcm") (held_frag o h hws hcap) ?_
  refine frag_append (xs := [_, _]) (frag_append (xs := [_]) (mid_assign o h (y := "rok") (by decide)
    (E := .op .add (.var "jz") (.const 0)) rfl (val := bw false) fun u hu => by simp [eval, jz_kept h hu.kept, bw])
    (mid_assign o h (y := "ri") (by decide) (E := .op .add (.var "jz") (.const 0)) rfl (val := .ofNat 64 0)
      fun u hu => by simp [eval, jz_kept h hu.kept])) ?_
  refine frag_conseq (frag_count o (c := Syntax.eAnd (Syntax.eEq (Syntax.v "rok") (Syntax.n 0))
      (Syntax.eLt (Syntax.v "ri") (Syntax.v "rcm")))
    (C := .op .and_ (.cmp .equal (.var "rok") (.const 0)) (.cmp .less (.var "ri") (.var "rcm"))) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) hIc (fun j => noDecl (P' := I j) _ rfl)
    (g := fun j => !seqSeen r.commits s j && decide (j < n)) (fun j u ⟨hu, _⟩ => flag_guard (e := 1) (by decide)
      (by decide) (by omega) (by omega) (by rw [vals_lookup hu.vals rfl, bw_nat]) (vals_lookup hu.vals rfl)
      (vals_lookup hu.vals rfl)) (fun j hj => ?_) 0) (fun u hu => ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩,
        Nat.zero_le _⟩) ?_
  · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hj
    obtain ⟨-, hj'⟩ := hj
    have hjc : j < capacity := by omega
    have hsj := hsq _ (List.getElem_mem hj')
    let L2 : List (String × Value) := [("rsl", at_ A (slotAt j)), ("ri", .ofNat 64 j),
      ("rok", bw (seqSeen r.commits s (j + 1))), ("rcm", .ofNat 64 n), ("rv", .ofNat 64 s), ("rgo", 1)]
    refine frag_conseq (P0 := Mid A cfg J r s0 ws os (L j))
      (P0' := Mid A cfg J r s0 ws os (("ri", .ofNat 64 (j + 1)) :: without "ri" L2)) ?_ (fun _ h => h.1)
      fun u hu => ⟨mid_lookups hu ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩, by omega⟩
    refine frag_append (xs := [_]) (mid_slotAt o h (y := "rsl") (by decide) (x := "ri") (i := j) rfl) ?_
    refine frag_append (xs := [_]) (M := Mid A cfg J r s0 ws os L2) ?_ ?_
    · refine frag_if o (C := .cmp .equal (slotWE slotSeq) (.var "rv")) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (fun k => ⟨k, rfl⟩) rfl rfl mid_clock
        (b := decide (r.commits[j].seq = s))
        (fun u hu => FramerCode.eval_eq hsj hs ((slotP_eval h hu hjc (p := "rsl") rfl (by decide) (by decide)).trans
          (congrArg some ((hu.rest.slots j hj' hjc).seq))) (ev_var (vals_lookup hu.vals rfl))) (fun e => ?_) fun e => ?_
      · have ht : seqSeen r.commits s (j + 1) = true := by
          rw [seqSeen_succ hj']; simp [of_decide_eq_true e]
        refine frag_conseq (mid_assign o h (y := "rok") (by decide) (E := .op .add (.var "jz") (.const 1)) rfl
          (val := bw true) fun u hu => by simp [eval, jz_kept h hu.kept, bw]) (fun _ h => h) fun u hu => ?_
        exact mid_lookups hu ⟨rfl, rfl, by rw [ht]; rfl, rfl, rfl, rfl, trivial⟩
      · have ht : seqSeen r.commits s (j + 1) = seqSeen r.commits s j := by
          rw [seqSeen_succ hj']
          have : r.commits[j].seq ≠ s := of_decide_eq_false e
          simp [this]
        exact frag_nil o fun u hu => mid_lookups hu ⟨rfl, rfl, by rw [ht]; rfl, rfl, rfl, rfl, trivial⟩
    · exact mid_assign o h (y := "ri") (E := .op .add (.var "ri") (.const (.ofNat 64 1))) (by decide) rfl
        (val := .ofNat 64 (j + 1)) fun u hu =>
            by simp only [eval, vals_lookup hu.vals (x := "ri") rfl, BitVec.ofNat_add]
  intro u ⟨j, ⟨hu, hjn⟩, hgj⟩
  have hall : seqSeen r.commits s j = seqSeen r.commits s n := by
    cases hsn : seqSeen r.commits s j
    · have : j = n := by simp only [hsn, Bool.not_false, Bool.true_and, decide_eq_false_iff_not] at hgj; omega
      rw [← this, hsn]
    · rw [seqSeen_mono hsn]
  exact mid_lookups hu ⟨by rw [← seqSeen_all, ← hall]; rfl, rfl, rfl, trivial⟩

/-- **Phase 8**, a name of the second pass: a temporary file removed. A final file no commit names is set aside, or
removed if already set aside or not to be. A name set aside is counted; or the names end. -/
theorem secondPass_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : r.phase = 8) (hok : ∀ c ∈ r.commits, c.ok = true)
    (hcap : r.commits.length ≤ capacity) (hmt : r.maxTail < 2 ^ 64) :
    Frag o RecoverProg.secondPass (Like s0) (POut A cfg J s0 (RecoverSpec.secondPass r)) := by
  have hb := h.toPBase
  refine from_start h ?_
  refine frag_if o (rw_lower (x := rEnd) (by decide)) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := r.ended)
    (fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) (fun he => ?_) fun he => ?_
  · -- no name left
    rw [RecoverSpec.secondPass, if_pos he]
    refine frag_conseq (mid_consts o hb [(rI, 0), (rPhase, 11)] _ (by decide)) (fun _ h => h) fun u hu => ?_
    exact mid_end hu (offs_all (by and_intros <;> rfl))
      (fun hr => rest_phase hr (by omega) (fun h9 => absurd h9 (by dsimp only; omega)) rfl rfl rfl rfl rfl)
      (vals_lookup hu.vals rfl)
  rw [RecoverSpec.secondPass, if_neg (by simpa using he)]
  refine frag_append (xs := RecoverProg.classify) (classify_frag o hb h.area.rest.nameLen (by decide) rfl) ?_
  let K (u : PancakeState σ) : Prop := u.locals "rk" = some (.ofNat 64 (kindOf (parseName r.name))) ∧
    ∀ n, parseName r.name = some n → n ≠ .journal → u.locals "rv" = some (.ofNat 64 (numOf n))
  refine frag_append (xs := [_]) (mid_set_and o hb (x := rFirst) (by decide) (E := .const (.ofNat 64 0)) rfl
    (val := .ofNat 64 0) (F := K) (fun _ _ _ => rfl) (fun _ _ h => h) fun _ _ h => h) ?_
  let ws1 := upd (scalars cfg r) rFirst (.ofNat 64 0)
  -- a name asked for next, the area's number stored of no value
  -- a name with a number: the number stored
  have hseqst : ∀ n, parseName r.name = some n → n ≠ .journal →
      Frag o [rset rSeq (Syntax.v "rv")] (fun u => Mid A cfg J r s0 ws1 [] [("rgo", 1)] u ∧ K u)
        (Mid A cfg J r s0 ws1 [(rSeq, .ofNat 64 (numOf n))] [("rk", .ofNat 64 (kindOf (some n))),
          ("rv", .ofNat 64 (numOf n)), ("rgo", 1)]) := fun n hpn hnj =>
    frag_conseq (mid_seq o hb (by omega) apart_nil (E := .var "rv") rfl (val := .ofNat 64 (numOf n))
      fun u hu => vals_lookup hu.vals rfl) (fun u ⟨hu, hk1, hk2⟩ => mid_add (mid_add hu (hk2 n hpn hnj))
        (by rw [← hpn]; exact hk1)) fun _ h => h
  have hkeval : ∀ (n : Name) (os : List (Nat × Word)) (l : List (String × Value)) (u : PancakeState σ),
      Mid A cfg J r s0 ws1 os l u → l.lookup "rk" = some (.ofNat 64 (kindOf (some n))) → ∀ c, c < 2 ^ 64 →
      eval u (.cmp .equal (.var "rk") (.const (.ofNat 64 c))) = some (bw (decide (kindOf (some n) = c))) :=
    fun n _ _ u hu hl c hc => FramerCode.eval_eq (by cases n <;> simp [kindOf]) hc (ev_var (vals_lookup hu.vals hl)) rfl
  by_cases hk1 : kindOf (parseName r.name) ≤ 1
  · -- no number: the next name asked for, the area's number stored of no value
    have hsp : RecoverSpec.secondName { r with first := false } (parseName r.name) =
        ({ r with first := false }, some .askName) := by
      cases hpn : parseName r.name with
      | none => rfl
      | some n => rw [hpn] at hk1; cases n <;> first | rfl | (simp [kindOf] at hk1)
    rw [hsp]
    have hkd : kindOf (parseName r.name) < 2 ^ 63 := by omega
    refine frag_append (xs := [_]) (frag_conseq (mid_seq_any o hb (by omega) apart_nil (E := .var "rv") rfl
      (l := [("rk", .ofNat 64 (kindOf (parseName r.name))), ("rgo", 1)])
      fun u hu => kept_has hu.kept (hb.bound "rv" (by decide))) (fun u ⟨hu, hk⟩ => mid_add hu hk.1)
      fun _ h => h) ?_
    refine frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 3))) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
      (b := decide (kindOf (parseName r.name) = 3)) (fun u hu => FramerCode.eval_eq (by omega) (by decide)
        (ev_var (vals_lookup hu.vals rfl)) rfl) (fun e => absurd (of_decide_eq_true e) (by omega)) fun _ => ?_
    refine frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 2))) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
      (b := decide (kindOf (parseName r.name) = 2)) (fun u hu => FramerCode.eval_eq (by omega) (by decide)
        (ev_var (vals_lookup hu.vals rfl)) rfl) (fun e => absurd (of_decide_eq_true e) (by omega)) fun _ => ?_
    refine frag_if o (C := .cmp .less (.const (.ofNat 64 3)) (.var "rk")) rfl
      (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
      (b := decide (3 < kindOf (parseName r.name))) (fun u hu => FramerCode.eval_lt (by decide) (by omega) rfl
        (ev_var (vals_lookup hu.vals rfl))) (fun e => absurd (of_decide_eq_true e) (by omega)) fun _ => ?_
    refine frag_conseq (stop_frag o hb asksName apart_nil) (fun _ h => h) fun u hu => ?_
    exact mid_end hu (offs_all (by and_intros <;> rfl))
      (fun hr => rest_phase hr (by omega) (fun h9 => absurd h9 (by dsimp only; omega)) rfl rfl rfl rfl rfl)
        ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl⟩
  cases hpn : parseName r.name with
  | none => exact absurd (by rw [hpn]; decide) hk1
  | some n =>
    cases n with
    | journal => exact absurd (by rw [hpn]; decide) hk1
    | temp s =>
      -- a temporary file removed
      refine frag_append (xs := [_]) (hseqst _ hpn (fun e => nomatch e)) ?_
      refine frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 3))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := true)
        (fun u hu => hkeval (.temp s) _ _ u hu rfl 3 (by decide)) (fun _ => ?_) fun e => absurd e (by decide)
      refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) (apart_of (by rfl))
        (E := .const (.ofNat 64 actRemove)) rfl fun _ _ => rfl) ?_
      refine frag_append (xs := [_]) (mid_out o hb (x := rActA) (by decide)
        (apart_of (by rfl)) (E := .var "rv") rfl (val := .ofNat 64 s)
        fun u hu => vals_lookup hu.vals rfl) ?_
      refine frag_append (xs := [_]) (mid_out o hb (x := rActB) (by decide) (apart_of (by rfl))
        (E := .const (.ofNat 64 nameTemp)) rfl fun _ _ => rfl) ?_
      refine frag_append (xs := [_]) (mid_inc o hb (x := rTidied) (by decide) rfl (k := r.tidied) rfl) ?_
      refine frag_append (xs := [_]) (mid_set o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 13)) rfl
        (val := .ofNat 64 13) fun _ _ => rfl) ?_
      refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
      exact mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr (by omega) (fun h9 => absurd h9
          (by dsimp only; omega)) rfl rfl rfl rfl rfl)
        ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl,
          outs_lookup hu.outs rfl⟩
    | final s =>
      have hs : s < 2 ^ 64 := num_lt hpn
      have hsq : ∀ c ∈ r.commits, c.seq < 2 ^ 64 := fun c hc => (ok_bounds (hok c hc)).1
      refine frag_append (xs := [_]) (hseqst _ hpn (fun e => nomatch e)) ?_
      refine frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 3))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := false)
        (fun u hu => hkeval (.final s) _ _ u hu rfl 3 (by decide)) (fun e => absurd e (by decide)) fun _ => ?_
      refine frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 2))) rfl
        (lowKK_append (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl))
        (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := true)
        (fun u hu => hkeval (.final s) _ _ u hu rfl 2 (by decide)) (fun _ => ?_) fun e => absurd e (by decide)
      refine frag_append (xs := recorded) (frag_conseq (recorded_frag o hb hsq hcap hs rfl)
        (fun u hu => mid_lookups hu ⟨rfl, rfl, trivial⟩) fun _ h => h) ?_
      simp only [RecoverSpec.secondName]
      refine frag_if o (C := .var "rok") rfl (lowK_any _ (k := .skip) (c := _) rfl)
        (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := (r.commits.map (·.seq)).contains s)
        (fun u hu => vals_lookup hu.vals rfl) (fun e => ?_) fun e => ?_
      · -- a commit names it: the next name
        rw [if_pos e]
        refine frag_conseq (stop_frag o hb asksName (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
        exact mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr (by omega) (fun h9 => absurd h9
            (by dsimp only; omega)) rfl rfl rfl rfl rfl)
          ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl⟩
      rw [if_neg (by rw [e]; exact Bool.false_ne_true)]
      refine frag_if o (C := .cmp .less (.const 0) (.op .add (rwE rTorn) (.op .and_ (rwE rTails)
          (.cmp .less (.op .xor (.var "rv") (.const (.ofNat 64 top))) (.op .xor (rwE rMaxTail)
            (.const (.ofNat 64 top))))))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
        (b := r.torn || (r.tails && decide (s < r.maxTail)))
        (fun u hu => ScanRun.e_or2 (mid_rw hb hu (by decide) (rw_lower (by decide)))
          (FramerCode.eval_and (mid_rw hb hu (by decide) (rw_lower (by decide)))
            (ult_eval hs hmt (ev_var (vals_lookup hu.vals rfl)) (mid_rw hb hu (by decide) (rw_lower (by decide))))))
        (fun e2 => ?_) fun e2 => ?_
      · -- set aside
        rw [if_pos e2]
        refine frag_append (xs := [_]) (mid_set o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 9)) rfl
          (val := .ofNat 64 9) fun _ _ => rfl) ?_
        refine frag_conseq (stop_frag o hb asksAside (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
        exact mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => ⟨fun _ => outs_lookup hu.outs rfl, hr.nameLen,
          hr.name, hr.unknown, hr.config, (fun _ hf => hr.scan (by omega) hf), hr.slots, fun _ => hr.high (by omega)⟩)
          ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩
      · -- removed
        rw [if_neg (by simpa using e2)]
        refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) (apart_of (by rfl))
          (E := .const (.ofNat 64 actRemove)) rfl fun _ _ => rfl) ?_
        refine frag_append (xs := [_]) (mid_out o hb (x := rActA) (by decide)
          (apart_of (by rfl)) (E := .var "rv") rfl (val := .ofNat 64 s)
          fun u hu => vals_lookup hu.vals rfl) ?_
        refine frag_append (xs := [_]) (mid_out o hb (x := rActB) (by decide) (apart_of (by rfl))
          (E := .const (.ofNat 64 nameFinal)) rfl fun _ _ => rfl) ?_
        refine frag_append (xs := [_]) (mid_inc o hb (x := rTidied) (by decide) rfl (k := r.tidied) rfl) ?_
        refine frag_append (xs := [_]) (mid_set o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 13)) rfl
          (val := .ofNat 64 13) fun _ _ => rfl) ?_
        refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
        exact mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr (by omega) (fun h9 => absurd h9
            (by dsimp only; omega)) rfl rfl rfl rfl rfl)
          ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl,
            outs_lookup hu.outs rfl⟩
    | quarantine s | tail s =>
      -- a name set aside counted
      refine frag_append (xs := [_]) (hseqst _ hpn (fun e => nomatch e)) ?_
      refine frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 3))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := false)
        (fun u hu => hkeval _ _ _ u hu rfl 3 (by decide)) (fun e => absurd e (by decide)) fun _ => ?_
      refine frag_if o (C := .cmp .equal (.var "rk") (.const (.ofNat 64 2))) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := false)
        (fun u hu => hkeval _ _ _ u hu rfl 2 (by decide)) (fun e => absurd e (by decide)) fun _ => ?_
      have hk63 : kindOf (parseName r.name) < 2 ^ 63 := by rw [hpn]; simp [kindOf]
      rw [hpn] at hk63
      refine frag_if o (C := .cmp .less (.const (.ofNat 64 3)) (.var "rk")) rfl
        (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := true)
        (fun u hu => FramerCode.eval_lt (x := 3) (by decide) hk63 rfl
          (ev_var (vals_lookup hu.vals rfl))) (fun _ => ?_) fun e => absurd e (by decide)
      refine frag_append (xs := [_]) (mid_out o hb (x := rActA) (by decide) (apart_of (by rfl))
        (E := .var "rv") rfl (val := .ofNat 64 s) fun u hu => vals_lookup hu.vals rfl) ?_
      refine frag_append (xs := [_]) (mid_set o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 13)) rfl
        (val := .ofNat 64 13) fun _ _ => rfl) ?_
      refine frag_conseq (stop_frag o hb givesAside (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
      exact mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr (by omega) (fun h9 => absurd h9
          (by dsimp only; omega)) rfl rfl rfl rfl rfl)
        ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩

/-- **Phase 9**, whether the name a final file is set aside under holds one already. -/
theorem asideGiven_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : r.phase = 9) :
    Frag o RecoverProg.asideGiven (Like s0) (POut A cfg J s0 (RecoverSpec.asideGiven r)) := by
  have hb := h.toPBase
  refine from_start h ?_
  refine frag_append (xs := [_]) (mid_inc o hb (x := rTidied) (by decide) rfl (k := r.tidied) rfl) ?_
  refine frag_append (xs := [_]) (mid_out o hb (x := rActA) (by decide) apart_nil
    (E := rwE rSeq) rfl (val := .ofNat 64 r.seq) fun u hu =>
      (rw_eval hb.hA (by rw [hu.kept.memaddrs]; exact hb.dom) (rsc_kept hb hu.kept) (x := rSeq) (by decide)
        (by decide) rfl).trans (congrArg some (hu.rest.seq (.inl hp)))) ?_
  refine frag_if o (rw_lower (x := rFound) (by decide)) (lowK_any _ (k := .skip) (c := _) rfl)
    (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := r.found)
    (fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) (fun hf => ?_) fun hf => ?_
  · refine frag_append (xs := [_]) (mid_out o hb (x := rActB) (by decide) (apart_of (by rfl)) (E :=
      .const (.ofNat 64 nameFinal)) rfl fun _ _ => rfl) ?_
    refine frag_append (xs := [_]) (mid_set o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 13)) rfl
      fun _ _ => rfl) ?_
    refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) (apart_of (by rfl))
        (E := .const (.ofNat 64 actRemove)) rfl fun _ _ => rfl) ?_
    refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
    rw [RecoverSpec.asideGiven, if_pos hf]
    refine mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr (by omega)
      (fun h => by simp at h) rfl rfl rfl rfl rfl) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
        outs_lookup hu.outs rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩
  · refine frag_append (xs := [_]) (mid_set o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 12)) rfl
      fun _ _ => rfl) ?_
    refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) (apart_of (by rfl)) (E :=
        .const (.ofNat 64 actRename)) rfl fun _ _ => rfl) ?_
    refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
    rw [RecoverSpec.asideGiven, if_neg (by rw [hf]; decide)]
    refine mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr (by omega)
      (fun _ => ⟨rfl, .inl hp⟩) rfl rfl rfl rfl rfl) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
        outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩

/-- **Phase 10**, a new journal created, and the directory synced if it held no file. -/
theorem created_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : r.phase = 10) (hi : r.i < 2 ^ 64) :
    Frag o RecoverProg.created (Like s0) (POut A cfg J s0 (RecoverSpec.created r)) := by
  have hb := h.toPBase
  refine from_start h ?_
  refine frag_append (xs := [_, _]) (ri_frag o hb (k := r.i) rfl) ?_
  refine frag_if o (C := .cmp .equal (.var "ri") (.const (.ofNat 64 0))) rfl (lowK_any _ (k := .skip) (c := _) rfl)
    (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := decide (r.i = 0))
    (fun u hu => FramerCode.eval_eq hi (by decide) (vals_lookup hu.vals rfl) rfl) (fun e => ?_) fun e => ?_
  · have e : r.i = 0 := of_decide_eq_true e
    refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) apart_nil
      (E := .const (.ofNat 64 actCreate)) rfl fun _ _ => rfl) ?_
    refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
    rw [RecoverSpec.created, if_pos e]
    exact mid_end hu (words_i cfg r) (rest_i (by omega) _) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
        outs_lookup hu.outs rfl⟩
  have e0 : r.i ≠ 0 := of_decide_eq_false e
  refine frag_if o (C := .op .and_ (.cmp .equal (.var "ri") (.const (.ofNat 64 1))) (rwE rWait)) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
    (b := decide (r.i = 1) && r.wait)
    (fun u hu => FramerCode.eval_and (FramerCode.eval_eq hi (by decide) (vals_lookup hu.vals rfl) rfl)
      (mid_rw hb hu (by decide) (rw_lower (by decide)))) (fun e => ?_) fun e => ?_
  · refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) apart_nil
      (E := .const (.ofNat 64 actSyncDir)) rfl fun _ _ => rfl) ?_
    refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
    rw [RecoverSpec.created, if_neg e0, if_pos e]
    exact mid_end hu (words_i cfg r) (rest_i (by omega) _) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
        outs_lookup hu.outs rfl⟩
  · refine frag_conseq (stop_frag o hb done apart_nil) (fun _ h => h) fun u hu => ?_
    rw [RecoverSpec.created, if_neg e0, if_neg (by rw [e]; decide)]
    exact mid_end hu (words_i cfg r) (rest_i (by omega) _) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl⟩

/-- **Phase 11**, the directory synced after names are tidied, the torn tail's number set aside, done. -/
theorem finish_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : r.phase = 11) (hi : r.i < 2 ^ 63) (ht : r.tidied < 2 ^ 63) :
    Frag o RecoverProg.finish (Like s0) (POut A cfg J s0 (RecoverSpec.finish r)) := by
  have hb := h.toPBase
  refine from_start h ?_
  refine frag_append (xs := [_, _]) (ri_frag o hb (k := r.i) rfl) ?_
  refine frag_if o (C := .op .and_ (.cmp .equal (.var "ri") (.const (.ofNat 64 0)))
      (.cmp .less (.const (.ofNat 64 0)) (rwE rTidied))) rfl (lowK_any _ (k := .skip) (c := _) rfl)
    (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock (b := decide (r.i = 0) && decide (0 < r.tidied))
    (fun u hu => FramerCode.eval_and (FramerCode.eval_eq (by omega) (by decide) (vals_lookup hu.vals rfl) rfl)
      (FramerCode.eval_lt (by decide) ht rfl (mid_rw hb hu (by decide) (rw_lower (by decide)))))
    (fun e => ?_) fun e => ?_
  · refine frag_append (xs := [_]) (mid_out o hb (x := rAct) (by decide) apart_nil
      (E := .const (.ofNat 64 actSyncDir)) rfl fun _ _ => rfl) ?_
    refine frag_conseq (stop_frag o hb gives (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
    rw [RecoverSpec.finish, if_pos (by simpa using e)]
    exact mid_end hu (words_i cfg r) (rest_i (by omega) _) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl,
        outs_lookup hu.outs rfl⟩
  have e0 : ¬(r.i = 0 ∧ 0 < r.tidied) := by simpa using e
  refine frag_if o (C := .op .and_ (FramerCode.leE (.var "ri") (.const (.ofNat 64 1))) (rwE rTorn)) rfl
    (lowK_any _ (k := .skip) (c := _) rfl) (lowK_any _ (k := .skip) (c := _) rfl) rfl rfl pout_clock
    (b := decide (r.i ≤ 1) && r.torn)
    (fun u hu => FramerCode.eval_and (FramerCode.eval_le hi (by decide) (vals_lookup hu.vals rfl) rfl)
      (mid_rw hb hu (by decide) (rw_lower (by decide)))) (fun e => ?_) fun e => ?_
  · refine frag_append (xs := [_]) (mid_set o hb (x := rI) (by decide) (E := .const (.ofNat 64 2)) rfl
      fun _ _ => rfl) ?_
    refine frag_append (xs := [_]) (mid_out o hb (x := rActA) (by decide) apart_nil (E := rwE rNext0)
      (rw_lower (by decide)) fun u hu => mid_rw hb hu (by decide) (rw_lower (by decide))) ?_
    refine frag_conseq (stop_frag o hb givesAside (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
    rw [RecoverSpec.finish, if_neg e0, if_pos (by simpa using e)]
    exact mid_end hu (offs_all (by and_intros <;> rfl)) (rest_i (by omega) _)
      ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩
  · refine frag_conseq (stop_frag o hb done apart_nil) (fun _ h => h) fun u hu => ?_
    rw [RecoverSpec.finish, if_neg e0, if_neg (by simpa using e)]
    exact mid_end hu (words_i cfg r) (rest_i (by omega) _) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl⟩

/-- **Phase 12**, the number of a final file just set aside. -/
theorem renamed_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : r.phase = 12) :
    Frag o RecoverProg.renamed (Like s0) (POut A cfg J s0 (RecoverSpec.renamed r)) := by
  have hb := h.toPBase
  refine from_start h ?_
  refine frag_append (xs := [_]) (mid_out o hb (x := rActA) (by decide) apart_nil
    (E := rwE rSeq) rfl (val := .ofNat 64 r.seq) fun u hu =>
      (rw_eval hb.hA (by rw [hu.kept.memaddrs]; exact hb.dom) (rsc_kept hb hu.kept) (x := rSeq) (by decide)
        (by decide) rfl).trans (congrArg some (hu.rest.seq (.inr hp)))) ?_
  refine frag_append (xs := [_]) (mid_set o hb (x := rPhase) (by decide) (E := .const (.ofNat 64 13)) rfl
    fun _ _ => rfl) ?_
  refine frag_conseq (stop_frag o hb givesAside (apart_of (by rfl))) (fun _ h => h) fun u hu => ?_
  refine mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr (by omega)
    (fun h => by simp at h) rfl rfl rfl rfl rfl)
    ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl, outs_lookup hu.outs rfl⟩

/-- **Phase 13**, the next name of the second pass asked for. -/
theorem askNext_frag (o : Oracle σ) {A : Word} {cfg : Config} {J : Bytes} {r : RSt} {s0 : PancakeState σ}
    (h : PIn A cfg J r s0) (hp : 5 ≤ r.phase) :
    Frag o RecoverProg.askNext (Like s0) (POut A cfg J s0 (RecoverSpec.askNext r)) := by
  have hb := h.toPBase
  refine from_start h ?_
  refine frag_append (xs := [_, _]) (mid_consts o hb [(rFirst, 0), (rPhase, 8)] _ (by decide)) ?_
  refine frag_conseq (stop_frag o hb asksName apart_nil) (fun _ h => h) fun u hu => ?_
  refine mid_end hu (offs_all (by and_intros <;> rfl)) (fun hr => rest_phase hr hp
    (fun h => by simp at h) rfl rfl rfl rfl rfl) ⟨vals_lookup hu.vals rfl, outs_lookup hu.outs rfl⟩

end DN.News.RecoverArea
