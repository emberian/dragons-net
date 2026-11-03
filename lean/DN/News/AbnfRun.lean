-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfGen

/-!
# DN.News.AbnfRun

The rules' functions, proven to do what their contract says (`BodyOk`): a rule's, from its slot `s` into its slot
`d`, leaves there the ends of the rule's matches from the positions of slot `s` (`rule_body`, by `AbnfGen.gen_ok`);
the comment's likewise (`comment_body`); every function in `order`, each calling only those before it
(`bodies_ok`).
-/

namespace DN.News.AbnfRun

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg DN.News.AbnfLayout
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.AbnfGen
open DN.News.ScanRun (at_ at_add at_ne at_inj Vals vals_lookup vals_cons vals_set Fresh without lookup_head
  lookup_without fresh_cons)
open DN.News.FramerCode (bw ev_var)
open DN.News.AbnfMatch (Matches)
open DN.News.AbnfComment (commentAdd ruleComment_ok commentSet_iff)

variable {σ : Type}

/-! ## A rule's function -/

theorem not_gen_short {x : String} (h : x.toList.length ≤ 1) (k : Nat) : ¬GenName x k := fun hg => by
  obtain ⟨p, c, rest, e, _⟩ := genName_digit hg
  rw [e] at h; simp at h

theorem not_gen_nn (k : Nat) : ¬GenName "nn" k := fun hg => by
  obtain ⟨p, c, rest, e, hc⟩ := genName_digit hg
  have : "nn".toList = ['n', 'n'] := rfl
  rw [this] at e
  cases e
  exact absurd hc (by decide)

/-- A rule's own locals have no generated names. -/
theorem avoid_own {l : List (String × Value)}
    (h : ∀ q ∈ l, q.1 = "s" ∨ q.1 = "d" ∨ q.1 = "e" ∨ q.1 = "a" ∨ q.1 = "nn") (lo hi : Nat) :
    Avoid l lo hi :=
  fun q hq j _ _ hg => by
    rcases h q hq with e | e | e | e | e <;> rw [e] at hg
    · exact not_gen_short (by decide) j hg
    · exact not_gen_short (by decide) j hg
    · exact not_gen_short (by decide) j hg
    · exact not_gen_short (by decide) j hg
    · exact not_gen_nn j hg

theorem term_at {i : Nat} (hi : i < AbnfRules.grammar.size) : AbnfRules.grammar[i]? = some (termOf i) := by
  unfold termOf; rw [Array.getElem?_eq_getElem hi]; rfl

theorem leaves_in {i : Nat} (hi : i < AbnfRules.grammar.size) (hic : i ≠ commentRule) :
    ∀ lf ∈ leavesOf steps (termOf i), lf ∈ allLeaves := fun lf hlf => by
  unfold allLeaves
  refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩
  by_cases hf : hasFun i = true
  · rw [if_pos hf, if_neg (by simpa using hic)]; exact hlf
  · rw [if_neg hf]
    have hl : (leafOf (termOf i)).isSome = true := by
      unfold hasFun at hf; simp only [Bool.or_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, not_or] at hf
      exact Option.isSome_iff_ne_none.2 hf.2
    obtain ⟨l, hl'⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨s', hs⟩ := steps_succ
    rw [hs, leavesOf, hl'] at hlf
    rw [hl']
    simpa [leavesAt] using hlf

theorem ruleFun_name (m : Mutant) (ofs i : Nat) : (ruleFun m ofs i).name = funName i := by
  unfold ruleFun
  split
  · next h => unfold funName; rw [if_pos h]; rfl
  · rfl

theorem ruleFun_params (m : Mutant) (ofs i : Nat) : (ruleFun m ofs i).params.map (·.2) = ["s", "d"] := by
  unfold ruleFun
  split <;> rfl

theorem mem_ruleFun {ofs i : Nat} (hi : i ∈ order) : ruleFun .none ofs i ∈ functions .none ofs :=
  List.mem_append_right _ (List.mem_map.2 ⟨i, hi, rfl⟩)

/-- **A rule's function** does what its contract says, those it calls doing what theirs say. -/
theorem rule_body (o : Oracle σ) {ofs : Nat} {code : String → Option (List String × PancakeProg)}
    (hcode : ProgCode code ofs) {i : Nat} (hi : i ∈ order) (hic : i ≠ commentRule)
    (hcalls : ∀ j ∈ callees i, BodyOk o ofs code j) : BodyOk o ofs code i := by
  intro s1 A ks kd S bytes hA hc hks hkd hne hs hd hlen hS hB
  have hcode1 : ProgCode s1.code ofs := hc ▸ hcode
  obtain ⟨hsize, -, hen, hfr⟩ := order_all hi
  have hen' : AbnfOrder.enough steps (termOf i) = true := hen.resolve_left hic
  have hneed : need i = needOf steps (termOf i) := by unfold need; rw [if_neg (by simpa using hic)]
  have hfl := frame_le hi
  have hks' : ks < slots := by omega
  have hkd' : kd < slots := by omega
  suffices h : FragR o (RuleRet A bytes i kd S s1.memory) (ruleFun .none ofs i).body (fun s => s = s1) fun _ => False by
    obtain ⟨body, hlow, hsafe⟩ := body_of h
    refine ⟨body, ?_, hsafe⟩
    have := progCode_of hcode1 (mem_ruleFun hi) body hlow
    rw [hc, ruleFun_name, ruleFun_params] at this
    exact this
  -- the term's statements
  have hcj : ∀ j ∈ callsOf steps (termOf i), j ∈ callees i := fun j hj => by
    unfold callees; rw [if_neg (by simpa using hic)]; exact List.mem_eraseDups.2 hj
  have hgen := gen_ok o hA hcode1 hlen steps (termOf i) (Syntax.v "s") (Syntax.v "d") (frameOf i) 0 hen'
    (fun j hj => ⟨hc ▸ hcalls j (hcj j hj), hneed ▸ hfr j (hcj j hj)⟩)
    (leaves_in hsize hic) (hneed ▸ hfl) (.inr ⟨_, rfl⟩) (.inr ⟨_, rfl⟩)
  obtain ⟨⟨hlowG, -, -⟩, hdo⟩ := hgen
  generalize hG : gen .none steps (termOf i) (Syntax.v "s") (Syntax.v "d") (frameOf i) 0 = G at hlowG hdo
  obtain ⟨gs, k'⟩ := G
  unfold ruleFun
  rw [if_neg (by simpa using hic)]
  dsimp only
  rw [hG]
  dsimp only
  refine fragR_conseq (P0 := RunF s1 [("s", BitVec.ofNat 64 ks), ("d", BitVec.ofNat 64 kd)] (· = s1.memory)) ?_
    (entry_two hs hd) fun _ h => h
  let l0 : List (String × Value) := [("s", BitVec.ofNat 64 ks), ("d", BitVec.ofNat 64 kd)]
  obtain ⟨Ea, hEa⟩ := atOff_lower ofs
  have hlowD : LowKK (if repeats steps (termOf i) = true then
      [areaAt ofs, .dec "nn" (word (Syntax.v "a") aLen)] else []) := by
    split
    · exact lowKK_append (xs := [_]) (lowKK_dec hEa) (lowKK_dec rfl)
    · exact lowKK_nil
  have hret : LowKK [.ret (Syntax.n 0)] := lowKK_ret rfl
  have hlowR := lowKK_append hlowD (lowKK_append hlowG hret)
  have hlowRest := lowKK_append (xs := [_]) (lowKK_ite (c := Syntax.v "e") rfl hret lowKK_nil) hlowR
  rw [List.append_assoc, List.append_assoc]
  refine fragR_append (xs := [_]) (fragR_of (void_frag o hA hcode1 (rt := "e") (l := l0) (F := (· = s1.memory))
    rfl rfl rfl hks' hkd' (fun u h => vals_mem h (by simp [l0])) (fun u h => vals_mem h (by simp [l0])) (Ss := S)
    fun m hm => ⟨hm ▸ hS, hm ▸ hB.1⟩)) ?_
  refine fragR_exists hlowRest fun v => ?_
  by_cases hv1 : v = 1
  · -- slot `s` empty: so is slot `d`, the rule matching from nowhere
    subst hv1
    refine fragR_append (M := fun _ => False) (fragR_if o rfl hret lowKK_nil (fun _ _ => id)
      (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim) (b := true) (fun u h => vals_mem h (List.mem_cons_self ..))
      (fun _ => fragR_ret o rfl fun u h => ⟨0, rfl, ?_⟩) (fun h => nomatch h)) (fragR_of (frag_unsat hlowR
        fun _ h => h))
    obtain ⟨m, rfl, hr⟩ := h.2
    rcases hr with ⟨hnone, -, hSd, hfr⟩ | ⟨-, h10, -⟩
    · refine ⟨rfl, ?_, allSets_frame hB.1 hkd' hSd hfr, kept_frame (.inl rfl) hfr⟩
      unfold Holds
      rw [← setOf_eq (T := fun _ => false) fun e => ⟨fun h => absurd h Bool.false_ne_true,
        fun ⟨x, hx, _⟩ => absurd ((hnone x).symm.trans hx) Bool.false_ne_true⟩]
      exact hSd
    · exact absurd h10 (by decide)
  · -- slot `s` not empty: the term's statements
    refine fragR_append (xs := [_]) (M := RunF s1 (("e", v) :: l0) (· = s1.memory)) (fragR_if o rfl hret
      lowKK_nil (runF_clock _ _ _) (noDecl _ rfl) (noDecl _ rfl) (b := false) (fun u h => ?_) (fun h => nomatch h)
      fun _ => fragR_of (frag_nil o fun u h => runF_mono h (fun _ hq => hq) fun m' ⟨m, hm, hr⟩ => ?_)) ?_
    · obtain ⟨m, _, hr⟩ := h.2
      rcases hr with ⟨-, h1, -⟩ | ⟨-, h0, -⟩
      · exact absurd h1 hv1
      · rw [vals_mem h (List.mem_cons_self ..), h0]; rfl
    · rcases hr with ⟨-, h1, -⟩ | ⟨-, -, hmm⟩
      · exact absurd h1 hv1
      · rw [hmm, hm]
    have hfin : ∀ L : List (String × Value),
        (∀ q ∈ L, q.1 = "s" ∨ q.1 = "d" ∨ q.1 = "e" ∨ q.1 = "a" ∨ q.1 = "nn") →
        ("s", BitVec.ofNat 64 ks) ∈ L → ("d", BitVec.ofNat 64 kd) ∈ L →
        (repeats steps (termOf i) = true → ("nn", BitVec.ofNat 64 bytes.length) ∈ L) →
        FragR o (RuleRet A bytes i kd S s1.memory) (gs ++ [.ret (Syntax.n 0)]) (RunF s1 L (· = s1.memory))
          fun _ => False := fun L hL hsL hdL hnn =>
      fragR_append (fragR_of (hdo L (· = s1.memory) ks kd S (.inr ⟨"s", rfl, hsL⟩) (.inr ⟨"d", rfl, hdL⟩)
        hks hkd hne
        (avoid_own hL _ _) hnn fun m hm => ⟨hm ▸ hS, hm ▸ hB⟩)) (fragR_exists hret fun l' =>
          fragR_ret o rfl fun u ⟨_, h⟩ => ⟨0, rfl, by
            obtain ⟨m0, hm0, hH, hBase, hK⟩ := h.2
            exact ⟨rfl, holds_congr hH fun e =>
              ⟨fun ⟨x, hx, hm⟩ => ⟨x, hx, (AbnfMatch.ref_iff' (term_at hsize)).2 hm⟩,
                fun ⟨x, hx, hm⟩ => ⟨x, hx, (AbnfMatch.ref_iff' (term_at hsize)).1 hm⟩⟩,
              hBase.1, hm0 ▸ hK⟩⟩)
    by_cases hr : repeats steps (termOf i) = true
    · rw [if_pos hr]
      let l1 : List (String × Value) := ("nn", BitVec.ofNat 64 bytes.length) :: ("a", A) :: ("e", v) :: l0
      have hl8 : aLen < aSets + slots * setSize := by
        have := pow_lt; rw [aPow_eq] at this; simp only [aLen]; omega
      refine fragR_append (xs := [_, _]) (M := RunF s1 l1 (· = s1.memory)) (fragR_of (frag_append (xs := [_])
        (runF_dec o hEa (x := "a") rfl (v := A) fun u h => areaAt_eval hA h.1.base hEa)
        (runF_dec o rfl (x := "nn") rfl (v := BitVec.ofNat 64 bytes.length) fun u h => ?_))) (hfin l1 ?_ (by simp [l1,
            l0])
          (by simp [l1, l0]) fun _ => List.mem_cons_self ..)
      · have := load_eval hA h.1.memaddrs (y := aLen) hl8 (by decide)
          (E := .op .add (.var "a") (.const (BitVec.ofNat 64 aLen))) (by
            simp only [eval, show u.locals "a" = some A from h.1.vals _ (List.mem_cons_self ..)]; rfl)
        rw [h.2, hB.2.1] at this
        exact this
      · intro q hq
        simp only [l1, l0, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp
    · rw [if_neg hr, List.nil_append]
      refine hfin (("e", v) :: l0) (fun q hq => ?_) (by simp [l0]) (by simp [l0]) fun h => absurd h hr
      simp only [l0, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp

theorem funName_comment : funName commentRule = "ruleComment" := by
  unfold funName; rw [if_pos (beq_self_eq_true _)]

/-- **The comment's function** does what a rule's contract says. -/
theorem comment_body (o : Oracle σ) {ofs : Nat} {code : String → Option (List String × PancakeProg)}
    (hcode : ProgCode code ofs) : BodyOk o ofs code commentRule := by
  intro s1 A ks kd S bytes hA hc hks hkd hne hs hd hlen hS hB
  have hfl := frame_le comment_in
  have hks' : ks < slots := by omega
  have hkd' : kd < slots := by omega
  obtain ⟨Sd, hSd⟩ := hB.1 kd hkd'
  obtain ⟨body, hlow, hsafe⟩ := ruleComment_ok o hA hks' hkd' hne hs hd hS hSd hlen hB.2.1 hB.2.2
  refine ⟨body, ?_, conseq hsafe (fun _ h => h) (fun v m ⟨hv, hT, hfr⟩ =>
    ⟨hv, ?_, allSets_frame hB.1 hkd' hT hfr,
    kept_frame (.inl rfl) hfr⟩) fun _ h => h⟩
  · have := progCode_of (hc ▸ hcode) (mem_ruleComment (ofs := ofs)) body hlow
    rw [hc] at this
    rw [funName_comment]; exact this
  · unfold Holds; rw [← setOf_eq (P := Ends bytes (.ref commentRule) S) fun e => commentSet_iff hlen e]; exact hT

/-- **Every rule's function** does what its contract says: each calls only those before it in `order`. -/
theorem bodies_ok (o : Oracle σ) {ofs : Nat} {code : String → Option (List String × PancakeProg)}
    (hcode : ProgCode code ofs) : ∀ i ∈ order, BodyOk o ofs code i := by
  suffices h : ∀ n, ∀ k < n, (hk : k < order.length) → BodyOk o ofs code order[k] by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
    exact h (k + 1) k (Nat.lt_succ_self _) hk
  intro n
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
  | succ n ih =>
    intro k hk hko
    by_cases hc : order[k] = commentRule
    · rw [hc]; exact comment_body o hcode
    · refine rule_body o hcode (List.getElem_mem hko) hc fun j hj => ?_
      have hjt := order_callees hko j hj
      obtain ⟨k', hk', e⟩ := List.getElem_of_mem hjt
      rw [List.getElem_take] at e
      rw [List.length_take] at hk'
      rw [← e]
      exact ih k' (by omega) (by omega)

end DN.News.AbnfRun
