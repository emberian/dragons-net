-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.AnalyzerCert
import DN.Compiler.AnalyzerSound

/-!
# DN.Compiler.AnalyzerCertSound

**A program a certificate of `DN.Compiler.AnalyzerCert` accepts, its claims holding, never fails**
(`analyzeC_safe`, `never_failsC`, and with functions `programC_never_fails`): the rules `analyzeC`
checks of the parts it does not analyze are those `analyze_safe` proves sound, with the invariant of
a loop given rather than searched for, and the first statements of a chain analyzed together
(`prefix_safe`); a function's certificate shows its body safe as `CodeOk` asks.
-/

namespace DN.Compiler.Analyzer

open DN.Compiler DN.Compiler.Safe

variable {σ : Type}

/-! ## Soundness -/

theorem Ob.ok_sound {size : Nat} {ob : Ob} (h : ob.ok size = true) : ob.run size = .ok ob.out := by
  unfold Ob.ok at h
  split at h
  · rename_i out hout
    rw [hout, of_decide_eq_true h]
  · cases h

theorem obsOk_append {size : Nat} {l r : List Ob} (h : ObsOk size (l ++ r)) :
    ObsOk size l ∧ ObsOk size r :=
  ⟨fun ob hm => h ob (List.mem_append_left _ hm), fun ob hm => h ob (List.mem_append_right _ hm)⟩

/-- The first `n` statements of a chain, analyzed, then the rest: as the whole chain. -/
theorem prefix_safe (o : Oracle σ) {size : Nat} {env : Env} {Q : PancakeState σ → Prop} :
    ∀ (n : Nat) (A : AState) (p q : PancakeProg) (out : Option AState),
      prefixOut size env n A p = .ok out → dropChain n p = some q →
      (∀ B, out = some B → Safe o (HoldsE size env B) q Q) → Safe o (HoldsE size env A) p Q := by
  intro n
  induction n with
  | zero =>
    intro A p q out h hq hrest
    simp only [prefixOut] at h
    simp only [dropChain] at hq
    cases h
    cases hq
    exact hrest A rfl
  | succ n ih =>
    intro A p q out h hq hrest
    cases p with
    | seq c1 c2 =>
      simp only [prefixOut, bind, Except.bind] at h
      simp only [dropChain] at hq
      split at h
      · cases h
      · rename_i r hr
        cases r with
        | none =>
          simp only at h
          cases h
          exact Safe.seq (analyze_safe o size env c1 A none hr) (postE_none o c2 size env _)
            (postE_clockFree size env none)
        | some B =>
          simp only at h
          apply Safe.seq (analyze_safe o size env c1 A (some B) hr) _
            (postE_clockFree size env (some B))
          intro s ⟨B', hB', hsB⟩
          cases hB'
          exact ih B c2 q out h hq hrest s hsB
    | _ => simp [prefixOut] at h

/-- A branch run by a certificate from a state in which its condition has the value that leads to
it comes to what the whole statement may end in. -/
theorem branchC_safe {o : Oracle σ} {size : Nat} {env : Env} {A : AState} {e : PancakeExp}
    {t : Bool} {c : PancakeProg} {k : Cert} {ob out : Option AState} {obs : List Ob}
    {s : PancakeState σ} {w : Word}
    (ih : ∀ (p : PancakeProg) (A : AState) (out : Option AState) (obs : List Ob),
      analyzeC size env A p k = .ok (out, obs) → ObsOk size obs →
        Safe o (HoldsE size env A) p (PostE size env out))
    (hb : branchC size e t (fun X => analyzeC size env X c k) A = .ok (ob, obs))
    (hobs : ObsOk size obs) (hs : HoldsE size env A s) (ew : eval s e = some w)
    (hw : decide (w ≠ 0) = t) (up : ∀ (t : PancakeState σ), PostE size env ob t → PostE size env out t) :
    Ok (PostE size env out) (PancakeSem o c s) := by
  obtain ⟨G, hG, hsG⟩ := assume_sound A e t hs.1 w ew hw
  simp only [branchC, hG] at hb
  have k := ih c G ob obs hb hobs s ⟨hsG, hs.2⟩
  revert k
  cases PancakeSem o c s with
  | mk r t =>
    cases r with
    | none => exact up t
    | some _ => exact id

/-- **A statement a certificate accepts, its claims holding, never errs**: from every state the
abstract one stands for, with code holding the functions it may call, a run ends as a run may end,
or finishes normally in a state the result stands for. -/
theorem analyzeC_safe (o : Oracle σ) (size : Nat) (env : Env) :
    ∀ (k : Cert) (p : PancakeProg) (A : AState) (out : Option AState) (obs : List Ob),
      analyzeC size env A p k = .ok (out, obs) → ObsOk size obs →
        Safe o (HoldsE size env A) p (PostE size env out) := by
  intro k
  induction k with
  | leaf d =>
    intro p A out obs h hobs
    cases d with
    | none =>
      simp only [analyzeC] at h
      cases h
      exact analyze_safe o size env p A none (hobs _ (List.mem_singleton_self _))
    | some d =>
      simp only [analyzeC] at h
      split at h
      · cases h
        exact analyze_safe o size env p A _ (hobs _ (List.mem_singleton_self _))
      · cases h
  | chain n d k ih =>
    intro p A out obs h hobs
    simp only [analyzeC, chainC] at h
    split at h
    · cases h
    · rename_i hn
      split at h
      · cases h
      · rename_i q hq
        cases h
        have hp := hobs _ (List.mem_singleton_self _)
        simp only [Ob.run, hn, ↓reduceIte] at hp
        exact prefix_safe o n A p q none hp hq (fun B hB => by cases hB)
      · rename_i q d hq
        split at h
        · cases h
        · rename_i B hB
          split at h
          · cases h
          · rename_i hr
            cases h
            have hp := hobs _ (List.mem_cons_self ..)
            simp only [Ob.run, hn, ↓reduceIte] at hp
            refine prefix_safe o n A p q (some B) hp hq ?_
            intro B' hB'
            cases hB'
            exact ih q B _ _ hr fun ob hm => hobs ob (List.mem_cons_of_mem _ hm)
  | dec k ih =>
    intro p A out obs h hobs
    cases p with
    | dec x e c =>
      simp only [analyzeC, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i v hv
        split at h
        · cases h
        · rename_i res hr
          obtain ⟨r, obs'⟩ := res
          have hobs' : ObsOk size obs' := by
            cases r with
            | none =>
              simp only at h
              cases h
              exact hobs
            | some B =>
              simp only at h
              split at h
              · cases h
              · cases h
                exact hobs
          refine dec_safe hv (ih c _ r obs' hr hobs') fun B hB => ?_
          subst hB
          simp only at h
          split at h
          · cases h
          · rename_i u hn
            cases h
            exact ⟨need_ok hn, rfl⟩
    | decCall rt f args c =>
      simp only [analyzeC, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i u hargs
        split at h
        · cases h
        · rename_i ps rest hfind
          split at h
          · cases h
          · rename_i u2 hlen
            split at h
            · cases h
            · rename_i res hr
              obtain ⟨r, obs'⟩ := res
              have hobs' : ObsOk size obs' := by
                cases r with
                | none =>
                  simp only at h
                  cases h
                  exact hobs
                | some B =>
                  simp only at h
                  split at h
                  · cases h
                  · cases h
                    exact hobs
              have hl := need_ok hlen
              simp only [beq_iff_eq] at hl
              refine call_safe hargs hfind hl (ih c _ r obs' hr hobs') fun B hB => ?_
              subst hB
              simp only at h
              split at h
              · cases h
              · rename_i u3 hn
                cases h
                exact ⟨need_ok hn, rfl⟩
    | _ => simp [analyzeC] at h
  | seq k1 k2 ih1 ih2 =>
    intro p A out obs h hobs
    cases p with
    | seq c1 c2 =>
      simp only [analyzeC, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i r hr
        obtain ⟨r, obs1⟩ := r
        cases r with
        | none =>
          simp only at h
          cases h
          exact Safe.seq (ih1 c1 A none obs hr hobs) (postE_none o c2 size env _)
            (postE_clockFree size env none)
        | some B =>
          simp only at h
          split at h
          · cases h
          · rename_i r2 hr2
            obtain ⟨out2, obs2⟩ := r2
            cases h
            obtain ⟨h1, h2⟩ := obsOk_append hobs
            apply Safe.seq (ih1 c1 A (some B) obs1 hr h1) _ (postE_clockFree size env (some B))
            intro s ⟨B', hB', hsB⟩
            cases hB'
            exact ih2 c2 B out2 obs2 hr2 h2 s hsB
    | _ => simp [analyzeC] at h
  | cond k1 k2 ih1 ih2 =>
    intro p A out obs h hobs
    cases p with
    | cond e c1 c2 =>
      simp only [analyzeC, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i v hv
        split at h
        · cases h
        · rename_i r1 hr1
          obtain ⟨o1, obs1⟩ := r1
          simp only at h
          split at h
          · cases h
          · rename_i r2 hr2
            obtain ⟨o2, obs2⟩ := r2
            simp only at h
            split at h
            · cases h
            · rename_i out' hj
              cases h
              obtain ⟨h1, h2⟩ := obsOk_append hobs
              obtain ⟨up1, up2⟩ := joinOuts_upE (σ := σ) hj size env
              apply Safe.cond
              · intro s hs
                obtain ⟨w, ew, _⟩ := eval_of hs.1 hv
                exact ⟨w, ew⟩
              · intro s ⟨hs, hne⟩
                obtain ⟨w, ew, _⟩ := eval_of hs.1 hv
                have hw : decide (w ≠ 0) = true := by
                  simp only [ne_eq, decide_eq_true_eq]
                  intro z
                  exact hne (by rw [ew, z])
                exact branchC_safe ih1 hr1 h1 hs ew hw up1
              · intro s ⟨hs, hz⟩
                exact branchC_safe ih2 hr2 h2 hs hz (by decide) up2
    | _ => simp [analyzeC] at h
  | loop d k ih =>
    intro p A out obs h hobs
    cases p with
    | while_ e c =>
      simp only [analyzeC, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i I hI
        split at h
        · cases h
        · rename_i u hle
          split at h
          · cases h
          · rename_i v hv
            split at h
            · cases h
            · rename_i r hr
              obtain ⟨post, obs'⟩ := r
              simp only at h
              split at h
              · cases h
              · rename_i u' hlp
                cases h
                have hlp := need_ok hlp
                have body : Safe o (fun s => HoldsE size env I s ∧ eval s e ≠ some 0) c
                    (HoldsE size env I) := by
                  intro s ⟨hs, hne⟩
                  obtain ⟨w, ew, _⟩ := eval_of hs.1 hv
                  have hw : decide (w ≠ 0) = true := by
                    simp only [ne_eq, decide_eq_true_eq]
                    intro z
                    exact hne (by rw [ew, z])
                  obtain ⟨G, hG, hsG⟩ := assume_sound I e true hs.1 w ew hw
                  simp only [branchC, hG] at hr
                  have k := ih c G post obs hr hobs s ⟨hsG, hs.2⟩
                  revert k
                  cases PancakeSem o c s with
                  | mk r t =>
                    cases r with
                    | none =>
                      intro ⟨B, hB, hsB⟩
                      subst hB
                      simp only [leOpt] at hlp
                      exact ⟨le_holds hlp hsB.1, hsB.2⟩
                    | some _ => exact id
                have loopI := Safe.while_
                  (fun s hs => (eval_of hs.1 hv).elim fun w hw => ⟨w, hw.1⟩)
                  body (fun _ _ h => h)
                refine Safe.conseq loopI (fun s hs => ⟨le_holds (need_ok hle) hs.1, hs.2⟩) ?_
                intro s ⟨hs, hz⟩
                have hw : decide ((0 : Word) ≠ 0) = false := by decide
                obtain ⟨A', hA', hsA'⟩ := assume_sound I e false hs.1 0 hz hw
                exact ⟨A', hA', hsA', hs.2⟩
    | _ => simp [analyzeC] at h

/-- A whole `main` a certificate accepts, its claims holding: as `check_safe`. -/
theorem checkC_safe (o : Oracle σ) {size : Nat} {p : PancakeProg} {k : Cert} {obs : List Ob}
    (h : checkC size p k = .ok obs) (hobs : ObsOk size obs) :
    Safe o (fun s => Covers size s.memaddrs s.baseAddr) p (fun _ => False) := by
  unfold checkC at h
  split at h
  · rename_i obs' hr
    cases h
    refine Safe.conseq (analyzeC_safe o size [] k p _ none obs hr hobs)
      (fun s hc => ⟨⟨hc, ?_, ?_⟩, trivial⟩) ?_
    · intro x v hv
      cases hv
    · exact holds_empty_cells s
    · intro s ⟨B, hB, _⟩
      cases hB
  · cases h
  · cases h

/-- The claims of an accepted certificate, each holding: whatever is listed is as `checkC` lists. -/
theorem claims_of {size : Nat} {p : PancakeProg} {k : Cert}
    (h : (checkC size p k).toBool = true) : checkC size p k = .ok (claims size p k) := by
  unfold claims
  cases hc : checkC size p k with
  | ok obs => rfl
  | error m => rw [hc] at h; cases h

/-- The premise holds of a claim the analysis gives. -/
theorem obsOk_witness : ObsOk (floor + 8) [⟨⟨[], []⟩, .ret (.const 0), 0, none, []⟩] := by
  intro ob hm
  simp only [List.mem_singleton] at hm
  subst hm
  rfl

/-- Claims numbered below `n`, each holding by `Ob.ok`, hold all, when there are `n`. -/
theorem obsOk_of_get {size : Nat} {l : List Ob}
    (h : ∀ i, i < l.length → (l.getD i default).ok size = true) : ObsOk size l := by
  intro ob hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  have := h i hi
  simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
  exact Ob.ok_sound this

/-- **No run of a `main` a certificate accepts fails, its claims holding**, as `never_fails`. -/
theorem never_failsC (o : Oracle σ) {size : Nat} {p : PancakeProg} {k : Cert}
    (h : (checkC size p k).toBool = true)
    (hobs : ∀ i, i < (claims size p k).length → ((claims size p k).getD i default).ok size = true)
    (s : PancakeState σ) (hc : Covers size s.memaddrs s.baseAddr) : ¬ Entry.Fails o p s :=
  Safe.not_fails (checkC_safe o (claims_of h) (obsOk_of_get hobs)) (fun _ => hc)

/-! ## Functions -/

/-- The functions of `fns`, defined after those `env` names and each accepted by its certificate,
its claims holding, in code that holds them: the code holds them all, as `CodeOk` asks. -/
theorem fnsOk_codeOk {size : Nat} {code : String → Option (List String × PancakeProg)} :
    ∀ {env : Env} {fns : List FnC}, fnsOk size env fns = true →
      (∀ i, i < fns.length → ObsOk size (fnClaims size env fns i)) →
      CodeOk (σ := σ) size code env →
      (∀ f ps body k, (f, ps, body, k) ∈ fns → code f = some (ps, body)) →
      CodeOk (σ := σ) size code (envAfter env fns)
  | _, [], _, _, hc, _ => hc
  | env, (f, ps, body, k) :: fns, h, hobs, hc, hcode => by
    simp only [fnsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨_, hnd⟩, hb⟩, hrest⟩ := h
    have h0 := hobs 0 (by simp)
    have safe : ∀ o : Oracle σ, Safe o (fun s => Holds size (entryState ps) s ∧
        CodeOk (σ := σ) size s.code env) body (fun _ => False) := by
      intro o
      simp only [fnClaims] at h0
      unfold bodyC at hb h0
      split at hb
      · rename_i obs hr
        rw [hr] at h0
        exact Safe.conseq (analyzeC_safe o size env k body _ none obs hr h0) (fun _ h => h)
          fun _ ⟨_, hB, _⟩ => by cases hB
      · cases hb
      · cases hb
    exact fnsOk_codeOk (env := (f, ps) :: env) (fns := fns) hrest (fun i hi => hobs (i + 1) (by simp only [List.length_cons]; omega))
      ⟨⟨body, hcode f ps body k (by simp), hnd, safe⟩, hc⟩
      fun g qs b k' hm => hcode g qs b k' (List.mem_cons_of_mem _ hm)

/-- **No run of a program its certificates accept fails, their claims holding**: its `main`, from
any heap that covers the bytes from `floor` to `size` after `@base` and code that holds its
functions, whatever the external world answers and whatever the clock. The claims of `main` need
only the functions' names and parameters. -/
theorem programC_never_fails (o : Oracle σ) {size : Nat} {fns : List FnC} {p : PancakeProg}
    {k : Cert} {obs : List Ob} (hf : fnsOk size [] fns = true)
    (hfns : ∀ i, i < fns.length → ObsOk size (fnClaims size [] fns i))
    (h : checkC size p k (envAfter [] fns) = .ok obs) (hobs : ObsOk size obs)
    (s : PancakeState σ) (hc : Covers size s.memaddrs s.baseAddr)
    (hcode : ∀ f ps body k, (f, ps, body, k) ∈ fns → s.code f = some (ps, body)) :
    ¬ Entry.Fails o p s := by
  unfold checkC at h
  split at h
  · rename_i obs' hr
    cases h
    have hco := fnsOk_codeOk (σ := σ) hf hfns trivial hcode
    refine Safe.not_fails (P := HoldsE size (envAfter [] fns) ⟨[], []⟩)
      (Safe.conseq (analyzeC_safe o size _ k p _ none obs hr hobs) (fun _ h => h)
        fun _ ⟨_, hB, _⟩ => by cases hB) fun _ => ?_
    exact ⟨⟨hc, fun _ _ hv => by simp [lookup] at hv, holds_empty_cells _⟩, hco⟩
  · cases h
  · cases h

/-! ## The premises can hold -/

/-- A function that returns its argument, as `returnsCode` holds it, and a `main` that calls it. -/
def oneFn : List FnC := [("f", ["k"], .ret (.var "k"), .leaf none)]
def callsF : PancakeProg := .decCall "r" "f" [.const 1] (.ret (.var "r"))

/-- The premises of `programC_never_fails` can hold: of this program, from `holdsE_witness`'s heap
and code. -/
theorem programC_witness :
    fnsOk 128 [] oneFn = true ∧ (∀ i, i < oneFn.length → ObsOk 128 (fnClaims 128 [] oneFn i)) ∧
      checkC 128 callsF (.dec (.leaf none)) (envAfter [] oneFn) =
        .ok (claims 128 callsF (.dec (.leaf none)) (envAfter [] oneFn)) ∧
      ObsOk 128 (claims 128 callsF (.dec (.leaf none)) (envAfter [] oneFn)) ∧
      ∀ f ps body k, (f, ps, body, k) ∈ oneFn → returnsCode f = some (ps, body) := by
  refine ⟨by decide, fun i hi => ?_, rfl, obsOk_of_get (by decide), fun f ps body k hm => ?_⟩
  · have : i = 0 := by simp [oneFn] at hi; omega
    subst this
    exact obsOk_of_get (by decide)
  · simp only [oneFn, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
    rfl

end DN.Compiler.Analyzer
