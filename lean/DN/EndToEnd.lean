-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionSafe
import DN.Compiler.CanonRun

/-!
# DN.EndToEnd

**What `Parse` reads from the session's printed text never fails.** The gate prints the session's
program; `ParseCorrect` proves that `Parse`, the Lean copy of CakeML's parser, reads the text as the
program's functions, each body in the model with its lowering's canonical form; `CanonRun` proves a
program fails exactly where its canonical form does; `SessionSafe` proves the lowering never fails.
So the `main` `Parse` reads, entered from a heap covering the layout and from code holding the
functions read, never fails, whatever the host does (`text_never_fails`). Those two premises can
hold together (`text_premises_witness`); the third, that the gate accepts the session, holds by
evaluating `Session.regression_824`.

Only that the program never fails is proven: that it answers as `SessionSpec` says is tested. The
links from here to the machine code are listed in `docs/assurance.md`, "What is trusted".
-/

namespace DN.EndToEnd

open DN.Compiler DN.Compiler.Analyzer DN.Compiler.ParseCorrect DN.Compiler.CanonRun DN.Server
  DN.Server.SessionCert

variable {σ : Type}

/-- The functions `fnsOk` takes have distinct names, none `main` and none of `env`. -/
theorem fnsOk_names {size : Nat} :
    ∀ {env : Env} {fns : List FnC}, fnsOk size env fns = true →
      (fns.map (·.1)).Nodup ∧ ∀ g ∈ fns, g.1 ≠ "main" ∧ findFn g.1 env = none
  | _, [], _ => ⟨List.nodup_nil, fun _ h => by cases h⟩
  | env, (f, ps, b, k) :: fns, h => by
    simp only [fnsOk, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none, bne_iff_ne,
      ne_eq] at h
    obtain ⟨⟨⟨⟨hf, hm⟩, -⟩, -⟩, hrest⟩ := h
    obtain ⟨hnd, hall⟩ := fnsOk_names hrest
    refine ⟨List.nodup_cons.mpr ⟨fun hin => ?_, hnd⟩, fun g hg => ?_⟩
    · obtain ⟨g, hg, hgf⟩ := List.mem_map.mp hin
      have h2 := (hall g hg).2
      rw [hgf] at h2
      simp [findFn] at h2
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨hm, hf⟩
      · obtain ⟨h1, h2⟩ := hall g hg
        refine ⟨h1, ?_⟩
        simp only [findFn] at h2
        split at h2
        · cases h2
        · exact h2

/-- …and distinct parameters. -/
theorem fnsOk_params {size : Nat} :
    ∀ {env : Env} {fns : List FnC}, fnsOk size env fns = true → ∀ g ∈ fns, g.2.1.Nodup
  | _, [], _ => fun _ h => by cases h
  | env, (f, ps, b, k) :: fns, h => by
    simp only [fnsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact h.1.1.2
    · exact fnsOk_params h.2 g hg

/-- The code that declaring the functions the parser read makes: each name, its function, its body
read in the model. The names are distinct (`sessionTree_names`), so the first function of a name is
also the last, which `evaluate_decls` keeps. -/
def textCode (Fs : List Parse.Func) (f : String) : Option (List String × PancakeProg) :=
  (Fs.find? (·.name == f)).map fun G => (G.params, plainProg G.body)

theorem textCode_holds : ∀ {Fs : List Parse.Func}, (Fs.map (·.name)).Nodup →
    ∀ G ∈ Fs, textCode Fs G.name = some (G.params, plainProg G.body)
  | [], _, _, h => by cases h
  | F :: Fs, hnd, G, hG => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hG with rfl | hG
    · simp [textCode]
    · have hne : F.name ≠ G.name := fun he => hnd.1 (he ▸ List.mem_map_of_mem hG)
      have h := textCode_holds hnd.2 G hG
      simp only [textCode] at h ⊢
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact h

/-- The session's functions and `main`, as the parser reads them from the printed text. -/
def sessionTree : List Parse.Func := (Session.functions ++ [Session.main]).map funTree

/-- Their names are distinct: `fnsOk` takes the functions, none named `main`. -/
theorem sessionTree_names : (sessionTree.map (·.name)).Nodup := by
  obtain ⟨hnd, hall⟩ := fnsOk_names fns_ok
  have hnames : fnsC.map (·.1) = Session.functions.map (·.name) := by
    have h := congrArg (List.map (·.1)) fnsC_lowers
    simpa [List.map_map, Function.comp_def, lowerFn] using h
  rw [hnames] at hnd
  have hmain : Session.main.name = "main" := rfl
  simp only [sessionTree, List.map_map, Function.comp_def, funTree, List.map_append, List.map_cons,
    List.map_nil]
  refine List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb => ?_⟩
  simp only [List.mem_singleton] at hb
  subst hb
  rw [hmain]
  intro he
  subst he
  rw [← hnames] at ha
  obtain ⟨g, hg, hgm⟩ := List.mem_map.mp ha
  exact (hall g hg).1 hgm

/-- Each function read has distinct parameters, `main` none. -/
theorem sessionTree_params : ∀ G ∈ sessionTree, G.params.Nodup := by
  intro G hG
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hG
  rcases List.mem_append.mp hg with hg | hg
  · have hl : lowerFn g ∈ Session.functions.map lowerFn := List.mem_map_of_mem hg
    rw [← fnsC_lowers] at hl
    obtain ⟨c, hc, hce⟩ := List.mem_map.mp hl
    have h := fnsOk_params fns_ok c hc
    simp only [lowerFn, Prod.mk.injEq] at hce
    simpa [funTree, ← hce.2.1] using h
  · simp only [List.mem_singleton] at hg
    subst hg
    show (Session.main.params.map (·.2)).Nodup
    rw [show Session.main.params = [] from rfl]
    exact List.nodup_nil

/-- **What `Parse` reads from the session's printed text never fails**: the text reads as the
session's functions, their names and parameters distinct and every name of their bodies local,
and a `main`
without parameters. That `main`, entered from a heap covering the layout and from code holding the
functions read, never fails, for every external world, clock and heap content. The code's entry
for `main` is how its `Call` finds it; the proof does not need it. -/
theorem text_never_fails (o : Oracle σ) {src : String} (hsrc : Session.source = .ok src) :
    Parse.program src = some sessionTree ∧ (sessionTree.map (·.name)).Nodup ∧
      (∀ G ∈ sessionTree, G.params.Nodup) ∧ (∀ G ∈ sessionTree, LocalP G.body) ∧ ∃ F ∈ sessionTree, F.name = "main" ∧ F.params = [] ∧
      ∀ t : PancakeState σ, Covers SessionLayout.size t.memaddrs t.baseAddr →
        (∀ G ∈ sessionTree, t.code G.name = some (G.params, plainProg G.body)) →
        ¬ Entry.Fails o (plainProg F.body) t := by
  obtain ⟨hprog, hreads⟩ := emitProgram_reads hsrc
  obtain ⟨-, hname, hparams⟩ := Checked.emitProgram_entry hsrc
  refine ⟨hprog, sessionTree_names, sessionTree_params, fun G hG => ?_, funTree Session.main, List.mem_map_of_mem (by simp),
    hname, by simp [funTree, hparams], fun t hcov hcode => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hG
    exact (hreads g hg).locals
  -- The code the lowering runs from: the lowered functions, and elsewhere the code read.
  let c : String → Option (List String × PancakeProg) := fun f => (codeOf fnsC f).or (t.code f)
  have hs : ∀ f ps body k, (f, ps, body, k) ∈ fnsC → c f = some (ps, body) := by
    intro f ps body k hm
    simp [c, codeOf_holds fns_ok f ps body k hm]
  have hnf := SessionSafe.never_fails o { t with code := c } hcov hs
  -- Each function the lowering calls has the canonical form of the one read.
  have hcc : canonCode c = canonCode t.code := by
    funext f
    simp only [canonCode, c]
    cases hf : codeOf fnsC f with
    | none => rfl
    | some pb =>
      obtain ⟨g, hg, hgf, hpb⟩ : ∃ g ∈ fnsC, g.1 = f ∧ (g.2.1, g.2.2.1) = pb := by
        unfold codeOf at hf
        cases hfind : fnsC.find? (·.1 == f) with
        | none => rw [hfind] at hf; cases hf
        | some g =>
          rw [hfind] at hf
          cases hf
          exact ⟨g, List.mem_of_find?_eq_some hfind, by simpa using List.find?_some hfind, rfl⟩
      have hl : (g.1, g.2.1, g.2.2.1) ∈ Session.functions.map lowerFn :=
        fnsC_lowers ▸ List.mem_map_of_mem hg
      obtain ⟨G, hG, hGl⟩ := List.mem_map.mp hl
      simp only [lowerFn, Prod.mk.injEq] at hGl
      obtain ⟨hn, hps, hbody⟩ := hGl
      have hmem : G ∈ Session.functions ++ [Session.main] := List.mem_append_left _ hG
      have hcodeG : t.code G.name = some ((funTree G).params, plainProg (funTree G).body) :=
        hcode (funTree G) (List.mem_map_of_mem hmem)
      obtain ⟨b, hb, hcan⟩ := (hreads G hmem).body
      have hlow : Lower.lower G = some b := hb
      rw [← hgf, ← hn, hcodeG, ← hpb, ← hps, ← hbody, hlow]
      simp only [Option.some_or, Option.map_some, Option.getD_some, hcan]
      rfl
  -- `main` has the canonical form of its lowering.
  obtain ⟨b, hb, hcan⟩ := (hreads Session.main (by simp)).body
  have hbm : b = mainP := Option.some_inj.mp ((show Lower.lower Session.main = some b from hb).symm.trans
    lower_main)
  rw [hbm] at hcan
  exact fun hf => hnf ((fails_same o hcan (canonState_code t hcc).symm).mp hf)

/-- The premises hold together: of a state with a heap of just the layout above the first page and
the code the functions read make. -/
theorem text_premises_witness :
    ∃ t : PancakeState Unit, Covers SessionLayout.size t.memaddrs t.baseAddr ∧
      ∀ G ∈ sessionTree, t.code G.name = some (G.params, plainProg G.body) :=
  ⟨{ locals := fun _ => none, memory := fun _ => 0, memaddrs := heapWords 4096 SessionLayout.size,
     be := false, clock := 0, ffi := (), baseAddr := 4096, code := textCode sessionTree },
   SessionSafe.premises_witness.1, textCode_holds sessionTree_names⟩

end DN.EndToEnd
