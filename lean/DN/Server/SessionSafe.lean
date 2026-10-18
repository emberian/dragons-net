-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionCert
import DN.Compiler.AnalyzerCertSound

/-!
# DN.Server.SessionSafe

**The session's program never fails, whatever its host does.** For every FFI oracle, every clock
and every content of the heap, a run of the session's `main` from a state whose heap covers its
layout above the header and whose code holds the program's functions ends only as a run may end —
out of clock, a call the host ended, or a return — and never in `Fail` (`Entry.Fails`). The safety
analysis of `DN.Compiler.Analyzer` accepts the program in the pieces of `DN.Server.SessionCert`, and
`DN.Compiler.AnalyzerCertSound` proves that a program its certificates accept, their claims
holding, never fails; `printed_never_fails` ties this to the text the gate prints. That the Pancake
parser reads the text as its lowering is checked of this program by `scripts/parser_contract.py`,
not proved.
-/

namespace DN.Server.SessionSafe

open DN.Compiler DN.Compiler.Analyzer DN.Server DN.Server.SessionCert

variable {σ : Type}

/-- **The session's program never fails, whatever its host does.** -/
theorem never_fails (o : Oracle σ) (s : PancakeState σ)
    (h : Covers SessionLayout.size s.memaddrs s.baseAddr)
    (hcode : ∀ f ps body k, (f, ps, body, k) ∈ fnsC → s.code f = some (ps, body)) :
    ¬ Entry.Fails o mainP s :=
  programC_never_fails o fns_ok fns_claims (claims_of accepted) (obsOk_of_get claims_ok) s h
    hcode

/-- The same of the text the gate prints: it is the program's own, its `main` has the shape the
semantics runs, and the lowerings are the functions and the `main` `never_fails` is about. -/
theorem printed_never_fails (o : Oracle σ) (s : PancakeState σ)
    (h : Covers SessionLayout.size s.memaddrs s.baseAddr)
    (hcode : ∀ f ps body k, (f, ps, body, k) ∈ fnsC → s.code f = some (ps, body))
    {src : String} (hsrc : Session.source = .ok src) :
    src = String.intercalate "\n" ((Session.functions ++ [Session.main]).map Syntax.ppFun) ∧
      Session.main.exported = false ∧ Session.main.name = "main" ∧ Session.main.params = [] ∧
      (∀ g ∈ Session.functions, (Lower.lower g).isSome = true) ∧
      fnsC.map (fun g => (g.1, g.2.1, g.2.2.1)) = Session.functions.map lowerFn ∧
      Lower.lower Session.main = some mainP ∧ ¬ Entry.Fails o mainP s := by
  obtain ⟨he, hn, hpar⟩ := Checked.emitProgram_entry hsrc
  exact ⟨Checked.emitProgram_prints hsrc, he, hn, hpar, Checked.emitProgram_lowers hsrc,
    fnsC_lowers, lower_main, never_fails o s h hcode⟩

/-- The premises hold of a heap of just the layout, above the first page, and of the code of the
program's functions. -/
theorem premises_witness :
    Covers SessionLayout.size (heapWords 4096 SessionLayout.size) 4096 ∧
      ∀ f ps body k, (f, ps, body, k) ∈ fnsC → codeOf fnsC f = some (ps, body) :=
  ⟨covers_heap _ (Nat.le_refl _) (by decide +kernel) (by decide +kernel), codeOf_holds fns_ok⟩

end DN.Server.SessionSafe
