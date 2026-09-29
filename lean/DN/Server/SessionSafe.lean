-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.AnalyzerSound
import DN.Server.Session

/-!
# DN.Server.SessionSafe

**The session's program never fails, whatever its host does.** For every FFI oracle, every clock
and every content of the heap, a run of the session's `main` from a state whose heap covers its
layout above the header ends only as a run may end — out of clock, a call the host ended, or a
return — and never in `Fail` (`Entry.Fails`). The safety analysis of `DN.Compiler.Analyzer`
accepts the program, and `DN.Compiler.AnalyzerSound` proves that a program it accepts never fails;
`printed_never_fails` ties this to the text the gate prints. That the Pancake parser reads the text
as its lowering is checked of this program by `scripts/parser_contract.py`, not proved.
-/

namespace DN.Server.SessionSafe

open DN.Compiler DN.Compiler.Analyzer DN.Server

variable {σ : Type}

theorem lowers : (Lower.lower Session.main).isSome = true := by decide +kernel

/-- The session's `main`, as it lowers. -/
def mainP : PancakeProg := (Lower.lower Session.main).get lowers

theorem lower_main : Lower.lower Session.main = some mainP := (Option.some_get lowers).symm

/-- The analysis accepts the program: computed by the kernel. -/
theorem accepted : (check SessionLayout.size mainP).toBool = true := by decide +kernel

theorem checked : check SessionLayout.size mainP = .ok () := ok_of_toBool accepted

/-- **The session's program never fails, whatever its host does.** -/
theorem never_fails (o : Oracle σ) (s : PancakeState σ)
    (h : Covers SessionLayout.size s.memaddrs s.baseAddr) : ¬ Entry.Fails o mainP s :=
  Analyzer.never_fails o checked s h

/-- The same of the text the gate prints: it is the program's own, the entry has the shape the
semantics runs, and the lowering is the program `never_fails` is about. -/
theorem printed_never_fails (o : Oracle σ) (s : PancakeState σ)
    (h : Covers SessionLayout.size s.memaddrs s.baseAddr) {src : String}
    (hsrc : Session.source = .ok src) :
    src = Syntax.ppFun Session.main ∧ Session.main.exported = false ∧
      Session.main.name = "main" ∧ Session.main.params = [] ∧
      Lower.lower Session.main = some mainP ∧ ¬ Entry.Fails o mainP s := by
  obtain ⟨he, hn, hpar⟩ := Checked.emitMain_entry hsrc
  exact ⟨Checked.emitMain_prints hsrc, he, hn, hpar, lower_main, never_fails o s h⟩

/-- The premise holds of a heap of just the layout, above the first page. -/
theorem covers_witness :
    Covers SessionLayout.size (heapWords 4096 SessionLayout.size) 4096 :=
  covers_heap _ (Nat.le_refl _) (by decide +kernel) (by decide +kernel)

end DN.Server.SessionSafe
