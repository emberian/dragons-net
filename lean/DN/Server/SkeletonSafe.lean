-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.AnalyzerSound
import DN.Server.Skeleton

/-!
# DN.Server.SkeletonSafe

**The server loop never fails, whatever its host does.** For every FFI oracle, every clock and
every content of the heap, a run of `Skeleton.main` from a state whose heap covers its layout above
the header ends only as a run may end — out of clock, a call the host ended, or a return — and
never in `Fail` (`Entry.Fails`). The safety analysis of `DN.Compiler.Analyzer` accepts the program,
and `DN.Compiler.AnalyzerSound` proves that a program it accepts never fails; `printed_never_fails`
ties this to the text the gate prints. That the Pancake parser reads the text as its lowering is
checked of this program by `scripts/parser_contract.py`, not proved.
-/

namespace DN.Server.SkeletonSafe

open DN.Compiler DN.Compiler.Analyzer DN.Server

variable {σ : Type}

theorem lowers : (Lower.lower Skeleton.main).isSome = true := by decide +kernel

/-- The loop's `main`, as it lowers. -/
def mainP : PancakeProg := (Lower.lower Skeleton.main).get lowers

theorem lower_main : Lower.lower Skeleton.main = some mainP := (Option.some_get lowers).symm

/-- The analysis accepts the program: computed by the kernel. -/
theorem accepted : (check Layout.size mainP).toBool = true := by decide +kernel

theorem checked : check Layout.size mainP = .ok () := ok_of_toBool accepted

/-- **The server loop never fails, whatever its host does.** -/
theorem never_fails (o : Oracle σ) (s : PancakeState σ)
    (h : Covers Layout.size s.memaddrs s.baseAddr) : ¬ Entry.Fails o mainP s :=
  Analyzer.never_fails o checked s h

/-- The same of the text the gate prints: it is the loop's own, the entry has the shape the
semantics runs, and the lowering is the program `never_fails` is about. -/
theorem printed_never_fails (o : Oracle σ) (s : PancakeState σ)
    (h : Covers Layout.size s.memaddrs s.baseAddr) {src : String}
    (hsrc : Skeleton.source = .ok src) :
    src = Syntax.ppFun Skeleton.main ∧ Skeleton.main.exported = false ∧
      Skeleton.main.name = "main" ∧ Skeleton.main.params = [] ∧
      Lower.lower Skeleton.main = some mainP ∧ ¬ Entry.Fails o mainP s := by
  obtain ⟨he, hn, hpar⟩ := Checked.emitMain_entry hsrc
  exact ⟨Checked.emitMain_prints hsrc, he, hn, hpar, lower_main, never_fails o s h⟩

/-- The premise holds of a heap of just the layout, above the first page. -/
theorem covers_witness : Covers Layout.size (heapWords 4096 Layout.size) 4096 :=
  covers_heap _ (Nat.le_refl _) (by decide) (by decide)

end DN.Server.SkeletonSafe
