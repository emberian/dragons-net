-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Gen

/-!
# DN.Compiler.GenCorpus

The reduced cases the generated lane recorded: the program, its memory plan, its input, and what
the model makes of it. `mutants` are the cases in `tests/corpus/mutants/`, one for each defect
planted in the printer: `scripts/native_fuzz.py` reduces each again from the program it started
from and requires the same case, whose compiled code agrees with the model as printed and
disagrees as the defective printer prints it. `found` are the cases in `tests/corpus/found/`, each a
disagreement a run found and the fix it was kept for: the lane runs each as it stands and
requires the compiled code to agree with the model. The regressions below keep the model's
answers fixed on their own.
-/

namespace DN.Compiler.GenCorpus

open Lean DN.Compiler.Syntax DN.Compiler.Gen DN.Compiler.SyntaxJson

structure Case where
  name : String
  f : PFun
  plan : Plan
  input : Vector
  result : Nat
  changed : List (Nat × Nat × Nat)

private def reduced (params : List String) (body : List PStmt) : PFun :=
  { name := "dn_min", exported := true, params := params.map fun x => (1, x), body }

private def noParams : Plan := { params := [], entries := [] }

private def zeroInput : Vector := { data := [], seed := 0, mask := 0 }

def mutants : List Case :=
  [{ name := "if-negated", f := reduced [] [.ite (n 0) [.ret (n 0)] [.ret (n 1)]],
     plan := noParams, input := zeroInput,
     result := 1, changed := [] },
   { name := "ld8-as-lds", f := reduced ["p"] [.dec "x0" (.loadb (v "p")), .ret (v "x0")],
     plan := { params := [.pointer "p" 0 4000], entries := [] },
     input := { data := [], seed := 0, mask := 0xFFFFFFFFFFFFFFFF }, result := 13, changed := [] },
   { name := "le-as-lt", f := reduced [] [.ret (eLe (n 0) (n 0))],
     plan := noParams, input := zeroInput,
     result := 1, changed := [] },
   { name := "shift-off-by-one", f := reduced [] [.ret (.shr (n 1) (n 0))],
     plan := noParams, input := zeroInput,
     result := 1, changed := [] },
   { name := "st8-as-st", f := reduced ["p"] [.storeb (v "p") (eAdd (n 1) (n 255)), .ret (n 0)],
     plan := { params := [.pointer "p" 0 0], entries := [] },
     input := zeroInput, result := 0, changed := [] },
   { name := "xor-as-or", f := reduced [] [.ret (eXor (n 1) (n 1))],
     plan := noParams, input := zeroInput,
     result := 0, changed := [] },
   { name := "shl-as-shr", f := reduced [] [.ret (.shl (n 1) (n 1))],
     plan := noParams, input := zeroInput,
     result := 2, changed := [] }]

/-- None yet: no run has found a disagreement to keep. -/
def found : List Case := []

/-- Whether the model still gives case `name` the answer recorded for it. -/
def holds (name : String) : Bool :=
  match (mutants ++ found).find? (·.name == name) with
  | some c =>
    match runModel c.f c.plan c.input with
    | .ok o => o.result == c.result && o.changed == c.changed
    | .error _ => false
  | none => false

def regression_801 : Bool := holds "if-negated"
def regression_802 : Bool := holds "ld8-as-lds"
def regression_803 : Bool := holds "le-as-lt"
def regression_804 : Bool := holds "shift-off-by-one"
def regression_805 : Bool := holds "st8-as-st"
def regression_934 : Bool := holds "xor-as-or"
def regression_935 : Bool := holds "shl-as-shr"

def caseJson (c : Case) : Except String Json := do
  let o ← runModel c.f c.plan c.input
  return Json.mkObj [("name", toJson c.name), ("plan", planJson c.plan), ("program", funJson c.f),
    ("input", vectorJson c.input), ("model", Json.mkObj (outcomeJson o))]

/-- The cases, as the lane compares them with the recorded files. -/
def json : Except String Json := do
  return Json.mkObj [("mutants", Json.arr (← mutants.mapM caseJson).toArray),
    ("found", Json.arr (← found.mapM caseJson).toArray)]

end DN.Compiler.GenCorpus
