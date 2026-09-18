import Lean
import DN.Compiler.Checked
import DN.Compiler.Abi

/-! Deterministic differential fixtures: syntax and model results are exported
together, then checked against an independent Python evaluator and real native
code. These are executable tests, not compiler-correctness theorems. -/
namespace DN.Compiler.Baseline
open Syntax Lower Lean

def ops : List POp := [.add, .sub, .mul, .and_, .lt, .le, .eq]

def expressions : List PExpr :=
  ops.map (fun o => .binop o (v "a") (v "b")) ++
  ops.flatMap (fun o => ops.flatMap (fun p =>
    [.binop o (.binop p (v "a") (v "b")) (n 3),
     .binop o (v "a") (.binop p (v "b") (n 3))])) ++
  [n (2^64-1), eAdd (v "a") (n (2^64-1)),
   eSub (v "a") (eSub (v "b") (n 1))]

def boundaries : List Nat := [0, 1, 2, 255, 2^32, 2^63-1, 2^63, 2^64-1]
def values : List (Nat × Nat) :=
  boundaries.flatMap (fun a => boundaries.map (a, ·)) ++
  (List.range 128).map (fun i =>
    ((i * 6364136223846793005 + 1442695040888963407) % 2^64,
     (i * 2862933555777941757 + 3037000493) % 2^64))

def state (a b : Nat) : PancakeState Unit :=
  { locals := fun x => if x == "a" then some (BitVec.ofNat 64 a)
                      else if x == "b" then some (BitVec.ofNat 64 b) else none,
    memory := fun _ => 0, memaddrs := fun _ => false, be := false,
    clock := 128, ffi := (), baseAddr := 0 }

def exprJson : PExpr → Json
  | .var x => toJson x
  | .const x => toJson x
  | .binop o a b => Json.arr #[toJson (opSym o), exprJson a, exprJson b]
  | _ => Json.null -- no loads in this arithmetic fixture family

def functions : List PFun := expressions.zipIdx |>.map (fun (e, i) =>
  { name := "dn_probe_" ++ toString i, exported := true,
    params := [(1,"a"),(1,"b")], body := [.ret e] })

/-- Exercises declaration scoping, assignment, branches, bounded loops, and
early return in a loop. Memory instructions are tested by the native kernels. -/
def control : PFun :=
  { name := "dn_control", exported := true, params := [(1,"a"),(1,"b")], body :=
    [.dec "limit" (eAnd (v "a") (n 31)), .dec "acc" (v "b"), .dec "i" (n 0),
     .while (eLt (v "i") (v "limit"))
       [.ite (eEq (v "i") (n 7)) [.ret (v "acc")] [],
        .ite (eLt (v "acc") (n 0)) [.assign "acc" (eAdd (v "acc") (v "i"))]
          [.dec "temp" (eMul (v "acc") (n 3)), .assign "acc" (eAdd (v "temp") (n 1))],
        .assign "i" (eAdd (v "i") (n 1))], .ret (v "acc")] }

/-- All load-address nesting pairs must parse. The two inner-byte cases are
parser/model tests only: their absolute 8-bit result is not a usable native
userspace pointer. Inner-word cases also execute against real pointer cells. -/
def nestedLoads : List PExpr :=
  [.loadb (.loadb (v "p")), .loadb (.loadw 1 (v "p")),
   .loadw 1 (.loadb (v "p")), .loadw 1 (.loadw 1 (v "p"))]

def nestedFunctions : List PFun := nestedLoads.zipIdx |>.map (fun (e, i) =>
  { name := "dn_nested_" ++ toString i, exported := true,
    params := [(1,"p")], body := [.ret e] })

def nestedState : PancakeState Unit :=
  { locals := fun x => if x == "p" then some 0 else none,
    memory := fun p => if p == 0 then 8 else if p == 8 then 0x0123456789ABCDEF else 0,
    memaddrs := fun p => p == 0 || p == 8 || p == 16,
    be := false, clock := 0, ffi := (), baseAddr := 0 }

def fixture : Except String Json := do
  let wrapped := (functions ++ [control]).map Abi.wordResult
  let sources ← (functions ++ [control]).mapM Abi.emitWord
  let memorySources ← nestedFunctions.mapM Abi.emitWord
  let memoryExpected ← nestedLoads.mapM fun e => do
    let some lowered := lowerExp e | throw "nested load does not lower"
    let some value := eval nestedState lowered | throw "nested model load failed"
    pure value.toNat
  let cases ← expressions.mapM fun e => do
    let some lowered := lowerExp e | throw "fixture does not lower"
    let expected ← values.mapM fun (a,b) => do
      let some result := eval (state a b) lowered | throw "fixture evaluation failed"
      pure result.toNat
    pure (Json.mkObj [("expression", exprJson e), ("expected", toJson expected)])
  let some prog := lower control | throw "control fixture does not lower"
  let oracle : Oracle Unit := ⟨fun _ _ _ _ => .final ⟨"unexpected FFI"⟩⟩
  let controls ← values.mapM fun (a,b) => do
    let (some (.return_ result), _) := PancakeSem oracle prog (state a b)
      | throw "control fixture did not return"
    pure result.toNat
  -- Check the modeled ABI adapter as well as the original return-value model.
  for (f, index) in wrapped.zipIdx do
    let some p := lower f | throw "ABI wrapper does not lower"
    for (a,b) in values do
      let original := state a b
      let s := { original with locals := setLocal original.locals "dn_result" 16, memaddrs := fun address => address == 16 }
      let (result, final) := PancakeSem oracle p s
      let some originalFunction := (functions ++ [control])[index]?
        | throw "original function missing"
      let some originalProg := lower originalFunction
        | throw "original function missing"
      let (some (.return_ expected), _) := PancakeSem oracle originalProg original
        | throw "original did not return"
      unless result == some (.return_ 0) && final.memory 16 == expected do
        throw "ABI model output-slot mismatch"
  return Json.mkObj [("source", toJson (String.join (sources ++ memorySources))),
    ("values", toJson (values.map (fun (a,b) => [a,b]))),
    ("cases", toJson cases), ("control", toJson controls),
    ("nested_load_expected", toJson memoryExpected)]

end DN.Compiler.Baseline
