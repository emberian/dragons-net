-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean.Data.Json
import DN.Compiler.Checked
import DN.Compiler.SyntaxJson

/-!
# DN.Compiler.Input

**A program from outside** (issue #8): `dn-compiler compile FILE` reads one exported function, and the
functions it calls, as JSON of version `inputVersion`, and prints it through the gate, or refuses it
with a diagnostic whose code is stable across releases (`Diagnostic.code`). The form of a function is
`SyntaxJson`'s; the file around it names the version and nothing else. docs/compiler-input.md is the
format's description.

What it refuses, before the gate: a file that is not JSON, of another version, larger than
`maxBytes`, of more than `maxDepth` levels of JSON, with a field the format does not have, or a form
that is no expression, statement or function. The gate's refusals keep their reasons, one code each.
A key given twice takes its last value, as the JSON reader has it.
-/

namespace DN.Compiler.Input

open Lean DN.Compiler.Syntax DN.Compiler.SyntaxJson

/-- The version of the format this compiler reads; a file of another is refused. -/
def inputVersion : Nat := 1

/-- The most bytes a file may have, and how many levels of JSON it may nest. -/
def maxBytes : Nat := 1 <<< 18
def maxDepth : Nat := 256

/-- Why an input is refused. -/
inductive Problem
  | notJson (detail : String)
  | version (given : Option Nat)
  | tooLarge (bytes : Nat)
  | tooDeep
  | unknownField (field : String)
  | malformed (detail : String)
  | refused (reason : Checked.Reason)

/-- The stable code of each refusal: a new reason gets a new code, and none is ever reused. -/
def reasonCode : Checked.Reason → Nat
  | .exportedName => 100 | .foreignNamespace => 101 | .parameterCount => 102
  | .parameterShape => 103 | .parameterName => 104 | .duplicateParameter => 105
  | .literalWidth => 106 | .unboundVariable => 107 | .baseAddress => 108 | .loadShape => 109
  | .shiftAmount => 110 | .declarationName => 111 | .redeclaration => 112
  | .unboundAssignment => 113 | .callEffect => 114 | .callArity => 115 | .functionName => 116
  | .externalEffect => 117 | .externalArity => 118 | .notExported => 119 | .entryShape => 120
  | .unreachable => 121 | .missingReturn => 122 | .recursion => 123

def Problem.code : Problem → Nat
  | .notJson _ => 1 | .version _ => 2 | .tooLarge _ => 3 | .tooDeep => 4 | .unknownField _ => 5
  | .malformed _ => 6 | .refused r => reasonCode r

def Problem.message : Problem → String
  | .notJson d => s!"not JSON: {d}"
  | .version (some g) => s!"input version {g}, where this compiler reads {inputVersion}"
  | .version none => s!"an input version this compiler does not read: it reads {inputVersion}"
  | .tooLarge _ => s!"more than {maxBytes} bytes"
  | .tooDeep => s!"more than {maxDepth} levels of JSON"
  | .unknownField f => s!"a field the format does not have: {f}"
  | .malformed d => d
  | .refused r => r.message

/-- How the compiler ends on a refusal: 1 if the gate refused the function, 3 if the input is not of
the format. -/
def Problem.status : Problem → UInt32
  | .refused _ => 1
  | _ => 3

/-- How a refusal is printed: `error[DN0107]: variable not in scope`, at most 300 characters of
message, since a message may quote the input. -/
def Problem.render (p : Problem) : String :=
  let digits := toString p.code
  let m := p.message
  s!"error[DN{"".pushn '0' (4 - digits.length)}{digits}]: {if m.length > 300 then (m.take 300).toString ++ "..." else m}"

/-- The fields an object of the format may have, every one of them. -/
def onlyFields (j : Json) (allowed : List String) : Except Problem Unit := do
  let .ok obj := j.getObj? | throw (.malformed s!"not an object: {j.compress}")
  for ⟨k, _⟩ in obj.toArray do
    unless allowed.contains k do throw (.unknownField k)

/-- How deeply `j` nests, counted no further than `bound`. -/
def depth : Nat → Json → Nat
  | 0, _ => 0
  | bound + 1, .arr a => 1 + a.toList.foldl (fun d x => max d (depth bound x)) 0
  | bound + 1, .obj o => 1 + o.toArray.toList.foldl (fun d x => max d (depth bound x.2)) 0
  | _, _ => 0

/-- A function of the input, its fields checked. -/
def functionOf (j : Json) : Except Problem PFun := do
  onlyFields j ["name", "params", "body"]
  (funOfJson j).mapError .malformed

/-- The input: the exported function and the functions it calls. -/
structure Program where
  function : PFun
  calls : List PFun

def read (text : String) : Except Problem Program := do
  if text.utf8ByteSize > maxBytes then throw (.tooLarge text.utf8ByteSize)
  let j ← (Json.parse text).mapError .notJson
  onlyFields j ["dn_input", "function", "calls"]
  -- The number is compared, never printed whole: a version of a million digits is one line.
  match j.getObjVal? "dn_input" with
  | .ok (.num v) =>
    unless v.exponent == 0 && v.mantissa == (inputVersion : Int) do
      throw (.version (if v.exponent == 0 && 0 ≤ v.mantissa && v.mantissa < 1000 then some v.mantissa.toNat
        else none))
  | .ok _ => throw (.version none)
  | .error _ => throw (.malformed "no dn_input: the format's version")
  if depth (maxDepth + 1) j > maxDepth then throw .tooDeep
  let f ← functionOf (← (j.getObjVal? "function").mapError .malformed)
  let calls ← match j.getObjVal? "calls" with
    | .ok (.arr a) => a.toList.mapM fun c => do
        let g ← functionOf c
        pure { g with exported := false }
    | .ok v => throw (.malformed s!"calls is not a list: {v.compress}")
    | .error _ => pure []
  return ⟨f, calls⟩

/-- The input printed through the gate, or why not. -/
def compile (text : String) : Except Problem String := do
  let p ← read text
  (Checked.emitWith p.calls p.function).mapError .refused

/-- **No two reasons share a code**, and none is an input's. -/
theorem codes_distinct : ∀ a b : Checked.Reason, reasonCode a = reasonCode b → a = b := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (simp [reasonCode] at h)

theorem codes_apart (r : Checked.Reason) : 100 ≤ reasonCode r := by
  cases r <;> simp [reasonCode]

end DN.Compiler.Input
