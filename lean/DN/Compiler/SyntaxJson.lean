-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean.Data.Json
import DN.Compiler.Syntax

/-!
# DN.Compiler.SyntaxJson

A source program as data. The generated-programs lane prints programs in this form for the
independent interpreter (`scripts/fuzz_interp.py`), the reducer writes candidates back in it, and
`funOfJson` reads them for the model. The lowered program has its own form, `Canon.program`.
-/

namespace DN.Compiler.SyntaxJson

open Lean DN.Compiler.Syntax

def exprJson : PExpr → Json
  | .const k => toJson k
  | .var x => toJson x
  | .base => Json.arr #["@base"]
  | .binop op l r => Json.arr #[toJson (opSym op), exprJson l, exprJson r]
  | .loadw sh a => Json.arr #["lds", toJson sh, exprJson a]
  | .loadb a => Json.arr #["ld8", exprJson a]
  | .shr l r => Json.arr #[">>>", exprJson l, exprJson r]

mutual
def stmtJson : PStmt → Json
  | .dec x e => Json.arr #["var", toJson x, exprJson e]
  | .assign x e => Json.arr #["set", toJson x, exprJson e]
  | .store a e => Json.arr #["st", exprJson a, exprJson e]
  | .storeb a e => Json.arr #["st8", exprJson a, exprJson e]
  | .ffi name args => Json.arr #["ffi", toJson name, Json.arr (args.map exprJson).toArray]
  | .call r name args =>
    Json.arr #["call", toJson r, toJson name, Json.arr (args.map exprJson).toArray]
  | .ret e => Json.arr #["return", exprJson e]
  | .ite e t f => Json.arr #["if", exprJson e, blockJson t, blockJson f]
  | .while e b => Json.arr #["while", exprJson e, blockJson b]
def blockJson : List PStmt → Json
  | ss => Json.arr (ss.map stmtJson).toArray
end

def funJson (f : PFun) : Json :=
  Json.mkObj [("name", toJson f.name), ("params", toJson (f.params.map (·.2))),
    ("body", blockJson f.body)]

def opOfSym (s : String) : Option POp := POp.all.find? (opSym · == s)

/-- How deeply the readers below follow a nested program before giving up. -/
def jsonDepth : Nat := 10000

def exprOfJson : Nat → Json → Except String PExpr
  | 0, _ => throw "an expression nested too deeply"
  | fuel + 1, j => do
    if let .ok k := j.getNat? then return .const k
    if let .ok x := j.getStr? then return .var x
    match (← j.getArr?).toList with
    | [.str "@base"] => return .base
    | [.str "lds", sh, a] => return .loadw (← sh.getNat?) (← exprOfJson fuel a)
    | [.str "ld8", a] => return .loadb (← exprOfJson fuel a)
    | [.str ">>>", l, r] => return .shr (← exprOfJson fuel l) (← exprOfJson fuel r)
    | [.str s, l, r] =>
      match opOfSym s with
      | some op => return .binop op (← exprOfJson fuel l) (← exprOfJson fuel r)
      | none => throw s!"unknown operator {s}"
    | _ => throw s!"not an expression: {j.compress}"

def stmtOfJson : Nat → Json → Except String PStmt
  | 0, _ => throw "a statement nested too deeply"
  | fuel + 1, j => do
    let block (b : Array Json) := b.toList.mapM (stmtOfJson fuel)
    let e := exprOfJson jsonDepth
    match (← j.getArr?).toList with
    | [.str "var", .str x, v] => return .dec x (← e v)
    | [.str "set", .str x, v] => return .assign x (← e v)
    | [.str "st", a, v] => return .store (← e a) (← e v)
    | [.str "st8", a, v] => return .storeb (← e a) (← e v)
    | [.str "return", v] => return .ret (← e v)
    | [.str "if", c, .arr thn, .arr els] => return .ite (← e c) (← block thn) (← block els)
    | [.str "while", c, .arr b] => return .while (← e c) (← block b)
    | [.str "ffi", .str name, .arr args] => return .ffi name (← args.toList.mapM e)
    | [.str "call", .str r, .str name, .arr args] => return .call r name (← args.toList.mapM e)
    | _ => throw s!"not a statement: {j.compress}"

def funOfJson (j : Json) : Except String PFun := do
  let params := (← j.getObjValAs? (List String) "params").map fun x => (1, x)
  let body ← (← (← j.getObjVal? "body").getArr?).toList.mapM (stmtOfJson jsonDepth)
  return { name := ← j.getObjValAs? String "name", exported := true, params, body }

end DN.Compiler.SyntaxJson
