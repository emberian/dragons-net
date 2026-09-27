-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean.Data.Json
import DN.Compiler.Lower

/-!
# DN.Compiler.Canon

The form in which a lowered program is compared with the tree CakeML's parser builds from its
printed source (`scripts/parser_contract.py`). The parser builds `a + b + c` as one n-ary `Add`
and `a * b * c` nested to the left, and wraps every statement in a sequence; `Lower` builds
whatever the syntax tree held. In the canonical form a chain of `+`, `*` or `&` is nested to the
right and statements are lists, and `canon_eval` shows that it identifies only expressions that
evaluate alike, so the comparison cannot hide a difference behind a rearrangement.
-/

namespace DN.Compiler.Canon

open Lean DN.Compiler.Syntax

variable {σ : Type}

/-! ## Chains of an associative operator, nested to the right -/

/-- `x + y` with the chain `x` nested to the right. -/
def addChain : PancakeExp → PancakeExp → PancakeExp
  | .op .add a b, y => .op .add a (addChain b y)
  | x, y => .op .add x y

/-- `x & y` with the chain `x` nested to the right. -/
def andChain : PancakeExp → PancakeExp → PancakeExp
  | .op .and_ a b, y => .op .and_ a (andChain b y)
  | x, y => .op .and_ x y

/-- `x * y` with the chain `x` nested to the right. -/
def mulChain : PancakeExp → PancakeExp → PancakeExp
  | .mul a b, y => .mul a (mulChain b y)
  | x, y => .mul x y

/-- The canonical form of an expression. -/
def canon : PancakeExp → PancakeExp
  | .op .add l r => addChain (canon l) (canon r)
  | .op .and_ l r => andChain (canon l) (canon r)
  | .op .sub l r => .op .sub (canon l) (canon r)
  | .mul l r => mulChain (canon l) (canon r)
  | .cmp c l r => .cmp c (canon l) (canon r)
  | .loadByte a => .loadByte (canon a)
  | .loadWord a => .loadWord (canon a)
  | .shiftR l r => .shiftR (canon l) (canon r)
  | .const w => .const w
  | .var x => .var x
  | .base => .base

/-! ## The canonical form evaluates as the expression does -/

theorem eval_addChain (s : PancakeState σ) :
    ∀ x y, eval s (addChain x y) = eval s (.op .add x y)
  | .op .add a b, y => by
    simp only [addChain, eval, eval_addChain s b y]
    cases eval s a <;> cases eval s b <;> cases eval s y <;> simp [BitVec.add_assoc]
  | .op .and_ _ _, _ | .op .sub _ _, _ | .const _, _ | .var _, _ | .base, _ | .mul _ _, _
  | .cmp _ _ _, _ | .loadByte _, _ | .loadWord _, _ | .shiftR _ _, _ => rfl

theorem eval_andChain (s : PancakeState σ) :
    ∀ x y, eval s (andChain x y) = eval s (.op .and_ x y)
  | .op .and_ a b, y => by
    simp only [andChain, eval, eval_andChain s b y]
    cases eval s a <;> cases eval s b <;> cases eval s y <;> simp [BitVec.and_assoc]
  | .op .add _ _, _ | .op .sub _ _, _ | .const _, _ | .var _, _ | .base, _ | .mul _ _, _
  | .cmp _ _ _, _ | .loadByte _, _ | .loadWord _, _ | .shiftR _ _, _ => rfl

theorem eval_mulChain (s : PancakeState σ) :
    ∀ x y, eval s (mulChain x y) = eval s (.mul x y)
  | .mul a b, y => by
    simp only [mulChain, eval, eval_mulChain s b y]
    cases eval s a <;> cases eval s b <;> cases eval s y <;> simp [BitVec.mul_assoc]
  | .op _ _ _, _ | .const _, _ | .var _, _ | .base, _ | .cmp _ _ _, _ | .loadByte _, _
  | .loadWord _, _ | .shiftR _ _, _ => rfl

/-- **The canonical form loses nothing.** Two expressions with the same canonical form
evaluate alike in every state, so equal canonical trees mean equal values. -/
theorem canon_eval (s : PancakeState σ) : ∀ e, eval s (canon e) = eval s e
  | .op .add l r => by
    rw [canon, eval_addChain]
    simp only [eval, canon_eval s l, canon_eval s r]
  | .op .and_ l r => by
    rw [canon, eval_andChain]
    simp only [eval, canon_eval s l, canon_eval s r]
  | .op .sub l r => by simp only [canon, eval, canon_eval s l, canon_eval s r]
  | .mul l r => by
    rw [canon, eval_mulChain]
    simp only [eval, canon_eval s l, canon_eval s r]
  | .cmp c l r => by cases c <;> simp only [canon, eval, canon_eval s l, canon_eval s r]
  | .loadByte a => by simp only [canon, eval, canon_eval s a]
  | .loadWord a => by simp only [canon, eval, canon_eval s a]
  | .shiftR l r => by simp only [canon, eval, canon_eval s l, canon_eval s r]
  | .const _ => rfl
  | .var _ => rfl
  | .base => rfl

/-! ## The canonical tree, printed

The names of expressions are CakeML's, as `cake --explore` prints them; statements have short
names of their own, to which the script that reads the parser's tree maps CakeML's forms. -/

def expJson : PancakeExp → Json
  | .const w => Json.arr #["Const", toJson w.toNat]
  | .var x => Json.arr #["Var", toJson x]
  | .base => Json.arr #["BaseAddr"]
  | .op .add l r => Json.arr #["Add", expJson l, expJson r]
  | .op .and_ l r => Json.arr #["And", expJson l, expJson r]
  | .op .sub l r => Json.arr #["Sub", expJson l, expJson r]
  | .mul l r => Json.arr #["Mul", expJson l, expJson r]
  | .cmp .less l r => Json.arr #["Less", expJson l, expJson r]
  | .cmp .equal l r => Json.arr #["Equal", expJson l, expJson r]
  | .cmp .notLess l r => Json.arr #["NotLess", expJson l, expJson r]
  | .loadByte a => Json.arr #["MemLoadByte", expJson a]
  | .loadWord a => Json.arr #["MemLoad", expJson a]
  | .shiftR l r => Json.arr #["Lsr", expJson l, expJson r]

/-- A program as a list of statements: sequences flattened, `skip` dropped, and a declaration
holding the statements in its scope. -/
def blockJson : PancakeProg → List Json
  | .skip => []
  | .seq a b => blockJson a ++ blockJson b
  | .dec v e c => [Json.arr #["dec", toJson v, expJson (canon e), Json.arr (blockJson c).toArray]]
  | .assign v e => [Json.arr #["assign", toJson v, expJson (canon e)]]
  | .store a e => [Json.arr #["store", expJson (canon a), expJson (canon e)]]
  | .storeByte a e => [Json.arr #["storebyte", expJson (canon a), expJson (canon e)]]
  | .cond e c1 c2 =>
    [Json.arr #["if", expJson (canon e), Json.arr (blockJson c1).toArray, Json.arr (blockJson c2).toArray]]
  | .while_ e c => [Json.arr #["while", expJson (canon e), Json.arr (blockJson c).toArray]]
  | .ret e => [Json.arr #["return", expJson (canon e)]]
  | .extCall n a b c d =>
    [Json.arr #["extcall", toJson n, expJson (canon a), expJson (canon b), expJson (canon c),
      expJson (canon d)]]

/-- A function as the contract script compares it: its source, as the gate prints it, and the
canonical tree of its lowering. -/
def program (f : PFun) (source : String) : Except String Json := do
  let some body := Lower.lower f | throw s!"{f.name} does not lower"
  return Json.mkObj [("name", toJson f.name), ("source", toJson source),
    ("params", toJson (f.params.map (·.2))), ("body", Json.arr (blockJson body).toArray)]

end DN.Compiler.Canon
