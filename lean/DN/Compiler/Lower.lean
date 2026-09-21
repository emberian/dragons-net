-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.Lower

Adapted from the compiler extraction recorded in docs/provenance.json.
These definitions and theorems concern the Lean model. Correspondence to the
HOL4 backend, pretty-printer/parser, ABI and executable is tracked separately
in docs/assurance.md. The model is a restricted 64-bit Pancake fragment.
-/
import DN.Compiler.Semantics
import DN.Compiler.Syntax

namespace DN.Compiler.Lower

open DN.Compiler.Syntax (PExpr PStmt PFun POp emitRegion regionC0)
open DN.Compiler

/-- Lower an emitter expression to a modelled panLang expression, partially.
`POp.mul` is `Panop Mul`; `POp.lt` is `Cmp Less` (SIGNED); `POp.add`/`and_` are
`Op Add`/`Op And`. `loadw` (only `shape = 1` in the region) is `Load One`. The
fused-serve operators lower faithfully to their parse: `POp.eq` (`==`) to
`Cmp Equal a b`; `POp.le` (`<=`) to `Cmp NotLess b a` — the parser SWAPS the
operands (`conv_cmp`: `LeqT ↦ (NotLess, swap)`), so `a <= b ≡ ¬(b < a)`;
`POp.sub` (`-`) to `Op Sub [a;b]`. -/
def lowerExp : PExpr → Option PancakeExp
  | .base        => some .base
  | .const n     => some (.const (BitVec.ofNat 64 n))
  | .var s       => some (.var s)
  | .binop op l r =>
    match lowerExp l, lowerExp r with
    | some a, some b =>
      match op with
      | .add  => some (.op .add a b)
      | .and_ => some (.op .and_ a b)
      | .mul  => some (.mul a b)
      | .lt   => some (.cmp .less a b)
      | .eq   => some (.cmp .equal a b)     -- `a == b` parses to `Cmp Equal a b`
      | .le   => some (.cmp .notLess b a)   -- `a <= b` parses to `Cmp NotLess b a` (parser SWAPS operands)
      | .sub  => some (.op .sub a b)        -- `a - b` parses to `Op Sub [a;b]`
    | _, _ => none
  | .loadw 1 a   =>
    match lowerExp a with
    | some a' => some (.loadWord a')
    | none    => none
  | .loadw _ _ => none
  | .loadb a     =>
    match lowerExp a with
    | some a' => some (.loadByte a')
    | none    => none

mutual
/-- Lower a single non-`dec` statement (the `dec` scoping is handled by
`lowerStmtsFold`, which threads the continuation). Returns `none` on the
function calls, which the semantics model does not cover. -/
def lowerStmt1 : PStmt → Option PancakeProg
  | .dec n v    =>                          -- `dec` as a trailing stmt (unused by region)
    match lowerExp v with
    | some v' => some (.dec n v' .skip)
    | none    => none
  | .assign n v =>
    match lowerExp v with
    | some v' => some (.assign n v')
    | none    => none
  | .store a v  =>
    match lowerExp a, lowerExp v with
    | some a', some v' => some (.store a' v')
    | _, _             => none
  | .storeb a v  =>                         -- `st8 addr, val;` lowers to `StoreByte addr val`
    match lowerExp a, lowerExp v with
    | some a', some v' => some (.storeByte a' v')
    | _, _             => none
  | .ffi name [c, cl, a, al] =>
    match lowerExp c, lowerExp cl, lowerExp a, lowerExp al with
    | some c', some cl', some a', some al' => some (.extCall name c' cl' a' al')
    | _, _, _, _                           => none
  | .ffi _ _ => none
  | .call _ _ _ => none                     -- `var r = f(..)`: outside the modelled subset
  | .ret v      =>
    match lowerExp v with
    | some v' => some (.ret v')
    | none    => none
  | .ite c t e  =>
    match lowerExp c, lowerStmtsFold t, lowerStmtsFold e with
    | some c', some t', some e' => some (.cond c' t' e')
    | _, _, _                   => none
  | .while c b  =>
    match lowerExp c, lowerStmtsFold b with
    | some c', some b' => some (.while_ c' b')
    | _, _             => none
/-- Fold a statement list into the right-nested `Dec`/`Seq` shape. The real parser
wraps each statement in `Seq (Annot ..)` and folds a chain of one binary operator into
an n-ary `Op`, so agreement with it holds only up to that normalisation. -/
def lowerStmtsFold : List PStmt → Option PancakeProg
  | []            => some .skip
  | [s]           => lowerStmt1 s
  | (.dec n v) :: rest =>
    match lowerExp v, lowerStmtsFold rest with
    | some v', some r' => some (.dec n v' r')
    | _, _             => none
  | s :: rest     =>
    match lowerStmt1 s, lowerStmtsFold rest with
    | some s', some r' => some (.seq s' r')
    | _, _             => none
end

/-- An empty body is the empty program. Stated here so the equations of the fold are
elaborated in the module that defines it. -/
theorem lowerStmtsFold_nil : lowerStmtsFold [] = some .skip := by simp [lowerStmtsFold]

/-- Lower a whole emitter function (partial: `none` if any construct is outside
the modelled DN.Compiler fragment). -/
def lower (f : PFun) : Option PancakeProg := lowerStmtsFold f.body

/-- The region program, lowered from the canonical C0 spec — the concrete
`PancakeProg` the emit-correctness theorem runs. The region uses only modelled
constructs, so this is `some prog`. -/
def regionProg : Option PancakeProg := lower (emitRegion regionC0)

/-! ### Totality of `lowerExp` on the fused-serve first-order ops.

`lowerExp` now returns `some` (no longer `none`) on `POp.eq`/`le`/`sub` whenever
both operands lower, mapping each to the Sem construct its parse produces. -/

theorem lowerExp_eq_some {l r : PExpr} {a b : PancakeExp}
    (hl : lowerExp l = some a) (hr : lowerExp r = some b) :
    lowerExp (.binop .eq l r) = some (.cmp .equal a b) := by
  simp only [lowerExp, hl, hr]

theorem lowerExp_le_some {l r : PExpr} {a b : PancakeExp}
    (hl : lowerExp l = some a) (hr : lowerExp r = some b) :
    lowerExp (.binop .le l r) = some (.cmp .notLess b a) := by
  simp only [lowerExp, hl, hr]

theorem lowerExp_sub_some {l r : PExpr} {a b : PancakeExp}
    (hl : lowerExp l = some a) (hr : lowerExp r = some b) :
    lowerExp (.binop .sub l r) = some (.op .sub a b) := by
  simp only [lowerExp, hl, hr]

/-- Totality of `lowerStmt1` on the byte store `st8`: whenever both the address
and value expressions lower, `storeb` lowers (no longer `none`) to the modelled
`StoreByte`. -/
theorem lowerStmt1_storeb_some {a v : PExpr} {a' v' : PancakeExp}
    (ha : lowerExp a = some a') (hv : lowerExp v = some v') :
    lowerStmt1 (.storeb a v) = some (.storeByte a' v') := by
  simp only [lowerStmt1, ha, hv]

end DN.Compiler.Lower
