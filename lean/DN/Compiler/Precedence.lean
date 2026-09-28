-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Canon
import DN.Compiler.Checked

/-!
# DN.Compiler.Precedence

Where an operand may stand without parentheses. `reads` is the part of the Pancake grammar
(`pancake/parser/panPEGScript.sml`, lines 285-357 at `e8eca63` and 273-345 at `ed31510`) that the
printer depends on: for each place an operand can stand and each head it can have, whether the
parser reads that operand, printed bare, as one operand there. `scripts/parser_contract.py`
checks every cell against the pinned parsers, both ways: a cell that says so has to read as
intended, any other has to be refused or read differently. `printed_well` proves, for every
expression the gate accepts, that the printer leaves bare only what the table allows, anywhere
in it, and prints every shift distance as a bare number.
-/

namespace DN.Compiler.Precedence

open Lean DN.Compiler.Syntax

/-- Where an operand stands: the whole expression, an operand of a comparison, of `==`, the
address after `lds 1` or `ld8`, an operand of `&`, the left of `>>>`, or an operand of `+`, `-`
or `*`. -/
inductive Slot
  | top | cmp | eq | lds | ld8 | and_ | shiftLeft | add | sub | mul
  deriving DecidableEq

inductive Side
  | left | right
  deriving DecidableEq

/-- The head of a printed expression, as far as the grammar's levels tell them apart. -/
inductive Kind
  | atom | add | sub | mul | and_ | lt | le | eq | lds | ld8 | shr
  deriving DecidableEq

def kind : PExpr → Kind
  | .const _ | .var _ | .base => .atom
  | .binop .add _ _ => .add
  | .binop .sub _ _ => .sub
  | .binop .mul _ _ => .mul
  | .binop .and_ _ _ => .and_
  | .binop .lt _ _ => .lt
  | .binop .le _ _ => .le
  | .binop .eq _ _ => .eq
  | .loadw _ _ => .lds
  | .loadb _ => .ld8
  | .shr _ _ => .shr

/-- Whether both pinned parsers read an operand of head `k`, printed bare in `slot` on `side`,
as one operand there. A comparison operand is at `ELoadNT`, so a load may stand there but a
second comparison may not; the address after `lds 1` is at `ELoadByteNT` and after `ld8` at
`ELoad32NT`, so `lds 1 ld8 x` reads and `ld8 ld8 x` does not; `+` and `-` operands are at
`EMulNT` and `*` operands one level below `EMulNT` (`ENotNT` in the release, `EFieldNT` in the
patched source), where of the printed heads only atoms stand. A chain of one associative
operator reads as that chain, which the canonical form nests to the right. -/
def reads : Slot → Side → Kind → Bool
  | _, _, .atom => true
  | .top, _, _ => true
  | .cmp, _, k => !(k == .lt || k == .le || k == .eq)
  | .eq, _, k => k != .eq
  | .lds, _, k => [Kind.add, .sub, .mul, .and_, .ld8, .shr].contains k
  | .ld8, _, k => [Kind.add, .sub, .mul, .and_, .shr].contains k
  | .and_, _, k => [Kind.add, .sub, .mul, .and_, .shr].contains k
  | .shiftLeft, _, k => [Kind.add, .sub, .mul, .shr].contains k
  | .add, .left, k => [Kind.add, .sub, .mul].contains k
  | .add, .right, k => [Kind.add, .mul].contains k
  | .sub, .left, k => [Kind.add, .sub, .mul].contains k
  | .sub, .right, k => k == .mul
  | .mul, _, k => k == .mul

/-- Where the operands of a binary operator stand. -/
def slotOf : POp → Slot
  | .add => .add | .sub => .sub | .mul => .mul | .and_ => .and_
  | .lt => .cmp | .le => .cmp | .eq => .eq

/-! ## What the printer leaves bare -/

/-- Whether `wrapOperand` leaves `child` without parentheses. -/
def operandBare (parent : POp) : PExpr → Bool
  | .binop op _ _ => isAssoc parent && parent == op
  | .loadw _ _ | .loadb _ | .shr _ _ => false
  | _ => true

/-- Whether `wrapAtom` leaves a load's address without parentheses. -/
def addressBare : PExpr → Bool
  | .const _ | .var _ | .base => true
  | _ => false

theorem wrapOperand_eq (parent : POp) (child : PExpr) (s : String) :
    wrapOperand parent child s = if operandBare parent child then s else "(" ++ s ++ ")" := by
  cases child <;> simp [wrapOperand, operandBare]

theorem wrapAtom_eq (child : PExpr) (s : String) :
    wrapAtom child s = if addressBare child then s else "(" ++ s ++ ")" := by
  cases child <;> simp [wrapAtom, addressBare]

/-! ## The printer, in those terms

These pin `ppExpr` to the decisions above, so a change to the printer's parentheses changes what
the theorems below are about, or fails to build. -/

theorem ppExpr_binop (op : POp) (l r : PExpr) :
    ppExpr (.binop op l r) =
      (if operandBare op l then ppExpr l else "(" ++ ppExpr l ++ ")") ++ " " ++ opSym op ++ " " ++
        (if operandBare op r then ppExpr r else "(" ++ ppExpr r ++ ")") := by
  simp only [ppExpr, wrapOperand_eq]

theorem ppExpr_loadw (shape : Nat) (a : PExpr) :
    ppExpr (.loadw shape a) = "lds " ++ toString shape ++ " " ++
      (if addressBare a then ppExpr a else "(" ++ ppExpr a ++ ")") := by
  simp only [ppExpr, wrapAtom_eq]

theorem ppExpr_loadb (a : PExpr) :
    ppExpr (.loadb a) = "ld8 " ++ (if addressBare a then ppExpr a else "(" ++ ppExpr a ++ ")") := by
  simp only [ppExpr, wrapAtom_eq]

/-- The left of `>>>` is always parenthesized, and the distance printed as it stands. -/
theorem ppExpr_shr (l r : PExpr) : ppExpr (.shr l r) = "(" ++ ppExpr l ++ ") >>> " ++ ppExpr r := by
  simp only [ppExpr]

/-- Every operand the printer leaves bare, anywhere in `e`, stands where the parsers read it as
one operand, and every shift distance is a literal, which prints as the bare number the grammar
expects after `>>>` (the left of `>>>` is always parenthesized, `ppExpr_shr`). -/
def PrintedWell : PExpr → Prop
  | .binop op l r =>
    (operandBare op l = true → reads (slotOf op) .left (kind l) = true) ∧
    (operandBare op r = true → reads (slotOf op) .right (kind r) = true) ∧
    PrintedWell l ∧ PrintedWell r
  | .loadw _ a => (addressBare a = true → reads .lds .left (kind a) = true) ∧ PrintedWell a
  | .loadb a => (addressBare a = true → reads .ld8 .left (kind a) = true) ∧ PrintedWell a
  | .shr l r => (∃ k, r = .const k) ∧ PrintedWell l
  | .const _ | .var _ | .base => True

theorem operand_reads (op : POp) (side : Side) (child : PExpr) :
    operandBare op child = true → reads (slotOf op) side (kind child) = true := by
  cases child with
  | binop cop _ _ =>
    cases op <;> cases cop <;> cases side <;> simp [operandBare, kind, reads, slotOf, isAssoc]
  | _ => cases op <;> cases side <;> simp [operandBare, kind, reads, slotOf]

theorem address_reads (slot : Slot) (child : PExpr) :
    addressBare child = true → reads slot .left (kind child) = true := by
  cases child <;> simp [addressBare, kind, reads]

/-- **The printer's parentheses suffice**, for every expression the gate accepts, in either
profile. -/
theorem printed_well {p : Checked.Profile} {scope : List String} :
    ∀ e, Checked.expression p scope e = .ok () → PrintedWell e
  | .binop op l r, h => by
    obtain ⟨hl, hr⟩ := Checked.seq_ok h
    exact ⟨operand_reads op .left l, operand_reads op .right r, printed_well l hl,
      printed_well r hr⟩
  | .loadw shape a, h => by
    have ha : Checked.expression p scope a = .ok () := by
      by_cases hs : shape = 1
      · simpa [Checked.expression, hs] using h
      · simp [Checked.expression, hs] at h
    exact ⟨address_reads .lds a, printed_well a ha⟩
  | .loadb a, h => ⟨address_reads .ld8 a, printed_well a h⟩
  | .shr l r, h => by
    cases r with
    | const k =>
      have hl : Checked.expression p scope l = .ok () := by
        by_cases hk : k < 64
        · simpa [Checked.expression, hk] using h
        · simp [Checked.expression, hk] at h
      exact ⟨⟨k, rfl⟩, printed_well l hl⟩
    | _ => simp [Checked.expression] at h
  | .const _, _ | .var _, _ | .base, _ => trivial

/-! ## Every cell, for the parsers to be held to

Each cell is a function returning the representative operand printed bare in its place, with the
canonical tree of the intended reading, what `reads` says of it, and whether the printer leaves
that operand bare there, which makes it a cell `printed_well` relies on. -/

def slots : List (Slot × Side) :=
  [(.top, .left), (.cmp, .left), (.cmp, .right), (.eq, .left), (.eq, .right), (.lds, .left),
   (.ld8, .left), (.and_, .left), (.and_, .right), (.shiftLeft, .left), (.add, .left),
   (.add, .right), (.sub, .left), (.sub, .right), (.mul, .left), (.mul, .right)]

/-- A representative operand of each head, over the parameters `x` and `y`. -/
def operands : List PExpr :=
  [v "x", n 7, .base, eAdd (v "x") (v "y"), eSub (v "x") (v "y"), eMul (v "x") (v "y"),
   eAnd (v "x") (v "y"), eLt (v "x") (v "y"), eLe (v "x") (v "y"), eEq (v "x") (v "y"),
   .loadw 1 (v "x"), .loadb (v "x"), .shr (v "x") (n 2)]

/-- `child`, printed bare, in its place, the expression that placement is meant to be, and
whether the printer leaves `child` bare there. -/
def placed (slot : Slot) (side : Side) (child : PExpr) : String × PExpr × Bool :=
  let c := ppExpr child
  let pair (op : POp) := match side with
    | .left => (c ++ " " ++ opSym op ++ " c", .binop op child (v "c"), operandBare op child)
    | .right => ("a " ++ opSym op ++ " " ++ c, .binop op (v "a") child, operandBare op child)
  match slot with
  | .top => (c, child, false)
  | .cmp => pair .lt
  | .eq => pair .eq
  | .lds => ("lds 1 " ++ c, .loadw 1 child, addressBare child)
  | .ld8 => ("ld8 " ++ c, .loadb child, addressBare child)
  | .and_ => pair .and_
  | .shiftLeft => (c ++ " >>> 3", .shr child (n 3), false)
  | .add => pair .add
  | .sub => pair .sub
  | .mul => pair .mul

def Slot.label : Slot → String
  | .top => "top" | .cmp => "cmp" | .eq => "eq" | .lds => "lds" | .ld8 => "ld8" | .and_ => "and"
  | .shiftLeft => "shift-left" | .add => "add" | .sub => "sub" | .mul => "mul"

def Side.label : Side → String
  | .left => "left" | .right => "right"

def cells : Except String Json := do
  let mut out : Array Json := #[]
  for (slot, side) in slots do
    for child in operands do
      let (text, intended, bare) := placed slot side child
      let name := s!"dn_cell_{out.size}"
      let f : PFun :=
        { name := name, exported := true, params := [(1, "a"), (1, "c"), (1, "x"), (1, "y")],
          body := [.ret intended] }
      let source := "export fun " ++ name ++ "(1 a, 1 c, 1 x, 1 y) {\n  return " ++ text ++ ";\n}\n"
      let tree ← Canon.program f source
      out := out.push (Json.mkObj [("tree", tree), ("reads", toJson (reads slot side (kind child))),
        ("used_by_proof", toJson bare), ("cell", toJson s!"{slot.label}/{side.label}: {text}")])
  return Json.arr out

end DN.Compiler.Precedence
