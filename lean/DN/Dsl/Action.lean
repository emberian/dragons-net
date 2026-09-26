-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Kernels

/-!
# DN.Dsl.Action

A closed language of replies over one input line and one output buffer, embedded deeply: a
program is a value of `Act`, `Act.run` says what it does, and `Act.compile` turns it into the
emitted Pancake subset. `DN.Dsl.Correct` proves once, by induction over the language, that the
compiled code of every program does what `Act.run` says. docs/decisions/0001-embedding.md
records why the embedding is deep.
-/

namespace DN.Dsl

open DN.Compiler DN.Compiler.Syntax

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List (BitVec 8) := s.toList.map (fun c => BitVec.ofNat 8 c.toNat)

/-- Reply actions. -/
inductive Act
  /-- Append these bytes to the output. -/
  | lit (bytes : List (BitVec 8))
  /-- Run `thn` if the input starts with `keyword`, `els` otherwise. -/
  | ifPrefix (keyword : List (BitVec 8)) (thn els : Act)
  /-- Run `first`, then `second`. -/
  | seq (first second : Act)

/-- What an action does: the output after it, given the input and the output before it. -/
def Act.run : Act → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)
  | .lit bytes, _, out => out ++ bytes
  | .ifPrefix keyword thn els, inp, out =>
    if keyword.isPrefixOf inp then thn.run inp out else els.run inp out
  | .seq first second, inp, out => second.run inp (first.run inp out)

/-- The most bytes an action can append. -/
def Act.maxLen : Act → Nat
  | .lit bytes => bytes.length
  | .ifPrefix _ thn els => max thn.maxLen els.maxLen
  | .seq first second => first.maxLen + second.maxLen

/-- Keywords short enough to compare against a length with the signed comparison. -/
def Act.Fits : Act → Prop
  | .lit _ => True
  | .ifPrefix keyword thn els => keyword.length < 2 ^ 63 ∧ thn.Fits ∧ els.Fits
  | .seq first second => first.Fits ∧ second.Fits

/-- `Act.Fits`, computed. -/
def Act.fitsB : Act → Bool
  | .lit _ => true
  | .ifPrefix keyword thn els => decide (keyword.length < 2 ^ 63) && thn.fitsB && els.fitsB
  | .seq first second => first.fitsB && second.fitsB

theorem Act.fits_of_fitsB : ∀ (a : Act), a.fitsB = true → a.Fits
  | .lit _, _ => trivial
  | .ifPrefix _ thn els, h => by
    simp only [Act.fitsB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, Act.fits_of_fitsB thn h.1.2, Act.fits_of_fitsB els h.2⟩
  | .seq first second, h => by
    simp only [Act.fitsB, Bool.and_eq_true] at h
    exact ⟨Act.fits_of_fitsB first h.1, Act.fits_of_fitsB second h.2⟩

theorem Act.run_length_le : ∀ (a : Act) (inp out : List (BitVec 8)),
    (a.run inp out).length ≤ out.length + a.maxLen
  | .lit bytes, _, out => by simp [Act.run, Act.maxLen]
  | .ifPrefix keyword thn els, inp, out => by
    have h1 := Act.run_length_le thn inp out
    have h2 := Act.run_length_le els inp out
    simp only [Act.run, Act.maxLen]
    split <;> omega
  | .seq first second, inp, out => by
    have h1 := Act.run_length_le first inp out
    have h2 := Act.run_length_le second inp (first.run inp out)
    simp only [Act.run, Act.maxLen]
    omega

/-- An action only appends. -/
theorem Act.length_le_run : ∀ (a : Act) (inp out : List (BitVec 8)),
    out.length ≤ (a.run inp out).length
  | .lit bytes, _, out => by simp [Act.run]
  | .ifPrefix _ thn els, inp, out => by
    have h1 := Act.length_le_run thn inp out
    have h2 := Act.length_le_run els inp out
    simp only [Act.run]
    split <;> omega
  | .seq first second, inp, out =>
    Nat.le_trans (Act.length_le_run first inp out) (Act.length_le_run second inp _)

/-! ## Compilation

The generated code keeps the output cursor in `pos` and one flag, `m`, for the keyword test;
both are declared once, before the body. A branch decides before its arms run, so the arms may
reuse the flag. Each action is compiled in front of the code that follows it, so a sequence
needs no append. -/

/-- The address `out + pos + off`. -/
def outAt (off : Nat) : PExpr := eAdd (eAdd (v "out") (v "pos")) (n off)

/-- The address `inp + off`. -/
def inpAt (off : Nat) : PExpr := eAdd (v "inp") (n off)

/-- Store `bytes` at `out + pos + off …`, then move `pos` past everything written. -/
def litStmts : Nat → List (BitVec 8) → List PStmt → List PStmt
  | off, [], rest => .assign "pos" (eAdd (v "pos") (n off)) :: rest
  | off, b :: bs, rest => .storeb (outAt off) (n b.toNat) :: litStmts (off + 1) bs rest

/-- `1` when the input holds `keyword` from `inp + off`, `0` otherwise. -/
def matchExpr : Nat → List (BitVec 8) → PExpr
  | _, [] => n 1
  | off, b :: bs => eAnd (eEq (.loadb (inpAt off)) (n b.toNat)) (matchExpr (off + 1) bs)

/-- The code of an action, followed by `rest`. The keyword is compared only when the input
is at least as long, so no byte past the input is read. -/
def Act.compile : Act → List PStmt → List PStmt
  | .lit bytes, rest => litStmts 0 bytes rest
  | .ifPrefix keyword thn els, rest =>
    .assign "m" (n 0) ::
    .ite (eLe (n keyword.length) (v "inlen")) [.assign "m" (matchExpr 0 keyword)] [] ::
    .ite (v "m") (thn.compile []) (els.compile []) :: rest
  | .seq first second, rest => first.compile (second.compile rest)

/-- The value an exported function returns when it refuses its arguments. -/
def refusal : Nat := 2 ^ 32 - 1

/-- An action as a C-callable function `name(inp, inlen, out, cap)`: it refuses negative lengths
and an output buffer smaller than the action can fill, and otherwise returns how many bytes it
wrote at `out`. -/
def respond (name : String) (a : Act) : PFun :=
  { name := name, exported := true,
    params := [(1, "inp"), (1, "inlen"), (1, "out"), (1, "cap")],
    body := Kernels.rejectNegative ["inlen", "cap"] [.ret (n refusal)]
      [.ite (eLt (v "cap") (n a.maxLen)) [.ret (n refusal)]
        ([.dec "pos" (n 0), .dec "m" (n 0)] ++ a.compile [.ret (v "pos")])] }

/-- The source of `respond name a`, for an action the correctness theorems cover: its keywords
fit the signed comparison and its longest reply is below the refusal value, so the length it
returns reaches C whole and cannot be mistaken for a refusal. -/
def emit (name : String) (a : Act) : Except String String :=
  if !a.fitsB then .error "keyword too long for a signed length comparison"
  else if refusal ≤ a.maxLen then .error "reply may not fit the 32-bit result"
  else (Checked.emit (respond name a)).mapError Checked.Reason.message

end DN.Dsl
