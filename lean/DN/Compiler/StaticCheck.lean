-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Syntax

/-!
# DN.Compiler.StaticCheck

CakeML's static checker (`pancake/panStaticScript.sml`) tracks, for every local, whether it is
derived from the base address, and warns about a load or store whose address may not be. A
parameter and a loaded word are `Trusted`, a literal or a comparison `NotBased`, an operation
the strongest of its operands, and a local that the branches of an `if`, or a loop and the code
before it, leave in different states `NotTrusted`. An address holding a `NotTrusted` part draws
the warning. The generated-programs lane fails on every warning, so the generator keeps this
account and builds addresses only from parts that are not `NotTrusted`.

The two pinned revisions differ in one rule: a shift takes the state of the shifted expression
at `ed31510` and that of the distance at `e8eca63`, where a literal distance makes it
`NotBased`. The account is kept for both, and a part counts as trusted only if it is in both.
-/

namespace DN.Compiler.StaticCheck

open DN.Compiler.Syntax

inductive Bd
  | notBased | trusted | notTrusted | based
  deriving DecidableEq

/-- `based_merge`: `Based` over `NotTrusted` over `Trusted` over `NotBased`. -/
def Bd.merge : Bd → Bd → Bd
  | .based, _ | _, .based => .based
  | .notTrusted, _ | _, .notTrusted => .notTrusted
  | .trusted, _ | _, .trusted => .trusted
  | .notBased, .notBased => .notBased

/-- An address in this state draws no warning. -/
def Bd.addressable : Bd → Bool
  | .trusted | .based => true
  | .notBased | .notTrusted => false

/-- The state under the release's rules and under the patched source's. -/
abbrev Bd2 := Bd × Bd

def Bd2.merge (a b : Bd2) : Bd2 := (a.1.merge b.1, a.2.merge b.2)

def Bd2.all (b : Bd) : Bd2 := (b, b)

/-- What the checker makes of an expression, under either revision's rules, given the state of
each local. -/
def bdWith (look : String → Bd2) : PExpr → Bd2
  | .const _ => Bd2.all .notBased
  | .base => Bd2.all .based
  | .var x => look x
  | .binop op l r =>
    if op == .lt || op == .le || op == .eq then Bd2.all .notBased
    else (bdWith look l).merge (bdWith look r)
  | .loadw _ _ | .loadb _ => Bd2.all .trusted
  | .shr l r | .shl l r => ((bdWith look r).1, (bdWith look l).2)

/-! ## The account

One account serves both ends: the generator keeps it as it builds a program, and the reducer's
candidates, which arrive as data, are held to it, so that a candidate CakeML would warn about is
refused before it reaches the compiler. -/

/-- The state of each local in scope, in the order they were declared. -/
abbrev Account := List (String × Bd2)

def Account.bd (acc : Account) (e : PExpr) : Bd2 :=
  bdWith (fun x => (acc.lookup x).getD (Bd2.all .trusted)) e

def Account.addressable (acc : Account) (a : PExpr) : Bool :=
  let b := acc.bd a
  b.1.addressable && b.2.addressable

/-- Every load in `e` is from an address the checker trusts. -/
def Account.loads (acc : Account) : PExpr → Bool
  | .loadw _ a | .loadb a => acc.addressable a && acc.loads a
  | .binop _ l r | .shr l r | .shl l r => acc.loads l && acc.loads r
  | .const _ | .var _ | .base => true

/-- `branch_loc_inf`: after two paths from `before`, a local they leave in different states is
`NotTrusted`. Both accounts start with the locals of `before`. -/
def Account.join (before a b : Account) : Account :=
  before.zipIdx.map fun ((x, bd), k) =>
    match a[k]?, b[k]? with
    | some (_, ba), some (_, bb) =>
      let side (u v : Bd) : Bd := if u == v then u else .notTrusted
      (x, (side ba.1 bb.1, side ba.2 bb.2))
    | _, _ => (x, bd)

mutual
/-- The account after `s`, or nothing if `s` loads from or stores to an address the checker
would warn about. -/
def stmtAccount (acc : Account) : PStmt → Option Account
  | .dec x e => if acc.loads e then some (acc ++ [(x, acc.bd e)]) else none
  | .assign x e =>
    if acc.loads e then some (acc.map fun (y, b) => if y == x then (y, acc.bd e) else (y, b))
    else none
  | .store a e | .storeb a e =>
    if acc.addressable a && acc.loads a && acc.loads e then some acc else none
  | .ret e => if acc.loads e then some acc else none
  | .ite c t f =>
    if !acc.loads c then none else
    match blockAccount acc t, blockAccount acc f with
    | some onTrue, some onFalse => some (Account.join acc onTrue onFalse)
    | _, _ => none
  | .while c b =>
    if !acc.loads c then none else
    match blockAccount acc b with
    | some ab => some (Account.join acc ab acc)
    | none => none
  | .ffi _ args | .call _ _ args => if args.all acc.loads then some acc else none
def blockAccount (acc : Account) : List PStmt → Option Account
  | [] => some acc
  | s :: rest => match stmtAccount acc s with
    | some acc' => blockAccount acc' rest
    | none => none
end

/-- Whether CakeML's checker, under either pinned revision's rules, trusts every address `f`
loads from or stores to. -/
def trustedAddresses (f : PFun) : Bool :=
  (blockAccount (f.params.map fun (_, x) => (x, Bd2.all .trusted)) f.body).isSome

/-! ## Regressions -/

private def loadAfter (body : List PStmt) : PFun :=
  { name := "f", params := [(1, "p")],
    body := [.dec "x" (v "p")] ++ body ++ [.ret (.loadb (v "x"))] }

-- An address from a parameter is trusted; one that the branches of an `if` or a loop may leave
-- from something else is not.
def regression_811 : Bool := trustedAddresses (loadAfter [])
def regression_812 : Bool := !trustedAddresses (loadAfter [.ite (v "p") [.assign "x" (n 8)] []])
def regression_813 : Bool := !trustedAddresses (loadAfter [.while (n 0) [.assign "x" (n 8)]])
-- The revisions disagree on a shift by a literal: the release takes the distance's state, the
-- patched source the shifted expression's, so the address is trusted by one only.
def regression_814 : Bool :=
  bdWith (fun _ => Bd2.all .trusted) (.shr (v "p") (n 3)) == (.notBased, .trusted) &&
    !trustedAddresses
      { name := "f", params := [(1, "p")], body := [.ret (.loadb (.shr (v "p") (n 0)))] }

end DN.Compiler.StaticCheck
