-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Analyzer

/-!
# DN.Compiler.AnalyzerCert

The analysis of `DN.Compiler.Analyzer` in pieces, so that the kernel can check a large program in
several declarations, each with caches of its own: within one declaration the kernel keeps every
step of the reduction it makes, and its memory grows with the program. A certificate cuts the
program along its structure. A piece (`Cert.leaf`) is claimed to end in the state the certificate
gives as changes to the one it starts in; a loop the certificate cuts through takes the invariant
it gives, checked as `analyze` checks the one it finds. `analyzeC` runs a certificate without
analyzing its pieces and lists what it claims of each; `DN.Compiler.AnalyzerCertSound` proves that
when each claim holds — `analyze` gives it, each in a declaration of its own — the program is as
safe as `analyze_safe` makes it. A certificate is found as `analyze` finds invariants
(`dn-compiler analysis-cert`); only the checks are relied on.
-/

namespace DN.Compiler.Analyzer

open DN.Compiler

/-- A state given by its changes to another: new ranges of locals in scope, and the cells, if not
those of the other. -/
structure Delta where
  locals : List (String × AVal) := []
  cells : Option (List (String × Int × AVal)) := none

/-- The locals `ls` with the ranges `ds` gives, named in the order they are in scope: one pass,
since the kernel pays for each step; nothing if `ds` names a local not in scope, or out of order. -/
def mergeLocals : List (String × AVal) → List (String × AVal) → Option (List (String × AVal))
  | ls, [] => some ls
  | [], _ :: _ => none
  | (x, a) :: ls, (y, b) :: ds =>
    if x = y then ((x, b) :: ·) <$> mergeLocals ls ds
    else ((x, a) :: ·) <$> mergeLocals ls ((y, b) :: ds)

/-- `A` changed by `d`, or nothing if `d` names a local not in scope. -/
def Delta.apply (A : AState) (d : Delta) : Option AState :=
  (mergeLocals A.locals d.locals).map fun ls => ⟨ls, d.cells.getD A.cells⟩

/-- The analysis of the first `n` statements of a chain `seq c1 (seq c2 …)`. -/
def prefixOut (size : Nat) : Nat → AState → PancakeProg → Except Alarm (Option AState)
  | 0, A, _ => .ok (some A)
  | n + 1, A, .seq c1 c2 => do
    match ← analyze size A c1 with
    | none => .ok none
    | some B => prefixOut size n B c2
  | _ + 1, _, _ => .error "a chain shorter than the certificate's"

/-- The chain without its first `n` statements. -/
def dropChain : Nat → PancakeProg → Option PancakeProg
  | 0, p => some p
  | n + 1, .seq _ c2 => dropChain n c2
  | _ + 1, _ => none

/-- Where the analysis of a statement is cut: a piece, with the state it ends in if it can; the
first `n` statements of a chain as one piece, and the rest; or the statement's parts, a loop with
its invariant. -/
inductive Cert
  | leaf (out : Option Delta)
  | chain (n : Nat) (out : Option Delta) (rest : Cert)
  | seq (c1 c2 : Cert)
  | dec (inner : Cert)
  | cond (c1 c2 : Cert)
  | loop (inv : Delta) (body : Cert)

/-- What a certificate claims of a piece: its analysis from `A` gives `out` — of all of `p`, or of
the first `n` statements of its chain when `n` is not zero. -/
structure Ob where
  A : AState
  p : PancakeProg
  n : Nat
  out : Option AState

instance : Inhabited Ob := ⟨⟨⟨[], []⟩, .skip, 0, none⟩⟩

/-- The analysis a claim is about. -/
def Ob.run (size : Nat) (ob : Ob) : Except Alarm (Option AState) :=
  if ob.n = 0 then analyze size ob.A ob.p else prefixOut size ob.n ob.A ob.p

/-- The claims hold. -/
def ObsOk (size : Nat) (obs : List Ob) : Prop := ∀ ob ∈ obs, ob.run size = .ok ob.out

/-- The claim holds. -/
def Ob.ok (size : Nat) (ob : Ob) : Bool :=
  match ob.run size with
  | .ok out => decide (out = ob.out)
  | .error _ => false

abbrev OutC := Except Alarm (Option AState × List Ob)

/-- A branch's outcome from the states `X` stands for in which `e` is nonzero (`t`) or zero. -/
def branchC (size : Nat) (e : PancakeExp) (t : Bool) (body : AState → OutC) (X : AState) : OutC :=
  match assume size X e t with
  | none => .ok (none, [])
  | some G => body G

/-- The first `n` statements of the chain `p` as one piece from `A`, and the rest from where they
end, by `rest`. -/
def chainC (A : AState) (p : PancakeProg) (n : Nat) (out : Option Delta)
    (rest : AState → PancakeProg → OutC) : OutC :=
  if n = 0 then .error "a chain of no statements" else
  match dropChain n p, out with
  | none, _ => .error "a chain shorter than the certificate's"
  | some _, none => .ok (none, [⟨A, p, n, none⟩])
  | some q, some d =>
    match d.apply A with
    | none => .error "a piece's end names a local not in scope"
    | some B =>
      match rest B q with
      | .error m => .error m
      | .ok (out, obs) => .ok (out, ⟨A, p, n, some B⟩ :: obs)

/-- The outcome of a statement from `A` by certificate `k`, and the claims it rests on. -/
def analyzeC (size : Nat) (A : AState) : PancakeProg → Cert → OutC
  | p, .leaf none => .ok (none, [⟨A, p, 0, none⟩])
  | p, .leaf (some d) =>
    match d.apply A with
    | some B => .ok (some B, [⟨A, p, 0, some B⟩])
    | none => .error "a piece's end names a local not in scope"
  | p, .chain n out k => chainC A p n out (fun B q => analyzeC size B q k)
  | .dec x e c, .dec k => do
    let v ← valOf size A e s!"var {x}"
    match ← analyzeC size { locals := (x, v) :: A.locals, cells := killCells x A.cells } c k with
    | (none, obs) => .ok (none, obs)
    | (some B, obs) =>
      let ls := dropVar x B.locals
      need (lookup x ls).isNone s!"var {x}: a local declared again inside its own scope"
      .ok (some { locals := ls, cells := killCells x B.cells }, obs)
  | .seq c1 c2, .seq k1 k2 => do
    match ← analyzeC size A c1 k1 with
    | (none, obs) => .ok (none, obs)
    | (some B, obs1) =>
      let (out, obs2) ← analyzeC size B c2 k2
      .ok (out, obs1 ++ obs2)
  | .cond e c1 c2, .cond k1 k2 => do
    let _ ← valOf size A e "if"
    let (o1, obs1) ← branchC size e true (fun X => analyzeC size X c1 k1) A
    let (o2, obs2) ← branchC size e false (fun X => analyzeC size X c2 k2) A
    let out ← joinOuts o1 o2
    .ok (out, obs1 ++ obs2)
  | .while_ e c, .loop d k => do
    let I ← (d.apply A).elim (.error "while: the invariant names a local not in scope") .ok
    need (A.le I) "while: the invariant given does not hold on entry"
    let _ ← valOf size I e "while"
    let (post, obs) ← branchC size e true (fun X => analyzeC size X c k) I
    need (leOpt post I) "while: the invariant given is not kept"
    .ok (assume size I e false, obs)
  | _, _ => .error "the certificate does not fit the program"

/-- The analysis of a whole `main` by a certificate: the claims, if no run finishes normally. -/
def checkC (size : Nat) (p : PancakeProg) (k : Cert) : Except Alarm (List Ob) :=
  match analyzeC size ⟨[], []⟩ p k with
  | .ok (none, obs) => .ok obs
  | .ok (some _, _) => .error "main: a run may finish without a result"
  | .error m => .error m

/-- The claims of an accepted certificate, none otherwise. -/
def claims (size : Nat) (p : PancakeProg) (k : Cert) : List Ob :=
  match checkC size p k with
  | .ok obs => obs
  | .error _ => []

end DN.Compiler.Analyzer
