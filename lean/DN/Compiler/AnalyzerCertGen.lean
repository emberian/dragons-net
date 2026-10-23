-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.AnalyzerCert

/-!
# DN.Compiler.AnalyzerCertGen

Certificates for `DN.Compiler.AnalyzerCert`, found as `DN.Compiler.Analyzer` finds invariants, and
printed as Lean modules whose claims the kernel checks one declaration each, a program's dealt to
modules that lake checks side by side. A statement whose analysis costs more than a budget is cut
along its structure; a loop it cuts through gets the invariant the analysis's own search finds. The
cost of an analysis is counted as the kernel pays for it: each statement analyzed, in the search
for every invariant too, weighs as many locals as are in scope. Nothing here is relied on: the
modules it prints are checked.
-/

namespace DN.Compiler.Analyzer.Gen

open DN.Compiler DN.Compiler.Analyzer

/-! ## Cost -/

abbrev W := StateT Nat (Except Alarm)

def lift {α : Type} (x : Except Alarm α) : W α := StateT.lift x

def count (A : AState) : W Unit := modify (· + A.locals.length + 1)

def searchW (size : Nat) (e : PancakeExp) (step : AState → W (Option AState)) :
    Nat → AState → W (AState × Option AState)
  | 0, X => do return (X, ← step X)
  | n + 1, X => do
    match ← step X with
    | none => return (X, none)
    | some Y =>
      if Y.le X then return (X, some Y)
      else
        match X.join Y with
        | none => lift (.error "while: the locals in scope change in the loop")
        | some J =>
          if 2 < n then searchW size e step n (guardWiden size e X J)
          else
            match X.widen J with
            | none => lift (.error "while: the locals in scope change in the loop")
            | some W => searchW size e step n W

def branchW (size : Nat) (e : PancakeExp) (t : Bool) (body : AState → W (Option AState))
    (X : AState) : W (Option AState) :=
  match assume size X e t with
  | none => return none
  | some G => body G

/-- `analyze` with the functions `env` to call, counting what it costs. -/
def analyzeW (size : Nat) (env : Env) (A : AState) : PancakeProg → W (Option AState)
  | .dec x e c => do
    count A
    let v ← lift (valOf size A e s!"var {x}")
    match ← analyzeW size env { locals := (x, v) :: A.locals, cells := killCells x A.cells } c with
    | none => return none
    | some B => return some { locals := dropVar x B.locals, cells := killCells x B.cells }
  | .decCall rt _ _ c => do
    count A
    match ← analyzeW size env { locals := (rt, AVal.top) :: A.locals, cells := [] } c with
    | none => return none
    | some B => return some { locals := dropVar rt B.locals, cells := killCells rt B.cells }
  | .seq c1 c2 => do
    match ← analyzeW size env A c1 with
    | none => return none
    | some B => analyzeW size env B c2
  | .cond e c1 c2 => do
    count A
    let o1 ← branchW size e true (fun X => analyzeW size env X c1) A
    let o2 ← branchW size e false (fun X => analyzeW size env X c2) A
    lift (joinOuts o1 o2)
  | .while_ e c => do
    count A
    let (I, _) ← searchW size e (branchW size e true (fun X => analyzeW size env X c)) searchFuel A
    return assume size I e false
  | p => do
    count A
    lift (analyze size env A p)

def cost (size : Nat) (env : Env) (A : AState) (p : PancakeProg) : Nat :=
  match (analyzeW size env A p).run 0 with
  | .ok (_, k) => k
  | .error _ => 0

/-! ## Certificates -/

/-- `B` as changes to `A`, whose locals it has in the same order. -/
def deltaOf (A B : AState) : Delta :=
  { locals := (A.locals.zip B.locals).filterMap fun ((_, a), (y, b)) =>
      if decide (a = b) then none else some (y, b)
    cells := if decide (A.cells = B.cells) then none else some B.cells }

def leafOf (size : Nat) (env : Env) (A : AState) (p : PancakeProg) : Except Alarm Cert := do
  match ← analyze size env A p with
  | none => .ok (.leaf none)
  | some B =>
    let d := deltaOf A B
    if decide (d.apply A = some B) then .ok (.leaf (some d))
    else .error "a piece's end is not its start changed"

/-- What the certificate claims a statement ends in. -/
def outC (size : Nat) (env : Env) (A : AState) (p : PancakeProg) (k : Cert) :
    Except Alarm (Option AState) :=
  (analyzeC size env A p k).map (·.1)

/-- Whether a statement holds no loop: a piece that does would make its claim search for the
loop's invariant, which the certificate gives instead. -/
def loopFree : PancakeProg → Bool
  | .while_ _ _ => false
  | .dec _ _ c | .decCall _ _ _ c => loopFree c
  | .seq a b | .cond _ a b => loopFree a && loopFree b
  | _ => true

/-- How many of the first statements of the chain `p` fit in `budget` together, from `A`, none of
them a loop. -/
def chainFits (size budget : Nat) (env : Env) (A : AState) (spent : Nat) : PancakeProg → Nat
  | .seq c1 c2 =>
    let c := cost size env A c1
    if budget < spent + c || !loopFree c1 then 0 else
    match analyze size env A c1 with
    | .ok (some B) => 1 + chainFits size budget env B (spent + c) c2
    | _ => 1
  | _ => 0

/-- A certificate for `p` from `A`, with the functions `env` to call, cut at every loop and where a
piece costs more than `budget`, no deeper than `fuel`. -/
def certify (size budget : Nat) (env : Env) : Nat → AState → PancakeProg → Except Alarm Cert
  | 0, A, p => leafOf size env A p
  | fuel + 1, A, p =>
    if cost size env A p ≤ budget && loopFree p then leafOf size env A p else
    match p with
    | .seq c1 c2 => do
      let m := chainFits size budget env A 0 p
      if 2 ≤ m then
        let rest ← (dropChain m p).elim (.error "a chain shorter than counted") .ok
        match ← prefixOut size env m A p with
        | none => return .chain m none (.leaf none)
        | some B =>
          let d := deltaOf A B
          if !decide (d.apply A = some B) then .error "a chain's end is not its start changed"
          else return .chain m (some d) (← certify size budget env fuel B rest)
      let k1 ← certify size budget env fuel A c1
      match ← outC size env A c1 k1 with
      | none => .ok (.seq k1 (.leaf none))
      | some B => .ok (.seq k1 (← certify size budget env fuel B c2))
    | .dec x e c => do
      let v ← valOf size A e s!"var {x}"
      let inner := { locals := (x, v) :: A.locals, cells := killCells x A.cells }
      .ok (.dec (← certify size budget env fuel inner c))
    | .decCall rt _ _ c =>
      return .dec (← certify size budget env fuel
        { locals := (rt, AVal.top) :: A.locals, cells := [] } c)
    | .cond e c1 c2 => do
      let k1 ← match assume size A e true with
        | none => .ok (.leaf none)
        | some G => certify size budget env fuel G c1
      let k2 ← match assume size A e false with
        | none => .ok (.leaf none)
        | some G => certify size budget env fuel G c2
      .ok (.cond k1 k2)
    | .while_ e c => do
      let (I, _) ← search size e (branch size e true (fun X => analyze size env X c)) searchFuel A
      let d := deltaOf A I
      if !decide (d.apply A = some I) then .error "while: the invariant is not its entry changed"
      else
        let k ← match assume size I e true with
          | none => .ok (.leaf none)
          | some G => certify size budget env fuel G c
        .ok (.loop d k)
    | p => leafOf size env A p

/-- The statements of a program, compound ones too. -/
def nodes : PancakeProg → Nat
  | .dec _ _ c | .while_ _ c | .decCall _ _ _ c => nodes c + 1
  | .seq a b | .cond _ a b => nodes a + nodes b + 1
  | _ => 1

/-- What checking a claim costs. -/
def claimCost (size : Nat) (ob : Ob) : Nat :=
  if ob.n = 0 then cost size ob.env ob.A ob.p
  else ((List.range ob.n).foldl (init := (0, ob.A, ob.p)) fun (acc, A, q) _ =>
    match q with
    | .seq c1 c2 => (acc + cost size ob.env A c1,
        match analyze size ob.env A c1 with | .ok (some B) => B | _ => A, c2)
    | _ => (acc, A, q)).1

/-- A certificate for a whole `main`, and how many claims it makes; the cuts nest no deeper than
the program does. -/
def certifyMain (size budget : Nat) (p : PancakeProg) : Except Alarm (Cert × Nat) := do
  let k ← certify size budget [] (nodes p) ⟨[], []⟩ p
  let obs ← checkC size p k
  .ok (k, obs.length)

/-- Certificates for a program's functions, each from any arguments with those before it to call,
and for its `main`: the functions with theirs, `main`'s, and how many claims each makes. -/
def certifyProgram (size budget : Nat) (fns : List (String × List String × PancakeProg))
    (p : PancakeProg) : Except Alarm (List FnC × Cert × List Nat) := do
  let (env, cs) ← fns.foldlM (init := (([] : Env), ([] : List FnC)))
    fun (env, cs) (f, ps, body) => do
      let k ← certify size budget env (nodes body) (entryState ps) body
      .ok ((f, ps) :: env, cs ++ [(f, ps, body, k)])
  need (fnsOk size [] cs) "a function its certificate does not accept"
  let k ← certify size budget env (nodes p) ⟨[], []⟩ p
  let obs ← checkC size p k env
  .ok (cs, k, (List.range cs.length).map (fnClaims size [] cs · |>.length) ++ [obs.length])

/-! ## Printing -/

def ppInt (i : Int) : String :=
  if i = wordMin then "wordMin" else if i = wordMax then "wordMax"
  else if i < 0 then s!"({i})" else toString i

def ppAVal (v : AVal) : String :=
  let res := match v.res with | none => "none" | some r => s!"(some {r})"
  s!"AVal.mk {v.ptr} {ppInt v.lo} {ppInt v.hi} {res}"

def ppLocal : String × AVal → String
  | (x, v) => s!"(\"{x}\", {ppAVal v})"

def ppCell : String × Int × AVal → String
  | (x, k, v) => s!"(\"{x}\", {ppInt k}, {ppAVal v})"

def trimEnd (s : String) : String := String.ofList (s.toList.reverse.dropWhile (· == ' ')).reverse

/-- `head`, then the elements of a list, then `tail`: on one line at `ind` spaces if it fits in
100 columns, else an element a line. -/
def ppList (ind head tail : String) (xs : List String) : List String :=
  let one := ind ++ head ++ "[" ++ ", ".intercalate xs ++ "]" ++ tail
  if one.length ≤ 100 || xs.isEmpty then [one]
  else [ind ++ trimEnd head] ++ xs.mapIdx fun i x =>
    ind ++ (if i = 0 then "    [" else "     ") ++ x ++
      (if i + 1 = xs.length then "]" ++ tail else ",")

/-- A delta, opened by `head` and closed by `tail`. -/
def ppDelta (ind head tail : String) (d : Delta) : List String :=
  match d.cells with
  | none => ppList ind (head ++ "{ locals := ") (", cells := none }" ++ tail) (d.locals.map ppLocal)
  | some cs =>
    -- a field on a line of its own starts where the first one does
    let col := String.ofList (List.replicate (ind ++ head ++ "{ ").length ' ')
    ppList ind (head ++ "{ locals := ") "" (d.locals.map ppLocal) ++
      ppList col "cells := some " (" }" ++ tail) (cs.map ppCell)

/-- Lines closed by a parenthesis, on the last if it fits in 100 columns. -/
def closed (ind : String) (ls : List String) : List String :=
  match ls.getLast? with
  | some l => if l.length < 100 then ls.dropLast ++ [l ++ ")"] else ls ++ [ind ++ ")"]
  | none => [ind ++ ")"]

/-- A certificate, a part a line at `ind` spaces however deep: the nesting is in the
parentheses. -/
def ppCert (ind : String) : Cert → List String
  | .leaf none => [ind ++ "(.leaf none)"]
  | .leaf (some d) => ppDelta ind "(.leaf (some " "))" d
  | .chain n none a => closed ind ([ind ++ s!"(.chain {n} none"] ++ ppCert ind a)
  | .chain n (some d) a => closed ind (ppDelta ind s!"(.chain {n} (some " ")" d ++ ppCert ind a)
  | .seq a b => closed ind ([ind ++ "(.seq"] ++ ppCert ind a ++ ppCert ind b)
  | .dec a => closed ind ([ind ++ "(.dec"] ++ ppCert ind a)
  | .cond a b => closed ind ([ind ++ "(.cond"] ++ ppCert ind a ++ ppCert ind b)
  | .loop d a => closed ind (ppDelta ind "(.loop " "" d ++ ppCert ind a)

/-- What a module of claims is about: its name, what it says, the module that has the program and
the heap's size, and the names of both. -/
structure Target where
  module : String
  doc : String
  imports : List String
  program : String
  size : String

/-- Consecutive runs, from the first, of the items of these costs: each run's costs together no
more than `budget`, or a single item that costs more; as starts and lengths. -/
def runs (budget : Nat) (costs : List Nat) : List (Nat × Nat) :=
  let close (acc : List (Nat × Nat)) (a n : Nat) := if n = 0 then acc else acc ++ [(a, n)]
  let (acc, a, n, _) := costs.zipIdx.foldl (init := (([] : List (Nat × Nat)), 0, 0, 0))
    fun (acc, a, n, spent) (w, i) =>
      if 0 < n && budget < spent + w then (close acc a n, i, 1, w) else (acc, a, n + 1, spent + w)
  close acc a n

/-- Claims `rs` of the list `l`, each run a declaration `{name}_{a}`. -/
def claimChecks (name l : String) (rs : List (Nat × Nat)) : List (List String) :=
  rs.map fun (a, m) =>
    [s!"theorem {name}_{a} :",
     s!"    (List.range' {a} {m}).all (fun j => (({l}).getD j default).ok size) = true := by",
     "  decide +kernel", ""]

/-- From the declarations of `claimChecks`, `name`: that each claim of `l` holds, the number of
claims by the theorem `count`. -/
def claimsJoined (name l count : String) (rs : List (Nat × Nat)) : List String :=
  [s!"theorem {name} : ∀ j, j < ({l}).length → (({l}).getD j default).ok size = true := by",
   "  intro j hj",
   s!"  rw [{count}] at hj"] ++
  (rs.flatMap fun (a, m) =>
    [s!"  by_cases h{a} : j < {a + m}",
     s!"  · exact all_range {name}_{a} j (by omega) (by omega)"]) ++
  ["  exact absurd hj (by omega)", ""]

/-- Claims `rs` of the list `l` by declarations `{name}_{a}`, and from them `name`, that each holds,
the number of claims by the theorem `count`. -/
def claimRuns (name l count : String) (rs : List (Nat × Nat)) : List String :=
  (claimChecks name l rs).flatten ++ claimsJoined name l count rs

/-- That the certificate `checkE` checks fits `main` and makes `n` claims `l`. -/
def mainChecked (l checkE : String) (n : Nat) : List String :=
  ["/-- The certificate fits `main`, and how many claims it makes. -/",
   "theorem checked :",
   s!"    (({checkE}).toBool && ({l}).length == {n}) = true := by",
   "  decide +kernel", ""]

/-- Each half of `checked`. -/
def mainCounted (l checkE : String) (n : Nat) : List String :=
  [s!"theorem accepted : ({checkE}).toBool = true := by",
   "  have h := checked", "  simp only [Bool.and_eq_true] at h", "  exact h.1", "",
   s!"theorem count : ({l}).length = {n} := by",
   "  have h := checked", "  simp only [Bool.and_eq_true, beq_iff_eq] at h", "  exact h.2", ""]

/-- The theorems on `main`'s claims `l`: the certificate fits, how many claims it makes, and each
holds, in runs of at most `budget`. -/
def mainLines (l checkE : String) (n : Nat) (rs : List (Nat × Nat)) : List String :=
  mainChecked l checkE n ++ mainCounted l checkE n ++ claimRuns "claims_ok" l "count" rs

/-- A generated module: what it imports and says, and its declarations in the namespace `ns`. -/
def moduleText (module ns doc : String) (imports body : List String) : String :=
  "\n".intercalate (["-- SPDX-License-Identifier: AGPL-3.0-or-later",
     "-- Generated by `dn-compiler analysis-cert`; a test checks it is current."] ++
    imports.map (s!"import {·}") ++
    ["", "/-!", s!"# {module}", "", doc, "-/", "", s!"namespace {ns}", "",
     "open DN.Compiler DN.Compiler.Analyzer", ""] ++ body ++ [s!"end {ns}"]) ++ "\n"

/-- The module: the certificate, and its claims in declarations of at most `budget` each, as
`claimCost` counts. -/
def render (t : Target) (size budget : Nat) (p : PancakeProg) (k : Cert) : String :=
  let obs := claims size p k
  moduleText t.module t.module t.doc (t.imports ++ ["DN.Compiler.AnalyzerCert"])
    ([s!"def size : Nat := {t.size}", "",
      s!"theorem lowers : (Lower.lower {t.program}).isSome = true := by decide +kernel", "",
      "/-- The program, as it lowers. -/",
      s!"def mainP : PancakeProg := (Lower.lower {t.program}).get lowers", "",
      s!"theorem lower_main : Lower.lower {t.program} = some mainP :=",
      "  (Option.some_get lowers).symm", "",
      "/-- Where the analysis is cut, and what each piece ends in. -/",
      "def cert : Cert :="] ++ ppCert "  " k ++ [""] ++
     mainLines "claims size mainP cert" "checkC size mainP cert" obs.length
       (runs budget (obs.map (claimCost size))))

/-- What a module of a program's claims is about: as `Target`, with the names of its functions and
of its `main`. -/
structure ProgramTarget where
  module : String
  doc : String
  imports : List String
  functions : String
  program : String
  size : String

/-- How the claims of a program's functions are checked: a run of `n` functions from `a`, whose
claims together cost no more than the budget, in one declaration; or the claims of function `i`,
which cost more, in runs of their own. -/
inductive Piece
  | group (a n : Nat)
  | alone (i c : Nat) (rs : List (Nat × Nat))

/-- What a statement of a function a declaration checks weighs besides its claims: the kernel
checks its certificate's parts along the function's body, which costs about as much memory as a
claim of this cost does. -/
def nodeWeight : Nat := 20

/-! ## Programs, written out -/

/-- An operator, as a constructor's name. -/
def ppBinop : Binop → String
  | .add => ".add" | .and_ => ".and_" | .sub => ".sub" | .xor => ".xor" | .or_ => ".or_"

/-- A comparison, as a constructor's name. -/
def ppCmp : Cmp → String
  | .less => ".less" | .equal => ".equal" | .notLess => ".notLess"

/-- An expression, on one line. -/
def ppExp : PancakeExp → String
  | .const w => s!"(.const {w.toNat})"
  | .var x => s!"(.var {x.quote})"
  | .base => ".base"
  | .op b l r => s!"(.op {ppBinop b} {ppExp l} {ppExp r})"
  | .mul l r => s!"(.mul {ppExp l} {ppExp r})"
  | .cmp c l r => s!"(.cmp {ppCmp c} {ppExp l} {ppExp r})"
  | .loadByte a => s!"(.loadByte {ppExp a})"
  | .loadWord a => s!"(.loadWord {ppExp a})"
  | .shiftR l r => s!"(.shiftR {ppExp l} {ppExp r})"
  | .shiftL l r => s!"(.shiftL {ppExp l} {ppExp r})"

/-- How deep a written program nests before a part of it is written as a definition of its own:
the elaborator, the gate and nanoda recurse along the nesting, nanoda on a small stack. The
certificates nest up to about 150 deep and pass all three; the bodies, which nest far deeper, are
kept well below that. -/
def cutDepth : Nat := 64

/-- The lines of a part of a program, and how deep they nest; how many parts are cut off so far,
and the definitions written for them. -/
abbrev Written := StateM (Nat × List String) (List String × Nat)

/-- A part of a program whose lines nest `d` deep inside it: written in place, or, nesting
`cutDepth` deep, as the definition `{name}_{k}` named in its place. -/
def cutOff (name : String) (ls : List String) (d : Nat) : Written := do
  if d < cutDepth then return (ls, d)
  let (k, defs) ← get
  set (k + 1, defs ++ [s!"def {name}_{k} : PancakeProg :="] ++ ls ++ [""])
  return ([s!"  {name}_{k}"], 1)

/-- The program, a statement a line at two spaces however deep, the nesting in the parentheses;
the parts cut off are named `{name}_{k}`. -/
def ppProg (name : String) : PancakeProg → Written
  | .skip => return (["  .skip"], 1)
  | .assign v e => return ([s!"  (.assign {v.quote} {ppExp e})"], 1)
  | .store d e => return ([s!"  (.store {ppExp d} {ppExp e})"], 1)
  | .storeByte d e => return ([s!"  (.storeByte {ppExp d} {ppExp e})"], 1)
  | .extCall f a b c d =>
    return ([s!"  (.extCall {f.quote} {ppExp a} {ppExp b} {ppExp c} {ppExp d})"], 1)
  | .ret e => return ([s!"  (.ret {ppExp e})"], 1)
  | .dec v e c => do
    let (ls, d) ← ppProg name c
    cutOff name (closed "  " ([s!"  (.dec {v.quote} {ppExp e}"] ++ ls)) (d + 1)
  | .while_ e c => do
    let (ls, d) ← ppProg name c
    cutOff name (closed "  " ([s!"  (.while_ {ppExp e}"] ++ ls)) (d + 1)
  | .decCall rt f args c => do
    let (ls, d) ← ppProg name c
    cutOff name (closed "  "
      ([s!"  (.decCall {rt.quote} {f.quote} [{", ".intercalate (args.map ppExp)}]"] ++ ls)) (d + 1)
  | .seq a b => do
    let (la, da) ← ppProg name a
    let (lb, db) ← ppProg name b
    cutOff name (closed "  " (["  (.seq"] ++ la ++ lb)) (max da db + 1)
  | .cond e a b => do
    let (la, da) ← ppProg name a
    let (lb, db) ← ppProg name b
    cutOff name (closed "  " ([s!"  (.cond {ppExp e}"] ++ la ++ lb)) (max da db + 1)

/-- The definition `name` of the program `p`, after those of the parts cut off it. -/
def ppProgDef (name : String) (p : PancakeProg) : List String :=
  let ((ls, _), (_, defs)) := (ppProg name p).run (0, [])
  defs ++ [s!"def {name} : PancakeProg :="] ++ ls ++ [""]

/-- How many functions' lowerings one declaration holds to those written out: each declaration
first computes the program's functions from its source, about 4 s of the kernel's, and twenty
lowerings take it up to about 6 GB. -/
def lowerRun : Nat := 20

/-- How many modules a program's declarations the kernel checks by evaluation are dealt to: lake
checks modules side by side, the declarations of one one after another, each up to about 6 GB of
the kernel's evaluation (the lowering of one function alone takes up to 4.4); two at a time took
10.6 GB here, where a CI runner has 16. -/
def checkModules : Nat := 2

/-- `xs` dealt in turn into `k` lists: what a declaration costs the kernel is not known before. -/
def deal {α : Type} (k : Nat) (xs : List α) : List (List α) :=
  (List.range k).map fun r => (xs.zipIdx.filter (·.2 % k == r)).map (·.1)

/-- The modules of a program, by name: `{module}.Certs`, its functions and its `main` written out as
they lower, with their certificates; the declarations the kernel checks by evaluation — that they
are the program's as it lowers, `lowerRun` functions at a time, and the claims of its functions and
of its `main` in declarations of at most `budget` each as `claimCost` and `nodeWeight` count —
dealt in turn to the `checkModules` modules `{module}.Checks{r}`; and `module`, what follows from
them. -/
def renderProgram (t : ProgramTarget) (size budget : Nat) (cs : List FnC) (p : PancakeProg)
    (k : Cert) : List (String × String) :=
  let env := envAfter [] cs
  let fnObs := (List.range cs.length).map (fnClaims size [] cs ·)
  let costsOf (obs : List Ob) := obs.map (claimCost size)
  let fnCost := (fnObs.zip cs).map fun (obs, (_, _, body, _)) =>
    (costsOf obs).sum + nodeWeight * nodes body
  let mainObs := claims size p k env
  let ps : List Piece := (runs budget fnCost).map fun (a, m) =>
    if m = 1 && budget < fnCost.getD a 0 then
      let obs := fnObs.getD a []
      .alone a obs.length (runs budget (costsOf obs))
    else .group a m
  let fnClaimsAt (i : Nat) : String := s!"fnClaims size [] fnsC {i}"
  -- A piece's declarations the kernel checks by evaluation, and what follows from them.
  let piece : Piece → List (List String) × List String
    | .group a m =>
      ([[s!"theorem group_{a} :",
         s!"    (List.range' {a} {m}).all (fun i => fnOkAt size [] fnsC i &&",
         "      (fnClaims size [] fnsC i).all (·.ok size)) = true := by",
         "  decide +kernel", ""]], [])
    | .alone i c rs =>
      ([s!"theorem fn_{i}_checked :",
        s!"    (fnOkAt size [] fnsC {i} && ({fnClaimsAt i}).length == {c}) = true := by",
        "  decide +kernel", ""] :: claimChecks s!"fn_{i}" (fnClaimsAt i) rs,
       [s!"theorem fn_{i}_count : ({fnClaimsAt i}).length = {c} := by",
        s!"  have h := fn_{i}_checked", "  simp only [Bool.and_eq_true, beq_iff_eq] at h",
        "  exact h.2", ""] ++
       claimsJoined s!"fn_{i}" (fnClaimsAt i) s!"fn_{i}_count" rs)
  let dispatch : Piece → List String
    | .group a m =>
      [s!"  by_cases h{a} : i < {a + m}",
       s!"  · exact fnChecks_range group_{a} i (by omega) (by omega)"]
    | .alone i _ _ =>
      [s!"  by_cases h{i} : i < {i + 1}",
       s!"  · obtain rfl : i = {i} := by omega",
       s!"    have h := fn_{i}_checked",
       "    simp only [Bool.and_eq_true] at h",
       s!"    exact ⟨h.1, obsOk_of_get fn_{i}⟩"]
  let lowerings := (List.range ((cs.length + lowerRun - 1) / lowerRun)).map fun r =>
    (r * lowerRun, min lowerRun (cs.length - r * lowerRun))
  let lowered (a m : Nat) : List String :=
    [s!"theorem lowered_{a} :",
     s!"    (List.range' {a} {m}).all (fun i => decide ((fnsC[i]?).map (fun g => (g.1, g.2.1, g.2.2.1)) =",
     s!"      ({t.functions}[i]?).map lowerFn)) = true := by",
     "  decide +kernel", ""]
  let mainClaims := "claims size mainP cert (envAfter [] fnsC)"
  let checkE := "checkC size mainP cert (envAfter [] fnsC)"
  let mainRuns := runs budget (costsOf mainObs)
  let checks : List (List String) :=
    [[s!"theorem functions_count : {t.functions}.length = {cs.length} := by decide +kernel", ""],
     [s!"theorem fns_count : fnsC.length = {cs.length} := by decide +kernel", ""],
     ["/-- `mainP` is the program's `main` as it lowers. -/",
      s!"theorem lower_main : Lower.lower {t.program} = some mainP := by decide +kernel", ""]] ++
    lowerings.map (fun (a, m) => lowered a m) ++
    ps.flatMap (piece · |>.1) ++ [mainChecked mainClaims checkE mainObs.length] ++
    claimChecks "claims_ok" mainClaims mainRuns
  let dealt := deal checkModules checks
  let certs := s!"{t.module}.Certs"
  let shares := (List.range dealt.length).map (s!"{t.module}.Checks{·}")
  (certs, moduleText certs t.module
    (s!"The program of `{t.module}` written out as it lowers, its functions and its `main`, and\n" ++
      "their certificates.")
    (t.imports ++ ["DN.Compiler.AnalyzerCertSound"])
    ([s!"def size : Nat := {t.size}", "",
      "/-- A function as it lowers. -/",
      "def lowerFn (g : Syntax.PFun) : String × List String × PancakeProg :=",
      "  (g.name, g.params.map (·.2), (Lower.lower g).getD .skip)", ""] ++
     (cs.zipIdx.flatMap fun ((_, _, body, _), i) => ppProgDef s!"body_{i}" body) ++
     ppProgDef "mainP" p ++
     (cs.zipIdx.flatMap fun ((_, _, _, c), i) =>
       [s!"def cert_{i} : Cert :="] ++ ppCert "  " c ++ [""]) ++
     ["/-- The functions with their certificates. -/"] ++
     ppList "" "def fnsC : List FnC := " ""
       (cs.zipIdx.map fun ((f, ps, _, _), i) =>
         s!"({f.quote}, [{", ".intercalate (ps.map String.quote)}], body_{i}, cert_{i})") ++
     ["", "/-- Where the analysis of `main` is cut, and what each piece ends in. -/",
      "def cert : Cert :="] ++ ppCert "  " k ++ [""])) ::
  (shares.zip dealt).map (fun (m, ds) => (m, moduleText m t.module
    s!"A share of the claims of `{t.module}` the kernel checks by evaluation: lake checks the\nshares side by side."
    [certs] ds.flatten)) ++
  [(t.module, moduleText t.module t.module t.doc shares
    (["/-- `fnsC` is the program's functions as they lower. -/",
      "theorem fnsC_lowers :",
      s!"    fnsC.map (fun g => (g.1, g.2.1, g.2.2.1)) = {t.functions}.map lowerFn :=",
      "  map_eq_of_places (by rw [fns_count, functions_count]) fun i hi => by",
      "    rw [fns_count] at hi"] ++
     (lowerings.flatMap fun (a, m) =>
       [s!"    by_cases h{a} : i < {a + m}",
        s!"    · exact of_decide_eq_true (all_range lowered_{a} i (by omega) (by omega))"]) ++
     ["    exact absurd hi (by omega)", ""] ++
     ps.flatMap (piece · |>.2) ++
     ["/-- Each function's certificate fits it, and its claims hold. -/",
      "theorem fns_each :",
      "    ∀ i, i < fnsC.length →",
      "      fnOkAt size [] fnsC i = true ∧ ObsOk size (fnClaims size [] fnsC i) := by",
      "  intro i hi", "  rw [fns_count] at hi"] ++ ps.flatMap dispatch ++
     ["  exact absurd hi (by omega)", "",
      "theorem fns_ok : fnsOk size [] fnsC = true :=",
      "  fnsOk_of_each fun i hi => (fns_each i hi).1", "",
      "theorem fns_claims : ∀ i, i < fnsC.length → ObsOk size (fnClaims size [] fnsC i) :=",
      "  fun i hi => (fns_each i hi).2", ""] ++
     mainCounted mainClaims checkE mainObs.length ++ claimsJoined "claims_ok" mainClaims "count" mainRuns))]

/-! ## Examples, in a heap of 64 bytes above its header -/

open DN.Compiler.PancakeExp (c)

private def heap : Nat := floor + 64

/-- `i` counted from 0 to 8, a byte stored at each, then two nested loops over four rows of
eight. -/
private def loops : PancakeProg :=
  .dec "i" (c 0) (.seq (.while_ (.cmp .less (.var "i") (c 8))
      (.seq (.storeByte (.op .add (.op .add .base (c floor)) (.var "i")) (c 0))
        (.assign "i" (.op .add (.var "i") (c 1)))))
    (.seq (.assign "i" (c 0)) (.seq (.while_ (.cmp .less (.var "i") (c 4))
      (.dec "j" (c 0) (.seq (.while_ (.cmp .less (.var "j") (c 8))
          (.seq (.storeByte (.op .add (.op .add (.op .add .base (c floor)) (.mul (.var "i") (c 8)))
              (.var "j")) (c 0))
            (.assign "j" (.op .add (.var "j") (c 1)))))
        (.assign "i" (.op .add (.var "i") (c 1))))))
    (.ret (c 0)))))

/-- `i` counted from 0 to 8. -/
private def counter : PancakeProg :=
  .dec "i" (c 0)
    (.seq (.while_ (.cmp .less (.var "i") (c 8)) (.assign "i" (.op .add (.var "i") (c 1))))
      (.ret (c 0)))

/-- A certificate of `counter` with the invariant `[0, hi]` and the body claimed to end in
`[1, out]`. -/
private def counterCert (hi out : Int) : Cert :=
  .dec (.seq (.loop { locals := [("i", AVal.mk false 0 hi none)] }
    (.leaf (some { locals := [("i", AVal.mk false 1 out none)] }))) (.leaf none))

/-- A certificate found with every piece cut as small as it goes fits, and each claim holds. -/
def regression_946 (_ : Unit) : Bool :=
  match certifyMain heap 0 loops with
  | .ok (k, n) => (checkC heap loops k).toBool && 3 < n && (claims heap loops k).all (·.ok heap)
  | .error _ => false

/-- An invariant the body is claimed to leave is refused. -/
def regression_947 (_ : Unit) : Bool := !(checkC heap counter (counterCert 7 8)).toBool

/-- A claim the analysis does not give fits the certificate, and fails its own check. -/
def regression_948 (_ : Unit) : Bool :=
  (checkC heap counter (counterCert 8 7)).toBool &&
    !(claims heap counter (counterCert 8 7)).all (·.ok heap)

/-- A byte stored at `k` of the heap above its header, `k` checked first to lie in 64 bytes. -/
private def put : PancakeProg :=
  .seq (.cond (.cmp .less (c 0) (.op .add (.cmp .less (.var "k") (c 0))
      (.cmp .less (c 63) (.var "k")))) (.ret (c 1)) .skip)
    (.seq (.storeByte (.op .add (.op .add .base (c floor)) (.var "k")) (c 0)) (.ret (c 0)))

/-- `put` called for each `i` below 8, then `twice`, which calls `put` twice. -/
private def caller : PancakeProg :=
  .dec "i" (c 0) (.seq (.while_ (.cmp .less (.var "i") (c 8))
      (.decCall "r" "put" [.var "i"] (.assign "i" (.op .add (.var "i") (c 1)))))
    (.decCall "r" "twice" [c 3] (.ret (.var "r"))))

private def callees : List (String × List String × PancakeProg) :=
  [("put", ["k"], put), ("twice", ["k"], .decCall "a" "put" [.var "k"]
      (.decCall "b" "put" [.op .add (.var "k") (c 1)] (.ret (.var "b"))))]

/-- Certificates found for a program with functions, cut as small as they go, fit it, and each
claim of each function and of `main` holds. -/
def regression_962 (_ : Unit) : Bool :=
  match certifyProgram heap 0 callees caller with
  | .ok (fs, k, ns) =>
    1 < ns.headD 0 && (List.range fs.length).all (fun i => (fnClaims heap [] fs i).all (·.ok heap)) &&
      (claims heap caller k (envAfter [] fs)).all (·.ok heap)
  | .error _ => false

/-- A call of a function not before it, a function defined twice and one named as the entry are
refused; a function claimed to finish only with a result when it may not fits its certificate, and
its claim fails its own check. -/
def regression_963 (_ : Unit) : Bool :=
  let leaf : Cert := .leaf none
  let fs : List FnC := [("f", [], .skip, leaf)]
  let ret : PancakeProg := .ret (c 0)
  !(checkC heap (.decCall "r" "f" [] (.ret (.var "r"))) (.dec leaf) [("put", ["k"])]).toBool &&
    !fnsOk heap [] [("f", [], ret, leaf), ("f", [], ret, leaf)] &&
    !fnsOk heap [] [("main", [], ret, leaf)] &&
    fnsOk heap [] fs && !(fnClaims heap [] fs 0).all (·.ok heap)

end DN.Compiler.Analyzer.Gen
