-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.AnalyzerCert

/-!
# DN.Compiler.AnalyzerCertGen

Certificates for `DN.Compiler.AnalyzerCert`, found as `DN.Compiler.Analyzer` finds invariants, and
printed as a Lean module whose claims the kernel checks one declaration each. A statement whose
analysis costs more than a budget is cut along its structure; a loop it cuts through gets the
invariant the analysis's own search finds. The cost of an analysis is counted as the kernel pays
for it: each statement analyzed, in the search for every invariant too, weighs as many locals as
are in scope. Nothing here is relied on: the module it prints is checked.
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

/-- Claims `rs` of the list `l` by declarations `{name}_{a}`, and from them `name`, that each holds,
the number of claims by the theorem `count`. -/
def claimRuns (name l count : String) (rs : List (Nat × Nat)) : List String :=
  (rs.flatMap fun (a, m) =>
    [s!"theorem {name}_{a} :",
     s!"    (List.range' {a} {m}).all (fun j => (({l}).getD j default).ok size) = true := by",
     "  decide +kernel", ""]) ++
  [s!"theorem {name} : ∀ j, j < ({l}).length → (({l}).getD j default).ok size = true := by",
   "  intro j hj",
   s!"  rw [{count}] at hj"] ++
  (rs.flatMap fun (a, m) =>
    [s!"  by_cases h{a} : j < {a + m}",
     s!"  · exact all_range {name}_{a} j (by omega) (by omega)"]) ++
  ["  exact absurd hj (by omega)", ""]

/-- The theorems on `main`'s claims `l`: the certificate fits, how many claims it makes, and each
holds, in runs of at most `budget`. -/
def mainLines (l checkE : String) (n : Nat) (rs : List (Nat × Nat)) : List String :=
  ["/-- The certificate fits `main`, and how many claims it makes. -/",
   "theorem checked :",
   s!"    (({checkE}).toBool && ({l}).length == {n}) = true := by",
   "  decide +kernel", "",
   s!"theorem accepted : ({checkE}).toBool = true := by",
   "  have h := checked", "  simp only [Bool.and_eq_true] at h", "  exact h.1", "",
   s!"theorem count : ({l}).length = {n} := by",
   "  have h := checked", "  simp only [Bool.and_eq_true, beq_iff_eq] at h", "  exact h.2", ""] ++
  claimRuns "claims_ok" l "count" rs

/-- The module: the certificate, and its claims in declarations of at most `budget` each, as
`claimCost` counts. -/
def render (t : Target) (size budget : Nat) (p : PancakeProg) (k : Cert) : String :=
  let obs := claims size p k
  let lines : List String :=
    ["-- SPDX-License-Identifier: AGPL-3.0-or-later",
     "-- Generated by `dn-compiler analysis-cert`; a test checks it is current."] ++
    t.imports.map (s!"import {·}") ++
    ["import DN.Compiler.AnalyzerCert", "", "/-!", s!"# {t.module}", "", t.doc, "-/", "",
     s!"namespace {t.module}", "", "open DN.Compiler DN.Compiler.Analyzer", "",
     s!"def size : Nat := {t.size}", "",
     s!"theorem lowers : (Lower.lower {t.program}).isSome = true := by decide +kernel", "",
     "/-- The program, as it lowers. -/",
     s!"def mainP : PancakeProg := (Lower.lower {t.program}).get lowers", "",
     s!"theorem lower_main : Lower.lower {t.program} = some mainP :=",
     "  (Option.some_get lowers).symm", "",
     "/-- Where the analysis is cut, and what each piece ends in. -/",
     "def cert : Cert :="] ++ ppCert "  " k ++ [""] ++
    mainLines "claims size mainP cert" "checkC size mainP cert" obs.length
      (runs budget (obs.map (claimCost size))) ++
    [s!"end {t.module}"]
  "\n".intercalate lines ++ "\n"

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
lowers the function's body and checks its certificate's parts there, which costs about as much
memory as a claim of this cost does. -/
def nodeWeight : Nat := 20

/-- The module of a program: each function's certificate, the claims of its functions and of its
`main` in declarations of at most `budget` each, as `claimCost` and `nodeWeight` count. -/
def renderProgram (t : ProgramTarget) (size budget : Nat) (cs : List FnC) (p : PancakeProg)
    (k : Cert) : String :=
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
  let piece : Piece → List String
    | .group a m =>
      [s!"theorem group_{a} :",
       s!"    (List.range' {a} {m}).all (fun i => fnOkAt size [] fnsC i &&",
       "      (fnClaims size [] fnsC i).all (·.ok size)) = true := by",
       "  decide +kernel", ""]
    | .alone i c rs =>
      [s!"theorem fn_{i}_checked :",
       s!"    (fnOkAt size [] fnsC {i} && ({fnClaimsAt i}).length == {c}) = true := by",
       "  decide +kernel", "",
       s!"theorem fn_{i}_count : ({fnClaimsAt i}).length = {c} := by",
       s!"  have h := fn_{i}_checked", "  simp only [Bool.and_eq_true, beq_iff_eq] at h",
       "  exact h.2", ""] ++
      claimRuns s!"fn_{i}" (fnClaimsAt i) s!"fn_{i}_count" rs
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
  let mainClaims := "claims size mainP cert (envAfter [] fnsC)"
  let lines : List String :=
    ["-- SPDX-License-Identifier: AGPL-3.0-or-later",
     "-- Generated by `dn-compiler analysis-cert`; a test checks it is current."] ++
    t.imports.map (s!"import {·}") ++
    ["import DN.Compiler.AnalyzerCertSound", "", "/-!", s!"# {t.module}", "", t.doc, "-/", "",
     s!"namespace {t.module}", "", "open DN.Compiler DN.Compiler.Analyzer", "",
     s!"def size : Nat := {t.size}", "",
     "/-- A function as it lowers. -/",
     "def lowerFn (g : Syntax.PFun) : String × List String × PancakeProg :=",
     "  (g.name, g.params.map (·.2), (Lower.lower g).getD .skip)", "",
     s!"theorem lowers : (Lower.lower {t.program}).isSome = true := by decide +kernel", "",
     "/-- The program's `main`, as it lowers. -/",
     s!"def mainP : PancakeProg := (Lower.lower {t.program}).get lowers", "",
     s!"theorem lower_main : Lower.lower {t.program} = some mainP :=",
     "  (Option.some_get lowers).symm", ""] ++
    (cs.zipIdx.flatMap fun ((_, _, _, c), i) =>
      [s!"def cert_{i} : Cert :="] ++ ppCert "  " c ++ [""]) ++
    ppList "" "def certs : List Cert := " "" ((List.range cs.length).map (s!"cert_{·}")) ++ ["",
     "/-- The functions with their certificates. -/",
     "def fnsC : List FnC :=",
     s!"  (({t.functions}.map lowerFn).zip certs).map fun ((f, ps, b), k) => (f, ps, b, k)", "",
     "/-- …which are the program's functions as they lower. -/",
     "theorem fnsC_lowers :",
     s!"    fnsC.map (fun g => (g.1, g.2.1, g.2.2.1)) = {t.functions}.map lowerFn := by",
     "  unfold fnsC",
     "  rw [List.map_map]",
     "  exact List.map_fst_zip (by decide +kernel)", "",
     "/-- Where the analysis of `main` is cut, and what each piece ends in. -/",
     "def cert : Cert :="] ++ ppCert "  " k ++
    ["", s!"theorem fns_count : fnsC.length = {cs.length} := by decide +kernel", ""] ++
    ps.flatMap piece ++
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
    mainLines mainClaims "checkC size mainP cert (envAfter [] fnsC)" mainObs.length
      (runs budget (costsOf mainObs)) ++
    [s!"end {t.module}"]
  "\n".intercalate lines ++ "\n"

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
