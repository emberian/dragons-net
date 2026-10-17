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

/-- How many of the first statements of the chain `p` fit in `budget` together, from `A`. -/
def chainFits (size budget : Nat) (env : Env) (A : AState) (spent : Nat) : PancakeProg → Nat
  | .seq c1 c2 =>
    let c := cost size env A c1
    if budget < spent + c then 0 else
    match analyze size env A c1 with
    | .ok (some B) => 1 + chainFits size budget env B (spent + c) c2
    | _ => 1
  | _ => 0

/-- A certificate for `p` from `A`, with the functions `env` to call, cut where a piece costs more
than `budget`, no deeper than `fuel`. -/
def certify (size budget : Nat) (env : Env) : Nat → AState → PancakeProg → Except Alarm Cert
  | 0, A, p => leafOf size env A p
  | fuel + 1, A, p =>
    if cost size env A p ≤ budget then leafOf size env A p else
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
    ppList ind (head ++ "{ locals := ") "" (d.locals.map ppLocal) ++
      ppList ind "  cells := some " (" }" ++ tail) (cs.map ppCell)

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

/-- The module: the certificate, a declaration for each claim, and the claims together. -/
def render (t : Target) (k : Cert) (n : Nat) : String :=
  let claim (i : Nat) : List String :=
    [s!"theorem claim_{i} : ((claims size mainP cert).getD {i} default).ok size = true := by",
     "  decide +kernel"]
  let cases := (List.range n).map fun i => s!"  | {i}, _ => exact claim_{i}"
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
     "def cert : Cert :="] ++ ppCert "  " k ++
    ["", "/-- The certificate fits the program. -/",
     "theorem accepted : (checkC size mainP cert).toBool = true := by decide +kernel", "",
     s!"theorem count : (claims size mainP cert).length = {n} := by decide +kernel", ""] ++
    ((List.range n).flatMap fun i => claim i ++ [""]) ++
    ["/-- Every claim holds. -/",
     "theorem claims_ok : ∀ i, i < (claims size mainP cert).length →",
     "    ((claims size mainP cert).getD i default).ok size = true := by",
     "  intro i hi",
     "  rw [count] at hi",
     "  match i, hi with"] ++ cases ++
    [s!"  | _ + {n}, h => exact absurd h (by omega)", "", s!"end {t.module}"]
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
