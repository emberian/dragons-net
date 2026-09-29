-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Semantics

/-!
# DN.Compiler.Analyzer

A static analysis of a program in the model's Pancake subset that finds whether any run of it can
end in `Error`: a local read or written before it is declared, a load or a store outside a heap of
`size` bytes from `@base` or a word access off a word boundary, an external call whose arrays lie
outside that heap, a shift without a value. `DN.Compiler.AnalyzerSound` proves that a program it
accepts never errs, so a program is shown safe by running the analysis.

A word is abstracted by an interval of its signed value, or, for an address, of its offset from
`@base`, with the offset's remainder by eight when it is known. A load from memory gives any value,
except a word whose range a condition has just checked (a cell), which keeps that range until the
next store, external call, or change of the local it is addressed by. A loop's invariant is found
by running its body until the state stops growing, widening a bound that keeps moving; whatever the
search finds is checked, and only the check is relied on.
-/

namespace DN.Compiler.Analyzer

open DN.Compiler

def wordMin : Int := -(2 ^ 63)
def wordMax : Int := 2 ^ 63 - 1

/-- A word: its signed value, or its offset from `@base` when `ptr`, lies in `[lo, hi]`, and the
value or offset leaves the remainder `res` by eight when that is known. -/
structure AVal where
  ptr : Bool
  lo : Int
  hi : Int
  res : Option Nat
  deriving DecidableEq, Repr

/-- Any word. -/
def AVal.top : AVal := ⟨false, wordMin, wordMax, none⟩

/-- A number in `[lo, hi]`, or any word if that range is not one of signed words. -/
def AVal.num (lo hi : Int) (res : Option Nat) : AVal :=
  if wordMin ≤ lo ∧ hi ≤ wordMax then ⟨false, lo, hi, res⟩ else AVal.top

def AVal.const (k : Int) : AVal := AVal.num k k (some (k % 8).toNat)

/-- Zero or one, or exactly one of them when it is known. -/
def AVal.flag : Option Bool → AVal
  | some true => AVal.const 1
  | some false => AVal.const 0
  | none => AVal.num 0 1 none

def addRes : Option Nat → Option Nat → Option Nat
  | some a, some b => some ((a + b) % 8)
  | _, _ => none

def subRes : Option Nat → Option Nat → Option Nat
  | some a, some b => some ((a + 8 - b) % 8)
  | _, _ => none

/-- A product is a multiple of eight when a factor is. -/
def mulRes : Option Nat → Option Nat → Option Nat
  | some 0, _ | _, some 0 => some 0
  | _, _ => none

def add (a b : AVal) : AVal :=
  match a.ptr, b.ptr with
  | false, false => AVal.num (a.lo + b.lo) (a.hi + b.hi) (addRes a.res b.res)
  | true, false | false, true => ⟨true, a.lo + b.lo, a.hi + b.hi, addRes a.res b.res⟩
  | true, true => AVal.top

def sub (a b : AVal) : AVal :=
  match a.ptr, b.ptr with
  | false, false => AVal.num (a.lo - b.hi) (a.hi - b.lo) (subRes a.res b.res)
  | true, false => ⟨true, a.lo - b.hi, a.hi - b.lo, subRes a.res b.res⟩
  | _, _ => AVal.top

/-- A number times a constant `k`. -/
def scale (a : AVal) (k : Int) (kres : Option Nat) : AVal :=
  if 0 ≤ k then AVal.num (a.lo * k) (a.hi * k) (mulRes a.res kres)
  else AVal.num (a.hi * k) (a.lo * k) (mulRes a.res kres)

/-- A product of numbers one of which is a constant; any other product is any word. -/
def mul (a b : AVal) : AVal :=
  if a.ptr || b.ptr then AVal.top
  else if b.lo = b.hi then scale a b.lo b.res
  else if a.lo = a.hi then scale b a.lo a.res
  else AVal.top

def and_ (a b : AVal) : AVal :=
  if !a.ptr && !b.ptr && 0 ≤ a.lo && 0 ≤ b.lo then AVal.num 0 (min a.hi b.hi) none else AVal.top

/-- A logical shift right: any word when the distance is a number below a word, no value when
it may be a word or more. -/
def shiftR (b : AVal) : Option AVal :=
  if !b.ptr && 0 ≤ b.lo && b.hi < 64 then some AVal.top else none

/-- Whether `a < b` in signed order, when the ranges decide it. -/
def ltKnown (a b : AVal) : Option Bool :=
  if a.ptr || b.ptr then none
  else if a.hi < b.lo then some true
  else if b.hi ≤ a.lo then some false
  else none

def eqKnown (a b : AVal) : Option Bool :=
  if a.ptr || b.ptr then none
  else if a.lo = a.hi && b.lo = b.hi && a.lo = b.lo then some true
  else if a.hi < b.lo || b.hi < a.lo then some false
  else none

/-- The bytes at the start of the heap, which hold the header the compiler theorem requires and the
host writes before the program starts: no access the analysis accepts reaches into them. -/
def floor : Nat := 64

/-- A byte at an address in the heap, above its header. -/
def byteOk (size : Nat) (p : AVal) : Bool := p.ptr && floor ≤ p.lo && p.hi < size

/-- A word at an address in the heap, on a word boundary. -/
def wordOk (size : Nat) (p : AVal) : Bool := byteOk size p && p.res == some 0

/-- The abstract state: the locals in scope, the innermost first, and the cells — words at a
local's value plus a constant — whose range is known. -/
structure AState where
  locals : List (String × AVal)
  cells : List (String × Int × AVal)
  deriving DecidableEq, Repr

def lookup (x : String) : List (String × AVal) → Option AVal
  | [] => none
  | (y, v) :: rest => if x = y then some v else lookup x rest

/-- The innermost `x` set to `v`; nothing if there is none. -/
def setVar (x : String) (v : AVal) : List (String × AVal) → Option (List (String × AVal))
  | [] => none
  | (y, w) :: rest =>
    if x = y then some ((y, v) :: rest) else ((y, w) :: ·) <$> setVar x v rest

def dropVar (x : String) : List (String × AVal) → List (String × AVal)
  | [] => []
  | (y, w) :: rest => if x = y then rest else (y, w) :: dropVar x rest

def killCells (x : String) (cs : List (String × Int × AVal)) : List (String × Int × AVal) :=
  cs.filter fun c => c.1 != x

def lookupCell (x : String) (k : Int) : List (String × Int × AVal) → Option AVal
  | [] => none
  | (y, j, v) :: rest => if x = y && k = j then some v else lookupCell x k rest

/-- The cell an address expression names: a local, or a local plus a constant. -/
def cellOf : PancakeExp → Option (String × Int)
  | .var x => some (x, 0)
  | .op .add (.var x) (.const k) => some (x, k.toInt)
  | _ => none

/-- The value of an expression in every state the abstract one stands for, or nothing if some of
them may give it none. -/
def evalA (size : Nat) (A : AState) : PancakeExp → Option AVal
  | .const w => some (AVal.const w.toInt)
  | .var x => lookup x A.locals
  | .base => some ⟨true, 0, 0, some 0⟩
  | .op bop l r =>
    match evalA size A l, evalA size A r with
    | some a, some b =>
      match bop with
      | .add => some (add a b)
      | .sub => some (sub a b)
      | .and_ => some (and_ a b)
    | _, _ => none
  | .mul l r =>
    match evalA size A l, evalA size A r with
    | some a, some b => some (mul a b)
    | _, _ => none
  | .shiftR l r =>
    match evalA size A l, evalA size A r with
    | some _, some b => shiftR b
    | _, _ => none
  | .cmp c l r =>
    match evalA size A l, evalA size A r with
    | some a, some b =>
      match c with
      | .less => some (AVal.flag (ltKnown a b))
      | .notLess => some (AVal.flag ((ltKnown a b).map (!·)))
      | .equal => some (AVal.flag (eqKnown a b))
    | _, _ => none
  | .loadByte a =>
    match evalA size A a with
    | some p => if byteOk size p then some (AVal.num 0 255 none) else none
    | none => none
  | .loadWord a =>
    match evalA size A a with
    | some p =>
      if wordOk size p then
        some (match cellOf a with
          | some (x, k) => (lookupCell x k A.cells).getD AVal.top
          | none => AVal.top)
      else none
    | none => none

/-! ## Conditions -/

/-- `[lo, hi]` cut to `[lo', hi']`, or nothing if they do not meet. -/
def meet (v : AVal) (lo hi : Int) : Option AVal :=
  let l := max v.lo lo
  let h := min v.hi hi
  if l ≤ h then some { v with lo := l, hi := h } else none

/-- The state with the range of the local or cell `e` names cut to `[lo, hi]`, when `e` names one
and holds a number; nothing when the ranges do not meet. -/
def refine (size : Nat) (A : AState) (e : PancakeExp) (lo hi : Int) : Option AState :=
  match e with
  | .var x =>
    match lookup x A.locals with
    | some v =>
      if v.ptr then some A
      else (meet v lo hi).bind fun v' =>
        (setVar x v' A.locals).map fun ls => { A with locals := ls }
    | none => some A
  | .loadWord a =>
    match cellOf a, evalA size A (.loadWord a) with
    | some (x, k), some v =>
      if v.ptr then some A
      else (meet v lo hi).map fun v' =>
        { A with cells := (x, k, v') :: A.cells.filter fun c => !(c.1 = x && c.2.1 = k) }
    | _, _ => some A
  | _ => some A

def isFlag (v : AVal) : Bool := !v.ptr && 0 ≤ v.lo && v.hi ≤ 1

/-- The state cut to the runs in which `a < b` holds (`t`) or fails (`!t`), signed. -/
def assumeLt (size : Nat) (A : AState) (a b : PancakeExp) (t : Bool) : Option AState :=
  match evalA size A a, evalA size A b with
  | some va, some vb =>
    if va.ptr || vb.ptr then some A
    else if t then (refine size A a wordMin (vb.hi - 1)).bind fun A' =>
      refine size A' b (va.lo + 1) wordMax
    else (refine size A a vb.lo wordMax).bind fun A' => refine size A' b wordMin va.hi
  | _, _ => some A

def assumeEq (size : Nat) (A : AState) (a b : PancakeExp) : Option AState :=
  match evalA size A a, evalA size A b with
  | some va, some vb =>
    if va.ptr || vb.ptr then some A
    else (refine size A a vb.lo vb.hi).bind fun A' => refine size A' b va.lo va.hi
  | _, _ => some A

/-- The state cut to the runs in which `e` is nonzero (`t`) or zero (`!t`): nothing when there is
none. `AnalyzerSound.assume_sound` takes the cases in the order of these patterns. -/
def assume (size : Nat) (A : AState) : PancakeExp → Bool → Option AState
  | .cmp .less (.const z) (.op .add a b), false =>
    match evalA size A a, evalA size A b with
    | some va, some vb =>
      if z = 0 && isFlag va && isFlag vb then
        (assume size A a false).bind fun A' => assume size A' b false
      else some A
    | _, _ => some A
  | .cmp .equal (.cmp .equal a b) (.const z), false =>
    if z = 0 then assumeEq size A a b else some A
  | .op .and_ a b, true =>
    match evalA size A a, evalA size A b with
    | some va, some vb =>
      if isFlag va && isFlag vb then (assume size A a true).bind fun A' => assume size A' b true
      else some A
    | _, _ => some A
  | .cmp .less a b, t => assumeLt size A a b t
  | .cmp .notLess a b, t => assumeLt size A a b (!t)
  | .cmp .equal a b, true => assumeEq size A a b
  | e, t =>
    match evalA size A e with
    | some v =>
      if v.ptr then some A
      else if t then
        if v.lo = 0 && v.hi = 0 then none
        else if v.lo = 0 then refine size A e 1 wordMax
        else some A
      else refine size A e 0 0
    | none => some A

/-! ## Order -/

def AVal.le (a b : AVal) : Bool :=
  (!b.ptr && b.lo ≤ wordMin && wordMax ≤ b.hi && b.res.isNone) ||
    (a.ptr == b.ptr && b.lo ≤ a.lo && a.hi ≤ b.hi && (b.res.isNone || b.res == a.res))

def AVal.join (a b : AVal) : AVal :=
  if a.ptr == b.ptr then
    ⟨a.ptr, min a.lo b.lo, max a.hi b.hi, if a.res == b.res then a.res else none⟩
  else AVal.top

/-- `b` after `a` on the way to a loop's invariant: a bound that moved goes to the end of the
signed words, and an address that moved stops being one. -/
def AVal.widen (a b : AVal) : AVal :=
  if a.ptr == b.ptr then
    if a.ptr && (b.lo < a.lo || a.hi < b.hi) then AVal.top
    else
      ⟨a.ptr, if b.lo < a.lo then wordMin else a.lo, if a.hi < b.hi then wordMax else a.hi,
        if a.res == b.res then a.res else none⟩
  else AVal.top

def localsLe : List (String × AVal) → List (String × AVal) → Bool
  | [], [] => true
  | (x, a) :: r, (y, b) :: s => x = y && a.le b && localsLe r s
  | _, _ => false

def localsMap (f : AVal → AVal → AVal) :
    List (String × AVal) → List (String × AVal) → Option (List (String × AVal))
  | [], [] => some []
  | (x, a) :: r, (y, b) :: s =>
    if x = y then ((x, f a b) :: ·) <$> localsMap f r s else none
  | _, _ => none

/-- Every run `A` stands for, `B` stands for too. -/
def AState.le (A B : AState) : Bool :=
  localsLe A.locals B.locals &&
    B.cells.all fun (x, k, v) => match lookupCell x k A.cells with
      | some u => u.le v
      | none => false

def cellsJoin (C D : List (String × Int × AVal)) : List (String × Int × AVal) :=
  C.filterMap fun (x, k, u) => (lookupCell x k D).map fun v => (x, k, u.join v)

def AState.join (A B : AState) : Option AState :=
  (localsMap AVal.join A.locals B.locals).map fun ls => ⟨ls, cellsJoin A.cells B.cells⟩

def AState.widen (A B : AState) : Option AState :=
  (localsMap AVal.widen A.locals B.locals).map fun ls => ⟨ls, cellsJoin A.cells B.cells⟩

/-- Of two ways a statement may end normally, either. -/
def joinOpt : Option AState → Option AState → Option AState
  | none, b => b
  | a, none => a
  | some a, some b => a.join b

def leOpt : Option AState → AState → Bool
  | none, _ => true
  | some a, b => a.le b

/-! ## Statements -/

/-- An array of `len` bytes from `p` that lies in the heap, above its header. -/
def arrayOk (size : Nat) (p len : AVal) : Bool :=
  p.ptr && floor ≤ p.lo && !len.ptr && 0 ≤ len.lo && p.hi + len.hi ≤ size

/-- Why a program was not shown safe. -/
abbrev Alarm := String

/-- The outcome of a statement: an alarm, or the state it ends normally in, if it can. -/
abbrev Out := Except Alarm (Option AState)

def need (ok : Bool) (why : Alarm) : Except Alarm Unit := if ok then .ok () else .error why

def valOf (size : Nat) (A : AState) (e : PancakeExp) (what : String) : Except Alarm AVal :=
  match evalA size A e with
  | some v => .ok v
  | none => .error s!"{what}: an expression that may have no value: {repr e}"

/-- The bound the guard `e` puts on the local `x` of `X` when `x` may be as large as any word, plus
one: where a counter stepped by one past the guard stops. -/
def guardHi (size : Nat) (e : PancakeExp) (X : AState) (x : String) (v : AVal) : Option Int :=
  match setVar x { v with hi := wordMax } X.locals with
  | some ls =>
    match assume size { X with locals := ls } e true with
    | some G =>
      match lookup x G.locals with
      | some g => if g.hi < wordMax then some (g.hi + 1) else none
      | none => none
    | none => none
  | none => none

/-- `J` after `X`, with the upper bound of a number that grew taken to where the guard stops it,
if it does: widening up to the guard. -/
def guardWiden (size : Nat) (e : PancakeExp) (X J : AState) : AState :=
  { J with locals := go X.locals J.locals }
where
  go : List (String × AVal) → List (String × AVal) → List (String × AVal)
    | (_, a) :: r, (y, b) :: s =>
      let b' :=
        if !b.ptr && a.hi < b.hi then
          match guardHi size e J y b with
          | some g => if b.hi ≤ g then { b with hi := g } else b
          | none => b
        else b
      (y, b') :: go r s
    | _, s => s

/-- Rounds of the search for a loop's invariant. -/
def searchFuel : Nat := 6

/-- A candidate for a loop's invariant, from `X` with `fuel` more rounds, and the body's outcome
from it. `step` is the body's outcome from the states in which the guard `e` holds. The rounds
join and widen up to the guard, which is enough for counters and for locals the body sets from
bounded ones; the last two widen whatever still grows. A statement leaves the names in scope as it
found them, so the alarm for locals that change is not reached; it keeps the search total. -/
def search (size : Nat) (e : PancakeExp) (step : AState → Out) :
    Nat → AState → Except Alarm (AState × Option AState)
  | 0, X => do .ok (X, ← step X)
  | n + 1, X => do
    let post ← step X
    match post with
    | none => .ok (X, none)
    | some Y =>
      if Y.le X then .ok (X, post)
      else
        match X.join Y with
        | none => .error "while: the locals in scope change in the loop"
        | some J =>
          if 2 < n then search size e step n (guardWiden size e X J)
          else
            match X.widen J with
            | none => .error "while: the locals in scope change in the loop"
            | some W => search size e step n W

/-- A branch's outcome from the states `X` stands for in which `e` is nonzero (`t`) or zero. -/
def branch (size : Nat) (e : PancakeExp) (t : Bool) (body : AState → Out) (X : AState) : Out :=
  match assume size X e t with
  | none => .ok none
  | some G => body G

/-- Of the outcomes of two branches, the state either may end in. Both start from one state and
keep its names in scope, so the alarm is not reached; it keeps the join total. -/
def joinOuts : Option AState → Option AState → Out
  | some B1, some B2 =>
    match B1.join B2 with
    | some B => .ok (some B)
    | none => .error "if: the branches end with other locals in scope"
  | o1, o2 => .ok (joinOpt o1 o2)

/-- The state after a loop with this guard and body, from `A`: an invariant is searched for, and
it is checked to hold on entry and to be kept by the body. -/
def loop (size : Nat) (e : PancakeExp) (body : AState → Out) (A : AState) : Out := do
  let (I, post) ← search size e (branch size e true body) searchFuel A
  need (A.le I) "while: the invariant found does not hold on entry"
  let _ ← valOf size I e "while"
  need (leOpt post I) "while: no invariant found"
  .ok (assume size I e false)

def analyze (size : Nat) (A : AState) : PancakeProg → Out
  | .skip => .ok (some A)
  | .dec x e c => do
    let v ← valOf size A e s!"var {x}"
    let inner := { locals := (x, v) :: A.locals, cells := killCells x A.cells }
    match ← analyze size inner c with
    | none => .ok none
    | some B =>
      let ls := dropVar x B.locals
      need (lookup x ls).isNone s!"var {x}: a local declared again inside its own scope"
      .ok (some { locals := ls, cells := killCells x B.cells })
  | .assign x e => do
    let v ← valOf size A e s!"{x} ="
    match setVar x v A.locals with
    | some ls => .ok (some { locals := ls, cells := killCells x A.cells })
    | none => .error s!"{x} =: {x} is not declared"
  | .store d e => do
    let p ← valOf size A d "st"
    let _ ← valOf size A e "st"
    need (wordOk size p)
      s!"st: an address that may be off the heap or a word boundary: {repr d}, {repr p}"
    .ok (some { A with cells := [] })
  | .storeByte d e => do
    let p ← valOf size A d "st8"
    let _ ← valOf size A e "st8"
    need (byteOk size p) s!"st8: an address that may be off the heap: {repr d}, {repr p}"
    .ok (some { A with cells := [] })
  | .extCall name c cl a al => do
    let cp ← valOf size A c s!"@{name}"
    let clv ← valOf size A cl s!"@{name}"
    let ap ← valOf size A a s!"@{name}"
    let alv ← valOf size A al s!"@{name}"
    need (arrayOk size cp clv && arrayOk size ap alv) s!"@{name}: an array that may be off the heap"
    .ok (some { A with cells := [] })
  | .seq c1 c2 => do
    match ← analyze size A c1 with
    | none => .ok none
    | some B => analyze size B c2
  | .cond e c1 c2 => do
    let _ ← valOf size A e "if"
    let o1 ← branch size e true (fun X => analyze size X c1) A
    let o2 ← branch size e false (fun X => analyze size X c2) A
    joinOuts o1 o2
  | .while_ e c => loop size e (fun X => analyze size X c) A
  | .ret e => do
    let _ ← valOf size A e "return"
    .ok none

/-- The analysis of a whole `main`: no alarm, and no run finishes without a result. -/
def check (size : Nat) (p : PancakeProg) : Except Alarm Unit := do
  match ← analyze size ⟨[], []⟩ p with
  | none => .ok ()
  | some _ => .error "main: a run may finish without a result"

/-! ## Examples: what it accepts and what it refuses, in a heap of 64 bytes above its header -/

open DN.Compiler.PancakeExp (c)

/-- The byte `k` of the heap above its header. -/
private def at' (k : Nat) : PancakeExp := .op .add .base (c (floor + k))
private def heap : Nat := floor + 64
private def storeThenReturn (k : Nat) : PancakeProg := .seq (.store (at' k) (c 1)) (.ret (c 0))

/-- Bytes copied up to a length read from memory, checked (or not) to be at most 32 first. -/
private def copyUpTo (checked : Bool) : PancakeProg :=
  .dec "n" (.loadWord (at' 0))
    (.seq (if checked then
        .cond (.cmp .less (c 0)
            (.op .add (.cmp .less (.var "n") (c 0)) (.cmp .less (c 32) (.var "n"))))
          (.ret (c 1)) .skip
      else .skip)
      (.dec "j" (c 0)
        (.seq (.while_ (.cmp .less (.var "j") (.var "n"))
            (.seq (.storeByte (.op .add (at' 8) (.var "j")) (c 0))
              (.assign "j" (.op .add (.var "j") (c 1)))))
          (.ret (c 0)))))

/-- A byte at an offset read from memory, whose range a condition checked first; a store between
the check and the read forgets it. -/
private def cellProg (storeBetween : Bool) : PancakeProg :=
  .dec "p" (at' 0)
    (.seq (.cond (.cmp .less (c 0) (.op .add (.cmp .less (.loadWord (.var "p")) (c 0))
          (.cmp .less (c 32) (.loadWord (.var "p"))))) (.ret (c 1)) .skip)
      (.seq (if storeBetween then .store (at' 8) (c 0) else .skip)
        (.dec "n" (.loadWord (.var "p"))
          (.seq (.storeByte (.op .add (at' 16) (.var "n")) (c 0)) (.ret (c 0))))))

/-- Four rows of eight bytes, in two nested loops. -/
private def rows : PancakeProg :=
  .dec "i" (c 0) (.seq (.while_ (.cmp .less (.var "i") (c 4))
      (.dec "j" (c 0) (.seq (.while_ (.cmp .less (.var "j") (c 8))
          (.seq (.storeByte (.op .add (.op .add (at' 16) (.mul (.var "i") (c 8))) (.var "j")) (c 0))
            (.assign "j" (.op .add (.var "j") (c 1)))))
        (.assign "i" (.op .add (.var "i") (c 1))))))
    (.ret (c 0)))

/-- Eight bytes from the last down. -/
private def down : PancakeProg :=
  .dec "j" (c 8) (.seq (.while_ (.cmp .less (c 0) (.var "j"))
      (.seq (.assign "j" (.op .sub (.var "j") (c 1)))
        (.storeByte (.op .add (at' 8) (.var "j")) (c 0))))
    (.ret (c 0)))

/-- An external call whose second array runs `len` bytes from byte 8 of the heap. -/
private def call (len : Nat) : PancakeProg :=
  .seq (.extCall "f" (at' 0) (c 8) (at' 8) (c len)) (.ret (c 0))

/-- A word shifted right by `k`: a distance of 64 or more gives no value. -/
private def shifted (k : Nat) : PancakeProg :=
  .dec "n" (.shiftR (.loadWord (at' 0)) (c k)) (.ret (.var "n"))

def regression_825 : Bool := (check heap (storeThenReturn 8)).toBool
def regression_826 : Bool := !(check heap (storeThenReturn 64)).toBool
def regression_827 : Bool := !(check heap (storeThenReturn 4)).toBool
def regression_828 : Bool := !(check heap (.seq (.assign "x" (c 1)) (.ret (c 0)))).toBool
def regression_829 : Bool := (check heap (copyUpTo true)).toBool
def regression_830 : Bool := !(check heap (copyUpTo false)).toBool
def regression_831 : Bool := !(check heap (.store (at' 8) (c 1))).toBool
def regression_832 : Bool := (check heap (cellProg false)).toBool
def regression_833 : Bool := !(check heap (cellProg true)).toBool
def regression_834 : Bool := (check heap rows).toBool
def regression_835 : Bool := (check heap down).toBool
/-- A store into the header is refused. -/
def regression_836 : Bool :=
  !(check heap (.seq (.store (.op .add .base (c 8)) (c 1)) (.ret (c 0)))).toBool
def regression_837 : Bool := (check heap (call 56)).toBool
def regression_838 : Bool := !(check heap (call 57)).toBool
def regression_839 : Bool := (check heap (shifted 63)).toBool
def regression_840 : Bool := !(check heap (shifted 64)).toBool

end DN.Compiler.Analyzer
