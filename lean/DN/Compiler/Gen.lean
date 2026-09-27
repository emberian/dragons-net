-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean.Data.Json
import DN.Compiler.Abi
import DN.Compiler.Canon

/-!
# DN.Compiler.Gen

Bounded random programs of the subset the gate accepts, for the generated differential lane
(`scripts/native_fuzz.py`). Each program goes through the real gate and printer
(`Abi.emitWord`), and the model runs its lowering; the expected values come from the model,
never from the generator, and the lane holds them against an independent interpreter of the
source and against the compiled code.

Memory is a plan, not a set of numbers. There are three data buffers of one page, a page of
pointers into them and a page holding the result slot; the host maps each with a page without
access on both sides. A program reaches memory only through a pointer: a parameter, a local
declared from one, or a word loaded from the page of pointers, which the host fills with the
real addresses and the model with its own. Pointers are only ever used as addresses, so the
two sets of addresses never meet in a value. Every access the generator emits lies inside its
buffer, and word accesses are aligned; accesses at the first and last byte and word of a buffer
are favoured, since there the pages without access check that the compiled code touches
nothing beyond.

Which constructs a program may use is drawn per program (swarm testing): a mix that leaves
most of them out reaches combinations a fixed mix rarely does.
-/

namespace DN.Compiler.Gen

open Lean DN.Compiler.Syntax DN.Compiler.Lower

/-! ## SplitMix64

The same function fills the buffers in the model, in the independent interpreter and in the
host, so it is written out here rather than taken from a library. -/

def golden : UInt64 := 0x9E3779B97F4A7C15

def mix (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- Output `i` (from zero) of SplitMix64 started at `seed`. -/
def splitmix (seed : UInt64) (i : Nat) : UInt64 := mix (seed + golden * UInt64.ofNat (i + 1))

/-- A generator: the seed and how many outputs it has used. -/
abbrev G := StateM (UInt64 × Nat)

def next : G UInt64 := modifyGet fun (seed, i) => (splitmix seed i, (seed, i + 1))

def below (n : Nat) : G Nat := do
  let x ← next
  return if n == 0 then 0 else x.toNat % n

def chance (k outOf : Nat) : G Bool := do return (← below outOf) < k

def pick {α : Type} [Inhabited α] (xs : List α) : G α := do return xs[← below xs.length]!

/-- One of `xs`, or `d` when there is none. -/
def pickOr {α : Type} (d : α) (xs : List α) : G α := do return xs.getD (← below xs.length) d

/-! ## The memory plan -/

def pageBytes : Nat := 4096
def buffers : Nat := 3
def words : Nat := pageBytes / 8

/-- Where the model puts buffer `b`, the page of pointers and the result slot. The host puts
them elsewhere; no value a program computes depends on either. -/
def bufferBase (b : Nat) : Nat := 0x100000 * (b + 1)
def tableBase : Nat := 0x400000
def slotAddress : Nat := 0x500000 + pageBytes - 8

inductive Param
  | data (name : String)
  /-- A pointer to `offset` bytes into buffer `buffer`. -/
  | pointer (name : String) (buffer offset : Nat)
  /-- The page of pointers. -/
  | table (name : String)
  deriving Inhabited

def Param.name : Param → String
  | .data x | .pointer x _ _ | .table x => x

structure Plan where
  params : List Param
  /-- Word `k` of the page of pointers points `offset` bytes into buffer `buffer`. -/
  entries : List (Nat × Nat)

/-! ## What a program may use -/

structure Config where
  ops : List POp
  shift : Bool
  loadWord : Bool
  loadByte : Bool
  storeWord : Bool
  storeByte : Bool
  branches : Bool
  loops : Bool
  /-- Pointers loaded from the page of pointers, so loads nested in load addresses. -/
  table : Bool
  /-- Two pointer parameters into one buffer. -/
  alias : Bool
  /-- Offsets computed from data, masked into the buffer. -/
  computed : Bool
  pointerLocals : Bool
  earlyReturn : Bool
  /-- Expression depth. -/
  depth : Nat
  /-- Statements a block may have. -/
  statements : Nat
  /-- How deep blocks may nest. -/
  nesting : Nat

def Config.memory (c : Config) : Bool := c.loadWord || c.loadByte || c.storeWord || c.storeByte

def allOps : List POp := [.add, .sub, .mul, .and_, .lt, .le, .eq]

def genConfig : G Config := do
  let ops ← allOps.filterM fun _ => chance 1 2
  let flag := chance 1 2
  return { ops := if ops.isEmpty then [.add] else ops, shift := ← flag, loadWord := ← flag,
           loadByte := ← flag, storeWord := ← flag, storeByte := ← flag, branches := ← flag,
           loops := ← flag, table := ← flag, alias := ← flag, computed := ← flag,
           pointerLocals := ← flag, earlyReturn := ← flag, depth := 1 + (← below 4),
           statements := 1 + (← below 6), nesting := 1 + (← below 3) }

/-- An aligned offset into a buffer, favouring its first and last words. -/
def genOffset : G Nat := do
  match ← below 4 with
  | 0 => return 0
  | 1 => return pageBytes - 8
  | _ => return 8 * (← below words)

def genPlan (c : Config) : G Plan := do
  let mut params : List Param := []
  let mut entries : List (Nat × Nat) := []
  if c.memory || c.table then
    let b ← below buffers
    let offset ← if ← chance 1 2 then pure 0 else genOffset
    params := params ++ [.pointer "p" b offset]
    if c.alias then
      params := params ++ [.pointer "q" b (← genOffset)]
    else if ← chance 1 3 then
      params := params ++ [.pointer "q" (← below buffers) 0]
    if c.table then
      params := params ++ [.table "t"]
      let count := 1 + (← below 4)
      for _ in [0:count] do
        entries := entries ++ [(← below buffers, ← genOffset)]
  let dataNames := ["a", "b", "c"]
  let room := 3 - params.length
  let count ← if room > 0 && (← chance 3 4) then (· + 1) <$> below room else pure 0
  params := params ++ (dataNames.take count).map Param.data
  return { params, entries }

/-! ## Expressions

CakeML's static checker (`pancake/panStaticScript.sml`) tracks, for every local, whether it is
derived from the base address, and warns about a load or store whose address may not be. A
parameter and a loaded word are `Trusted`, a literal or a comparison `NotBased`, an operation
the strongest of its operands, and a local that the branches of an `if`, or a loop and the code
before it, leave in different states `NotTrusted`. An address holding a `NotTrusted` part draws
the warning, and the lane fails on every warning, so the generator keeps the same account and
builds addresses only from parts that are not `NotTrusted`.

The two pinned revisions differ in one rule: a shift takes the state of the shifted expression
at `ed31510` and that of the distance at `e8eca63`, where a literal distance makes it
`NotBased`. The account is kept for both, and a part counts as trusted only if it is in both. -/

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

/-- A local is data (mutable or not), a pointer with the range of byte offsets it may hold into
its buffer (both ends multiples of eight), or the page of pointers. -/
inductive Ty
  | data (mutable : Bool)
  | ptr (buffer lo hi : Nat)
  | table
  deriving Inhabited

abbrev Env := List (String × Ty)

def interesting : List Nat :=
  [0, 1, 2, 3, 7, 8, 31, 63, 64, 127, 128, 255, 256, 4095, 4096, 2 ^ 31 - 1, 2 ^ 31,
   2 ^ 32 - 1, 2 ^ 32, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64 - 1]

def genConst : G Nat := do
  if ← chance 3 4 then pick interesting else return (← next).toNat

def dataVars (env : Env) : List String :=
  env.filterMap fun (x, t) => match t with | .data _ => some x | _ => none

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
  | .shr l r => ((bdWith look r).1, (bdWith look l).2)

/-! ### The account

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
  | .binop _ l r | .shr l r => acc.loads l && acc.loads r
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
    if acc.loads e then some (acc.map fun (y, b) => if y == x then (y, acc.bd e) else (y, b)) else none
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

/-- The locals an address may be computed from: none either revision no longer trusts. -/
def settled (env : Env) (acc : Account) : Env :=
  env.filter fun (x, t) => match t with
    | .data _ =>
      let (a, b) := (acc.lookup x).getD (Bd2.all .trusted)
      a != .notTrusted && b != .notTrusted
    | _ => true

/-! ### Building expressions -/

def genLeaf (env : Env) : G PExpr := do
  let vars := dataVars env
  if !vars.isEmpty && (← chance 3 4) then return .var (← pick vars) else return .const (← genConst)

/-- The pointers a program can name here, with where they point: a pointer parameter or
local, or a word of the page of pointers. -/
def pointers (c : Config) (plan : Plan) (env : Env) : List (PExpr × Nat × Nat × Nat) :=
  let direct := env.filterMap fun (x, t) => match t with
    | .ptr b lo hi => some (.var x, b, lo, hi)
    | _ => none
  let loaded := if !c.table then [] else env.flatMap fun (x, t) => match t with
    | .table => plan.entries.zipIdx.map fun ((b, o), k) =>
        (.loadw 1 (if k == 0 then .var x else eAdd (.var x) (.const (8 * k))), b, o, o)
    | _ => []
  direct ++ loaded

def log2Floor : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => 1 + log2Floor ((n + 2) / 2)
  decreasing_by omega

/-- An address of an access `width` bytes wide (1 or 8) inside the buffer of some pointer, or
nothing when no pointer is in scope. `offset` generates the data an offset is computed from. -/
def genAddress (c : Config) (plan : Plan) (env : Env) (width : Nat) (offset : G PExpr) :
    G (Option PExpr) := do
  let ps := pointers c plan env
  if ps.isEmpty then return none
  let (p, _, lo, hi) ← pickOr (.const 0, 0, 0, 0) ps
  if c.computed && (← chance 1 2) then
    -- The masked value plus the pointer stays below the end of the buffer.
    let room := (pageBytes - width - hi) / width
    let bits := log2Floor (room + 1)
    let k ← if bits == 0 then pure 0 else (· + 1) <$> below bits
    let masked := eAnd (← offset) (.const (2 ^ k - 1))
    return some (eAdd p (if width == 1 then masked else eMul masked (.const 8)))
  let least : Int := -(lo : Int)
  let most : Int := (pageBytes : Int) - width - hi
  let steps := ((most - least) / width).toNat
  let o : Int ← match ← below 4 with
    | 0 => pure least
    | 1 => pure most
    | 2 => pure 0
    | _ => pure (least + (width : Int) * (← below (steps + 1)))
  return some (if o == 0 then p else if o > 0 then eAdd p (.const o.toNat) else eSub p (.const (-o).toNat))

/-- An expression of data over `env`, whose offsets use only the locals in `safe`. -/
def genData (c : Config) (plan : Plan) : Nat → Env → Env → G PExpr
  | 0, env, _ => genLeaf env
  | d + 1, env, safe => do
    let sub := genData c plan d env safe
    let offset := genData c plan d safe safe
    let mut kinds : List Nat := [0, 1, 1]
    if c.shift then kinds := kinds ++ [2]
    if c.loadWord then kinds := kinds ++ [3]
    if c.loadByte then kinds := kinds ++ [4]
    match ← pick kinds with
    | 1 => return .binop (← pickOr .add c.ops) (← sub) (← sub)
    | 2 => return .shr (← sub) (.const (← pick [0, 1, 7, 8, 31, 32, 35, 63, ← below 64]))
    | 3 =>
      match ← genAddress c plan env 8 offset with
      | some a => return .loadw 1 a
      | none => genLeaf env
    | 4 =>
      match ← genAddress c plan env 1 offset with
      | some a => return .loadb a
      | none => genLeaf env
    | _ => genLeaf env

/-! ## Statements -/

def fresh (env : Env) (pool : List String) : G (Option String) := do
  let free := pool.filter fun x => !env.any (·.1 == x)
  if free.isEmpty then return none else return some (← pick free)

def dataPool : List String := ["x0", "x1", "x2", "x3", "x4", "x5"]
def pointerPool : List String := ["r0", "r1", "r2"]
def counterPool : List String := ["i0", "i1", "i2"]

/-- A pointer local: a pointer in scope moved by an aligned constant or by a masked multiple of
eight, with the range it can then hold. -/
def genPointerLocal (c : Config) (plan : Plan) (env : Env) (offset : G PExpr) :
    G (Option (PExpr × Ty)) := do
  let ps := pointers c plan env
  if ps.isEmpty then return none
  let (p, b, lo, hi) ← pickOr (.const 0, 0, 0, 0) ps
  if c.computed && (← chance 1 2) then
    let room := (pageBytes - 8 - hi) / 8
    let bits := log2Floor (room + 1)
    let k ← if bits == 0 then pure 0 else (· + 1) <$> below bits
    return some (eAdd p (eMul (eAnd (← offset) (.const (2 ^ k - 1))) (.const 8)),
                 .ptr b lo (hi + 8 * (2 ^ k - 1)))
  let steps := (pageBytes - 8 - hi) / 8
  let o := 8 * (← below (steps + 1))
  return some (if o == 0 then p else eAdd p (.const o), .ptr b (lo + o) (hi + o))

/-- A block of statements over the locals `env`, in the states `acc` records, and whether it
always leaves the function. `iterations` is how many times the block may run in all, which
bounds the loops inside it. -/
def genBlock (c : Config) (plan : Plan) : Nat → Nat → Bool → Env → Account → G (List PStmt × Bool)
  | 0, _, _, _, _ => return ([], false)
  | fuel + 1, iterations, top, env0, acc0 => do
    let count := 1 + (← below c.statements)
    let mut env := env0
    let mut acc := acc0
    let mut out : List PStmt := []
    let mut exits := false
    for _ in [0:count] do
      if exits then break
      -- Offsets and pointer locals only from parts the checker trusts.
      let safe := settled env acc
      let data := genData c plan c.depth env safe
      let offset := genData c plan (c.depth - 1) safe safe
      let mutable := env.filterMap fun (x, t) => match t with | .data true => some x | _ => none
      let mut kinds : List Nat := [0, 0]
      if !mutable.isEmpty then kinds := kinds ++ [1]
      if c.storeWord then kinds := kinds ++ [2]
      if c.storeByte then kinds := kinds ++ [3]
      if c.branches && fuel > 0 then kinds := kinds ++ [4]
      if c.loops && fuel > 0 && iterations * 8 ≤ 64 then kinds := kinds ++ [5]
      if c.pointerLocals then kinds := kinds ++ [6]
      if c.earlyReturn && !top then kinds := kinds ++ [7]
      let mut made : List PStmt := []
      match ← pick kinds with
      | 1 => made := [.assign (← pick mutable) (← data)]
      | 2 =>
        if let some a ← genAddress c plan env 8 offset then
          made := [.store a (← data)]
      | 3 =>
        if let some a ← genAddress c plan env 1 offset then
          made := [.storeb a (← data)]
      | 4 =>
        let cond ← data
        let (t, et) ← genBlock c plan fuel iterations false env acc
        let (e, ee) ← genBlock c plan fuel iterations false env acc
        made := [.ite cond t e]
        exits := et && ee
      | 5 =>
        if let some i ← fresh env counterPool then
          let bound ← if ← chance 1 2 then pure (.const (← below 9))
            else pure (eAnd (← genData c plan (c.depth - 1) env safe) (.const 7))
          let inner := env ++ [(i, .data false)]
          let (body, bodyExits) ←
            genBlock c plan fuel (iterations * 8) false inner (acc ++ [(i, Bd2.all .notBased)])
          let step := if bodyExits then [] else [.assign i (eAdd (.var i) (.const 1))]
          made := [.dec i (.const 0), .while (eLt (.var i) bound) (body ++ step)]
          env := inner
      | 6 =>
        if let some r ← fresh env pointerPool then
          if let some (e, t) ← genPointerLocal c plan env offset then
            made := [.dec r e]
            env := env ++ [(r, t)]
      | 7 =>
        made := [.ret (← data)]
        exits := true
      | _ =>
        if let some x ← fresh env dataPool then
          made := [.dec x (← data)]
          env := env ++ [(x, .data true)]
      out := out ++ made
      -- The generator only builds what the account allows, so this never falls back; if it did,
      -- `record` refuses the program.
      acc := (blockAccount acc made).getD acc
    if top && !exits then
      out := out ++ [.ret (← genData c plan c.depth env (settled env acc))]
      exits := true
    return (out, exits)

def paramEnv (plan : Plan) : Env :=
  plan.params.map fun
    | .data x => (x, .data true)
    | .pointer x b o => (x, .ptr b o o)
    | .table x => (x, .table)

def genFun (name : String) (c : Config) (plan : Plan) : G PFun := do
  let (body, _) ← genBlock c plan (c.nesting + 1) 1 true (paramEnv plan)
    (plan.params.map fun p => (p.name, Bd2.all .trusted))
  return { name, exported := true, params := plan.params.map fun p => (1, p.name), body }

/-! ## Inputs and what the model makes of them -/

/-- One call: the value of each data parameter, and the seed and mask the buffers are filled
from. -/
structure Vector where
  data : List (String × Nat)
  seed : UInt64
  mask : UInt64

def masks : List UInt64 :=
  [0xFFFFFFFFFFFFFFFF, 0x0707070707070707, 0xFF, 0x8080808080808080, 0]

def genVector (plan : Plan) : G Vector := do
  let data ← plan.params.filterMapM fun
    | .data x => do return some (x, ← genConst)
    | _ => return none
  return { data, seed := ← next, mask := ← pick masks }

/-- Word `i` of buffer `b` before the call. -/
def fillWord (seed mask : UInt64) (b i : Nat) : Nat := (splitmix seed (b * words + i) &&& mask).toNat

def modelMemory (plan : Plan) (vec : Vector) (a : Word) : Word :=
  let x := a.toNat
  if x % 8 != 0 then 0
  else if x ≥ tableBase && x < tableBase + pageBytes then
    match plan.entries[(x - tableBase) / 8]? with
    | some (b, o) => BitVec.ofNat 64 (bufferBase b + o)
    | none => 0
  else
    let b := x / 0x100000 - 1
    let o := x % 0x100000
    if x ≥ bufferBase 0 && b < buffers && o < pageBytes then
      BitVec.ofNat 64 (fillWord vec.seed vec.mask b (o / 8))
    else 0

def modelDomain (a : Word) : Bool :=
  let x := a.toNat
  let b := x / 0x100000 - 1
  x % 8 == 0 &&
    ((x ≥ bufferBase 0 && b < buffers && x % 0x100000 < pageBytes) ||
     (x ≥ tableBase && x < tableBase + pageBytes) || x == slotAddress)

/-- The model's clock: well above the 2,352 loop iterations a generated program can take, and low
enough that a program the reducer turned into a long loop is refused quickly, since each store the
model makes lengthens every later load. -/
def clock : Nat := 10000

def modelState (plan : Plan) (vec : Vector) : PancakeState Unit :=
  let value : Param → Option Word
    | .data x => (vec.data.lookup x).map (BitVec.ofNat 64)
    | .pointer _ b o => some (BitVec.ofNat 64 (bufferBase b + o))
    | .table _ => some (BitVec.ofNat 64 tableBase)
  { locals := fun x => (plan.params.find? (·.name == x)).bind value,
    memory := modelMemory plan vec, memaddrs := modelDomain, be := false, clock,
    ffi := (), baseAddr := 0 }

/-- What the model makes of one call: the word the function returns and every word of the
buffers it changed, as buffer, byte offset and new value. -/
structure Outcome where
  result : Nat
  changed : List (Nat × Nat × Nat)

def run (f : PFun) (plan : Plan) (vec : Vector) : Except String Outcome := do
  let oracle : Oracle Unit := ⟨fun _ _ _ _ => .final .failed⟩
  let some wrapped := lower (Abi.wordResult f) | throw "the program does not lower"
  let some original := lower f | throw "the program does not lower"
  let s := modelState plan vec
  let (r, final) := PancakeSem oracle wrapped
    { s with locals := setLocal s.locals "dn_result" (BitVec.ofNat 64 slotAddress) }
  unless r == some (.return_ 0) do throw s!"the model does not return through the slot: {repr r}"
  let (r0, _) := PancakeSem oracle original s
  let some (.return_ value) := r0 | throw s!"the model does not return: {repr r0}"
  let result := final.memory (BitVec.ofNat 64 slotAddress)
  unless result == value do throw "the slot holds another value than the function returns"
  let mut changed := #[]
  for b in [0:buffers] do
    for i in [0:words] do
      let a : Word := BitVec.ofNat 64 (bufferBase b + 8 * i)
      if final.memory a != s.memory a then changed := changed.push (b, 8 * i, (final.memory a).toNat)
  for i in [0:words] do
    let a : Word := BitVec.ofNat 64 (tableBase + 8 * i)
    if final.memory a != s.memory a then throw "the program wrote into the page of pointers"
  return { result := result.toNat, changed := changed.toList }

/-! ## The source, as data

The independent interpreter reads the program in this form, and the reducer writes it back;
`funOfJson` reads it for the model. -/

def exprJson : PExpr → Json
  | .const k => toJson k
  | .var x => toJson x
  | .base => Json.arr #["@base"]
  | .binop op l r => Json.arr #[toJson (opSym op), exprJson l, exprJson r]
  | .loadw sh a => Json.arr #["lds", toJson sh, exprJson a]
  | .loadb a => Json.arr #["ld8", exprJson a]
  | .shr l r => Json.arr #[">>>", exprJson l, exprJson r]

mutual
def stmtJson : PStmt → Json
  | .dec x e => Json.arr #["var", toJson x, exprJson e]
  | .assign x e => Json.arr #["set", toJson x, exprJson e]
  | .store a e => Json.arr #["st", exprJson a, exprJson e]
  | .storeb a e => Json.arr #["st8", exprJson a, exprJson e]
  | .ffi name args => Json.arr #["ffi", toJson name, Json.arr (args.map exprJson).toArray]
  | .call r name args => Json.arr #["call", toJson r, toJson name, Json.arr (args.map exprJson).toArray]
  | .ret e => Json.arr #["return", exprJson e]
  | .ite e t f => Json.arr #["if", exprJson e, blockJson t, blockJson f]
  | .while e b => Json.arr #["while", exprJson e, blockJson b]
def blockJson : List PStmt → Json
  | ss => Json.arr (ss.map stmtJson).toArray
end

def funJson (f : PFun) : Json :=
  Json.mkObj [("name", toJson f.name), ("params", toJson (f.params.map (·.2))),
    ("body", blockJson f.body)]

def opOfSym (s : String) : Option POp := allOps.find? (opSym · == s)

/-- How deeply the readers below follow a nested program before giving up. -/
def nesting : Nat := 10000

def exprOfJson : Nat → Json → Except String PExpr
  | 0, _ => throw "an expression nested too deeply"
  | fuel + 1, j => do
    if let .ok k := j.getNat? then return .const k
    if let .ok x := j.getStr? then return .var x
    match (← j.getArr?).toList with
    | [.str "@base"] => return .base
    | [.str "lds", sh, a] => return .loadw (← sh.getNat?) (← exprOfJson fuel a)
    | [.str "ld8", a] => return .loadb (← exprOfJson fuel a)
    | [.str ">>>", l, r] => return .shr (← exprOfJson fuel l) (← exprOfJson fuel r)
    | [.str s, l, r] =>
      match opOfSym s with
      | some op => return .binop op (← exprOfJson fuel l) (← exprOfJson fuel r)
      | none => throw s!"unknown operator {s}"
    | _ => throw s!"not an expression: {j.compress}"

def stmtOfJson : Nat → Json → Except String PStmt
  | 0, _ => throw "a statement nested too deeply"
  | fuel + 1, j => do
    let block (b : Array Json) := b.toList.mapM (stmtOfJson fuel)
    let e := exprOfJson nesting
    match (← j.getArr?).toList with
    | [.str "var", .str x, v] => return .dec x (← e v)
    | [.str "set", .str x, v] => return .assign x (← e v)
    | [.str "st", a, v] => return .store (← e a) (← e v)
    | [.str "st8", a, v] => return .storeb (← e a) (← e v)
    | [.str "return", v] => return .ret (← e v)
    | [.str "if", c, .arr thn, .arr els] => return .ite (← e c) (← block thn) (← block els)
    | [.str "while", c, .arr b] => return .while (← e c) (← block b)
    | [.str "ffi", .str name, .arr args] => return .ffi name (← args.toList.mapM e)
    | [.str "call", .str r, .str name, .arr args] => return .call r name (← args.toList.mapM e)
    | _ => throw s!"not a statement: {j.compress}"

def funOfJson (j : Json) : Except String PFun := do
  let params := (← j.getObjValAs? (List String) "params").map fun x => (1, x)
  let body ← (← (← j.getObjVal? "body").getArr?).toList.mapM (stmtOfJson nesting)
  return { name := ← j.getObjValAs? String "name", exported := true, params, body }

def paramJson : Param → Json
  | .data x => Json.mkObj [("name", toJson x), ("kind", "data")]
  | .pointer x b o => Json.mkObj [("name", toJson x), ("kind", "pointer"), ("buffer", toJson b),
      ("offset", toJson o)]
  | .table x => Json.mkObj [("name", toJson x), ("kind", "table")]

def planJson (plan : Plan) : Json :=
  Json.mkObj [("params", Json.arr (plan.params.map paramJson).toArray),
    ("entries", toJson (plan.entries.map fun (b, o) => [b, o]))]

def paramOfJson (j : Json) : Except String Param := do
  let name ← j.getObjValAs? String "name"
  match ← j.getObjValAs? String "kind" with
  | "data" => return .data name
  | "pointer" => return .pointer name (← j.getObjValAs? Nat "buffer") (← j.getObjValAs? Nat "offset")
  | "table" => return .table name
  | k => throw s!"unknown parameter kind {k}"

def planOfJson (j : Json) : Except String Plan := do
  let params ← (← (← j.getObjVal? "params").getArr?).toList.mapM paramOfJson
  let entries ← (← j.getObjValAs? (List (List Nat)) "entries").mapM fun
    | [b, o] => pure (b, o)
    | _ => throw "an entry is a buffer and an offset"
  return { params, entries }

def vectorJson (v : Vector) : Json :=
  Json.mkObj [("data", Json.mkObj (v.data.map fun (x, k) => (x, toJson k))),
    ("fill", toJson [v.seed.toNat, v.mask.toNat])]

def vectorOfJson (j : Json) : Except String Vector := do
  let data ← match ← j.getObjVal? "data" with
    | .obj kvs => kvs.toList.mapM fun (x, k) => do return (x, ← k.getNat?)
    | _ => throw "data is an object"
  match ← j.getObjValAs? (List Nat) "fill" with
  | [seed, mask] => return { data, seed := UInt64.ofNat seed, mask := UInt64.ofNat mask }
  | _ => throw "fill is a seed and a mask"

def configJson (c : Config) : Json :=
  Json.mkObj [("ops", toJson (c.ops.map opSym)), ("shift", toJson c.shift),
    ("load_word", toJson c.loadWord), ("load_byte", toJson c.loadByte),
    ("store_word", toJson c.storeWord), ("store_byte", toJson c.storeByte),
    ("branches", toJson c.branches), ("loops", toJson c.loops), ("table", toJson c.table),
    ("alias", toJson c.alias), ("computed", toJson c.computed),
    ("pointer_locals", toJson c.pointerLocals), ("early_return", toJson c.earlyReturn),
    ("depth", toJson c.depth), ("statements", toJson c.statements), ("nesting", toJson c.nesting)]

/-! ## Records -/

/-- A program with its inputs, checked by the gate, printed, lowered and run in the model. -/
def record (f : PFun) (plan : Plan) (vectors : List Vector) (extra : List (String × Json)) :
    Except String Json := do
  let source ← (Abi.emitWord f).mapError Checked.Reason.message
  unless trustedAddresses (Abi.wordResult f) do
    throw "an address CakeML's static checker does not trust, which it would warn about"
  let tree ← Canon.program (Abi.wordResult f) source
  let runs ← vectors.mapM fun vec => do
    let o ← run f plan vec
    return Json.mkObj [("data", Json.mkObj (vec.data.map fun (x, k) => (x, toJson k))),
      ("fill", toJson [vec.seed.toNat, vec.mask.toNat]), ("result", toJson o.result),
      ("changed", toJson (o.changed.map fun (b, off, w) => [b, off, w]))]
  return Json.mkObj (extra ++ [("name", toJson f.name), ("plan", planJson plan),
    ("program", funJson f), ("source", toJson source), ("tree", tree),
    ("vectors", Json.arr runs.toArray)])

/-- Program `index` of the run started from `seed`: drawn from its own seed, so it can be made
again without the programs before it. -/
def generated (seed : UInt64) (index vectors : Nat) : Except String Json :=
  let draw : G (Config × Plan × PFun × List Vector) := do
    let c ← genConfig
    let plan ← genPlan c
    let f ← genFun s!"dn_fuzz_{index}" c plan
    let vs ← (List.range vectors).mapM fun _ => genVector plan
    return (c, plan, f, vs)
  let ((c, plan, f, vs), _) := draw.run (splitmix seed index, 0)
  (record f plan vs [("index", toJson index), ("config", configJson c)]).mapError
    fun e => s!"program {index} of seed {seed}: {e}\n{ppFun f}"

def emit (seed : UInt64) (count vectors : Nat) : Except String Json := do
  return Json.arr (← (List.range count).mapM fun i => generated seed i vectors).toArray

/-- Programs given as data, as the reducer and the corpus give them: each is checked, printed
and run like a generated one, and one that the gate refuses or the model does not run is
answered with the reason. -/
def replay (input : Json) : Except String Json := do
  let cases ← input.getArr?
  let out ← cases.mapM fun j => do
    let answer : Except String Json := do
      let f ← funOfJson (← j.getObjVal? "program")
      let plan ← planOfJson (← j.getObjVal? "plan")
      let vectors ← (← (← j.getObjVal? "vectors").getArr?).toList.mapM vectorOfJson
      record f plan vectors []
    match answer with
    | .ok r => pure r
    | .error e => pure (Json.mkObj [("error", toJson e)])
  return Json.arr out

/-- Outputs of SplitMix64 and fill words, for the test that holds the model's, the
interpreter's and the host's implementations together. -/
def samples : Json :=
  let seeds : List UInt64 := [0, 1, 0xFFFFFFFFFFFFFFFF]
  Json.mkObj [("splitmix", toJson (seeds.map fun s => (List.range 4).map fun i => (splitmix s i).toNat)),
    ("fill", toJson (masks.map fun m => [fillWord 7 m 0 0, fillWord 7 m 2 511]))]

end DN.Compiler.Gen
