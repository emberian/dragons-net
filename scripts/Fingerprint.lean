-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean

/-!
What a command of `dn-compiler` runs, after `lake build`:

  LEAN_PATH=<toolchain>/lib/lean:.lake/build/lib/lean lean --run scripts/Fingerprint.lean COMMAND...

prints, one JSON array a line, every declaration of the library the commands reach, theorems aside:
its expressions as a graph of nodes, each `[tag, fields, children]` whose children are earlier lines,
then the declaration, `["d", [name, kind, attributes...], [type, value]]`; the code the compiler made
of them and of what that code calls in the library, `["I", [code], []]`; then for each command
`["c", [command], [handler, declaration..., code...]]`. `scripts/once.py` hashes each line with what
its children hash to. The handler is the command's expression in `DN.Compiler.Cli.table` or, for a
printed program's `emit-NAME`, in `DN.Printed.named`; with it, `main`, which picks it, and what they
reach, the tables aside. Theorems are erased from the code, and binder names and kinds do not change
it. What the executable does when it starts, the same for every command, the toolchain and the
build's options are the caller's to count.
-/

open Lean

def dependencies (info : ConstantInfo) : Array Name :=
  let body := match info.value? (allowOpaque := true) with
    | some value => value.getUsedConstants
    | none => #[]
  let extra := match info with
    | .inductInfo v => v.ctors.toArray
    | .recInfo v => v.rules.toArray.flatMap (·.rhs.getUsedConstants)
    | _ => #[]
  info.type.getUsedConstants ++ body ++ extra

/-- The second part of the pair whose first is the string `name`, in `e`. -/
partial def paired (name : String) (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Prod.mk 4 && e.getAppArgs[2]! == .lit (.strVal name) then some e.getAppArgs[3]!
  else match e with
    | .app f a => paired name f <|> paired name a
    | .lam _ t b _ | .forallE _ t b _ => paired name t <|> paired name b
    | .letE _ t v b _ => paired name t <|> paired name v <|> paired name b
    | .mdata _ b | .proj _ _ b => paired name b
    | _ => none

/-- The pair naming `name` in the value of `root` or of a declaration of its module it reaches. -/
def pairedFrom (env : Environment) (root : Name) (name : String) : Option Expr := Id.run do
  let some module := env.getModuleIdxFor? root | return none
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains n || env.getModuleIdxFor? n != some module then continue
    seen := seen.insert n
    let some value := (env.find? n).bind (·.value? (allowOpaque := true)) | continue
    if let some found := paired name value then return some found
    stack := stack ++ value.getUsedConstants
  return none

/-- The handler of `command`, looked up as `main` looks it up. -/
def handler (env : Environment) (command : String) : Option Expr :=
  (do pairedFrom env `DN.Printed.named (← command.dropPrefix? "emit-").toString) <|>
    pairedFrom env `DN.Compiler.Cli.table command

/-- The declarations of the library reachable from `roots` other than through the tables, theorems
left out, the code the compiler runs in place of a recursive one (`X._unsafe_rec`) included; sorted. -/
def reached (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let mut seen : NameSet := NameSet.empty.insert `DN.Compiler.Cli.table |>.insert `DN.Printed.named
  let mut out : Array Name := #[]
  let mut stack := roots
  while h : stack.size > 0 do
    let name := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[idx.toNat]!.getRoot == `DN do continue
    let some info := env.find? name | continue
    if info.isTheorem then continue
    out := out.push name
    stack := stack ++ dependencies info
    let rec' := name ++ `_unsafe_rec
    if env.contains rec' then stack := stack.push rec'
  return out.qsort Name.lt

structure Graph where
  /-- The line of each expression and level printed, by address: a shared one is printed once. -/
  ids : Std.HashMap USize Nat := {}
  decls : NameMap Nat := {}
  next : Nat := 0

abbrev M := StateT Graph IO

def line (tag : String) (fields : List Json) (children : List Nat) : M Nat := do
  IO.println (Json.arr #[tag, Json.arr fields.toArray, toJson children]).compress
  modifyGet fun g => (g.next, { g with next := g.next + 1 })

unsafe def shared (key : USize) (print : M Nat) : M Nat := do
  if let some i := (← get).ids.get? key then return i
  let i ← print
  modify fun g => { g with ids := g.ids.insert key i }
  return i

unsafe def level (l : Level) : M Nat := shared (ptrAddrUnsafe l) do
  match l with
  | .zero => line "z" [] []
  | .succ a => line "s" [] [← level a]
  | .max a b => line "m" [] [← level a, ← level b]
  | .imax a b => line "i" [] [← level a, ← level b]
  | .param n => line "p" [toString n] []
  | .mvar n => line "v" [toString n.name] []

unsafe def expr (e : Expr) : M Nat := shared (ptrAddrUnsafe e) do
  match e with
  | .bvar k => line "B" [toJson k] []
  | .fvar x => line "F" [toString x.name] []
  | .mvar x => line "V" [toString x.name] []
  | .sort l => line "S" [] [← level l]
  | .const n ls => line "C" [toString n] (← ls.mapM level)
  | .app f a => line "A" [] [← expr f, ← expr a]
  | .lam _ t b _ => line "L" [] [← expr t, ← expr b]
  | .forallE _ t b _ => line "P" [] [← expr t, ← expr b]
  | .letE _ t v b _ => line "T" [] [← expr t, ← expr v, ← expr b]
  | .lit (.natVal n) => line "N" [toString n] []
  | .lit (.strVal s) => line "Q" [s] []
  | .mdata d b => line "D" [toString d] [← expr b]
  | .proj s i b => line "J" [toString s, toJson i] [← expr b]

/-- What the compiler makes of a declaration besides its type and value. -/
def attributes (env : Environment) (n : Name) (info : ConstantInfo) : List Json :=
  let kind := match info with
    | .defnInfo v => s!"def {repr v.safety}"
    | .opaqueInfo v => s!"opaque {v.isUnsafe}"
    | .inductInfo _ => "inductive"
    | .ctorInfo v => s!"constructor {v.cidx}"
    | .recInfo _ => "recursor"
    | .axiomInfo _ => "axiom"
    | .quotInfo _ => "quotient"
    | .thmInfo _ => "theorem"
  let inline := match Compiler.getInlineAttribute? env n with
    | some .inline => "inline" | some .noinline => "noinline" | some .macroInline => "macro_inline"
    | some .inlineIfReduce => "inline_if_reduce" | some .alwaysInline => "always_inline" | none => ""
  [toString n, kind, inline, toJson (Compiler.hasSpecializeAttribute env n),
   toJson (Compiler.hasNospecializeAttribute env n), toJson (isNoncomputable env n),
   toJson info.levelParams.length]

/-- The compiled code of each module of the library, by name. -/
def compiledCode (env : Environment) : Std.HashMap Name IR.Decl := Id.run do
  let mut out := {}
  for h : idx in [0:env.header.moduleNames.size] do
    if env.header.moduleNames[idx].getRoot != `DN then continue
    for d in IR.declMapExt.getModuleEntries env idx ++ IR.declMapExt.getModuleIREntries env idx do
      out := out.insert d.name d
  return out

/-- The library's compiled code reachable from `roots`, the tables aside; sorted. -/
def compiledFrom (env : Environment) (code : Std.HashMap Name IR.Decl) (roots : Array Name) :
    Array Name := Id.run do
  let mut seen : NameSet := NameSet.empty.insert `DN.Compiler.Cli.table |>.insert `DN.Printed.named
  let mut out : Array Name := #[]
  let mut stack := roots
  while h : stack.size > 0 do
    let name := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some d := code.get? name | continue
    out := out.push name
    stack := stack ++ IR.collectUsedDecls env [d]
  return out.qsort Name.lt

unsafe def compiledLine (code : Std.HashMap Name IR.Decl) (n : Name) : M Nat := do
  if let some i := (← get).decls.find? n then return i
  let i ← line "I" [toString (format code[n]!)] []
  modify fun g => { g with decls := g.decls.insert n i }
  return i

unsafe def decl (env : Environment) (n : Name) : M Nat := do
  if let some i := (← get).decls.find? n then return i
  let some info := env.find? n | throw (IO.userError s!"no declaration {n}")
  let value ← match info.value? (allowOpaque := true) with
    | some v => pure [← expr v]
    | none => pure []
  let i ← line "d" (attributes env n info) ((← expr info.type) :: value)
  modify fun g => { g with decls := g.decls.insert n i }
  return i

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `DN.Compiler.Main }] {}
  let mut status : UInt32 := 0
  let mut graph : Graph := {}
  let code := compiledCode env
  for command in args do
    match handler env command with
    | some h =>
      let names := reached env (h.getUsedConstants.push `main)
      let compiled := compiledFrom env code names
      let ((), g) ← (do
          let hid ← expr h
          let ids ← names.toList.mapM (decl env)
          let codeIds ← compiled.toList.mapM (compiledLine code)
          discard <| line "c" [command] (hid :: ids ++ codeIds)).run graph
      graph := g
    | none =>
      IO.eprintln s!"no command {command}"
      status := 1
  return status
