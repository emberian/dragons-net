-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean

/-!
The library modules a command of `dn-compiler` runs, after `lake build`:

  LEAN_PATH=<toolchain>/lib/lean:.lake/build/lib/lean lean --run scripts/Fingerprint.lean COMMAND...

For each command, one line: the command and the modules holding a declaration its handler reaches,
in `DN.Compiler.Cli.table` or, for a printed program's `emit-NAME`, in `DN.Printed.named`, and
`DN.Compiler.Main`, which picks the handler. A check
that ran the command rests on those modules' compiled files and no others of the library
(`scripts/once.py`); the toolchain and the build's options are the caller's to count. The audit
refuses `implemented_by`, `extern`, `csimp` and initializers in the library, so the declarations
reached are the code that runs.
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

/-- The modules of the library holding a declaration reachable from `roots`, the code the compiler
runs in place of a recursive one (`X._unsafe_rec`) included. -/
def modules (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut out : NameSet := NameSet.empty.insert `DN.Compiler.Main
  let mut stack := roots
  while h : stack.size > 0 do
    let name := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some idx := env.getModuleIdxFor? name | continue
    let module := env.header.moduleNames[idx.toNat]!
    unless module.getRoot == `DN do continue
    out := out.insert module
    let some info := env.find? name | continue
    stack := stack ++ dependencies info
    let rec' := name ++ `_unsafe_rec
    if env.contains rec' then stack := stack.push rec'
  return out

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

def roots (env : Environment) (command : String) : Option (Array Name) := do
  match pairedFrom env `DN.Compiler.Cli.table command with
  | some handler => return handler.getUsedConstants
  | none =>
    let printed ← command.dropPrefix? "emit-"
    let program ← pairedFrom env `DN.Printed.named printed.toString
    return program.getUsedConstants

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `DN.Compiler.Main }] {}
  let mut status : UInt32 := 0
  for command in args do
    match roots env command with
    | some names =>
      IO.println (" ".intercalate (command :: ((modules env names).toList.map toString).mergeSort))
    | none =>
      IO.eprintln s!"no command {command}"
      status := 1
  return status
