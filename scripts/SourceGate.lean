-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean

/-!
Source gate for one module of the `DN` library. `scripts/check_structure.py` runs it for
every module, in import order, before `lake build`:

  lean --run scripts/SourceGate.lean --out DIR [--syntax] [--option NAME=VALUE]... FILE MODULE

Lean's own parser reads the module and every command is checked before it is elaborated,
so a command that breaks the rules never runs. Imports come from the toolchain and from
DIR, where the gate writes each module it accepts.

The rules keep code written in the library from running while the library is built.
Commands, attributes, options and imports are allow-listed; syntax may be defined only in
files passed with `--syntax`; terms and tactics that evaluate code from the module, and
unsafe code, are refused. Lean still evaluates library code in some places, for example for
`decide +native`, but only as safe definitions, which cannot use primitives such as
`unsafeIO`. The gate is a tripwire, not a sandbox: check untrusted changes in isolation.
-/

open Lean Elab Frontend

def allowedImports : NameSet := [`Init, `Lean.Data.Json].foldl NameSet.insert {}

def allowedCommands : NameSet :=
  [``Parser.Command.declaration, ``Parser.Command.namespace, ``Parser.Command.section,
   ``Parser.Command.end, ``Parser.Command.open, ``Parser.Command.variable,
   ``Parser.Command.universe, ``Parser.Command.omit, ``Parser.Command.mutual,
   ``Parser.Command.moduleDoc,
   ``Parser.Command.set_option, ``Parser.Command.attribute, ``Parser.Command.in].foldl
    NameSet.insert {}

def syntaxCommands : NameSet :=
  [``Parser.Command.syntax, ``Parser.Command.macro, ``Parser.Command.macro_rules,
   ``Parser.Command.notation, ``Parser.Command.mixfix].foldl NameSet.insert {}

def allowedAttributes : NameSet := [`inline, `reducible, `irreducible].foldl NameSet.insert {}

def allowedOptions : NameSet := [`maxHeartbeats, `maxRecDepth].foldl NameSet.insert {}

def optionKinds : NameSet :=
  [``Parser.Command.set_option, ``Parser.Term.set_option, ``Parser.Tactic.set_option].foldl
    NameSet.insert {}

/-- Terms and tactics whose elaborators evaluate code taken from the module. Tactic
configuration values are compiled as unsafe code, so only `+option` and `-option` are left. -/
def codeRunners : NameSet :=
  [``Lean.byElab, ``Parser.Tactic.runTac, ``Lean.includeStr, ``Parser.Term.idbg,
   ``Parser.Term.doIdbg, ``Parser.Tactic.valConfigItem, ``Parser.Tactic.config].foldl
    NameSet.insert {}

def unsafeKinds : NameSet :=
  [``Parser.Command.«unsafe», ``Parser.Term.«unsafe»].foldl NameSet.insert {}

structure Rules where
  commands : Parser.SyntaxNodeKindSet
  attributes : Parser.SyntaxNodeKindSet
  syntaxAllowed : Bool

def headText (stx : Syntax) : String :=
  match stx[0] with
  | .ident _ _ name _ => name.toString
  | .atom _ val => val
  | _ => stx.getKind.toString

def nodeProblem (r : Rules) (stx : Syntax) (kind : SyntaxNodeKind) : Option String :=
  if r.commands.contains kind && !allowedCommands.contains kind then
    if !syntaxCommands.contains kind then some s!"command `{kind}` is not allowed"
    else if r.syntaxAllowed then none
    else some s!"syntax definition `{kind}` outside the reviewed syntax files"
  else if r.attributes.contains kind then
    if kind == ``Parser.Attr.simp || kind == ``Parser.Attr.simple &&
        allowedAttributes.contains stx[0].getId then none
    else some s!"attribute `{headText stx}` is not allowed"
  else if optionKinds.contains kind then
    if allowedOptions.contains stx[1].getId then none
    else some s!"option `{stx[1].getId}` is not allowed"
  else if codeRunners.contains kind then some s!"`{kind}` runs code from the module"
  else if unsafeKinds.contains kind then some "unsafe code is not allowed"
  else none

partial def problems (r : Rules) (stx : Syntax) : Array (Syntax × String) :=
  match stx with
  | .node _ kind args =>
    let here := match nodeProblem r stx kind with
      | some msg => #[(stx, msg)]
      | none => #[]
    args.foldl (· ++ problems r ·) here
  | _ => #[]

def report (ctx : Parser.InputContext) (items : Array (Syntax × String)) : IO Unit :=
  for (stx, msg) in items do
    let pos := ctx.fileMap.toPosition (stx.getPos?.getD 0)
    IO.println s!"{ctx.fileName}:{pos.line}:{pos.column}: {msg}"

def reportMessages (log : MessageLog) : IO Unit := do
  for m in log.reportedPlusUnreported.toList do
    if m.severity matches .error then IO.print (← m.toString)

/-- Parse, check and elaborate commands until the end of the module; `false` on failure. -/
partial def processCommands (r : Rules) : FrontendM Bool := do
  updateCmdPos
  let s ← getCommandState
  let scope := s.scopes.head!
  let pmctx := { env := s.env, options := scope.opts, currNamespace := scope.currNamespace,
                 openDecls := scope.openDecls }
  let ctx ← getInputContext
  let (cmd, ps, messages) := Parser.parseCommand ctx pmctx (← getParserState) s.messages
  setParserState ps
  setMessages messages
  if messages.hasErrors then
    reportMessages messages; return false
  let found := problems r cmd
  unless found.isEmpty do
    report ctx found; return false
  elabCommandAtFrontend cmd
  let messages := (← getCommandState).messages
  if messages.hasErrors then
    reportMessages messages; return false
  if Parser.isTerminalCommand cmd then return true
  processCommands r

structure Args where
  out : Option System.FilePath := none
  syntaxAllowed : Bool := false
  opts : Options := {}
  target : Option (System.FilePath × Name) := none

def parseOption (opts : Options) (arg : String) : Except String Options :=
  match arg.splitOn "=" with
  | [name, "true"] => .ok (opts.set name.toName true)
  | [name, "false"] => .ok (opts.set name.toName false)
  | [name, value] =>
    match value.toNat? with
    | some n => .ok (opts.set name.toName n)
    | none => .error s!"unsupported option value in {arg}"
  | _ => .error s!"--option expects NAME=VALUE, got {arg}"

def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--out" :: dir :: rest, a => parseArgs rest { a with out := some dir }
  | "--syntax" :: rest, a => parseArgs rest { a with syntaxAllowed := true }
  | "--option" :: arg :: rest, a => do parseArgs rest { a with opts := ← parseOption a.opts arg }
  | [file, module], a => .ok { a with target := some (file, module.toName) }
  | arg :: _, _ => .error s!"unexpected argument {arg}"

unsafe def main (args : List String) : IO UInt32 := do
  let a ← match parseArgs args {} with
    | .ok a => pure a
    | .error e => IO.eprintln e; return 2
  let (some out, some (file, module)) := (a.out, a.target)
    | IO.eprintln "usage: SourceGate --out DIR [--syntax] [--option NAME=VALUE]... FILE MODULE"
      return 2
  enableInitializersExecution
  searchPathRef.set (out :: (← getBuiltinSearchPath (← findSysroot)))
  let ctx := Parser.mkInputContext (← IO.FS.readFile file) file.toString
  let (header, parserState, messages) ← Parser.parseHeader ctx
  if messages.hasErrors then
    reportMessages messages; return 1
  let badImports := (HeaderSyntax.imports header (includeInit := false)).filterMap fun imp =>
    if allowedImports.contains imp.module || (`DN).isPrefixOf imp.module then none
    else some s!"import of {imp.module} is not allowed"
  unless badImports.isEmpty do
    report ctx (badImports.map (header.raw, ·)); return 1
  let (env, messages) ← processHeader header a.opts messages ctx (mainModule := module)
  if messages.hasErrors then
    reportMessages messages; return 1
  let categories := (Parser.parserExtension.getState env).categories
  let kinds cat := (Parser.getCategory categories cat).map (·.kinds) |>.getD {}
  let rules := { commands := kinds `command, attributes := kinds `attr,
                 syntaxAllowed := a.syntaxAllowed }
  let (ok, s) ← (processCommands rules { inputCtx := ctx }).run
    { commandState := Command.mkState env messages a.opts, parserState, cmdPos := parserState.pos }
  unless ok do return 1
  let olean := modToFilePath out module "olean"
  if let some dir := olean.parent then IO.FS.createDirAll dir
  writeModule s.commandState.env olean
  return 0
