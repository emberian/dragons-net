-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean

/-!
Source gate for one module of the `DN` library. `scripts/check_structure.py` runs it for
every module, in import order, before `lake build`:

  lean --run scripts/SourceGate.lean --out DIR [--syntax] [--option NAME=VALUE]... FILE MODULE

Lean's own parser reads the module and every command is checked before any is elaborated,
so a command that breaks the rules never runs. The gate elaborates only what changes how
the rest parses: the scopes, the scoped syntax an `open` brings in, and every command of
the files passed with `--syntax`; the build elaborates the rest once every module passed.
Imports come from the toolchain and from DIR, where the gate writes each module it accepts,
with the names its declarations give, for the `open`s of the modules that import it.

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

/-- Commands that change how the rest of a module parses, elaborated as they come. -/
def scopeCommands : NameSet :=
  [``Parser.Command.namespace, ``Parser.Command.section, ``Parser.Command.end].foldl
    NameSet.insert {}

structure Rules where
  commands : Parser.SyntaxNodeKindSet
  attributes : Parser.SyntaxNodeKindSet
  syntaxAllowed : Bool
  /-- Names of declarations here and in the imports, each a namespace in the build only if a
  constant under it was made too. -/
  maybe : IO.Ref NameSet
  /-- Those of this module, for the modules that import it. -/
  own : IO.Ref NameSet

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

/-- Whether Lean registers namespaces under `n`: every part of it a string. -/
def isNamespaceName : Name → Bool
  | .str .anonymous _ => true
  | .str p _ => isNamespaceName p
  | _ => false

/-- The namespaces a constant named `name` makes, as Lean registers them on adding it: the prefixes
of its name, unless it is internal. -/
def namePrefixes (name : Name) : List Name :=
  match name with
  | .str _ s => if s.front == '_' then [] else go name
  | _ => []
where go
  | .str p _ => if isNamespaceName p then p :: go p else []
  | _ => []

/-- The names the declarations of `stx` give their constants in namespace `ns`; a private one's
makes no namespace. -/
partial def declared (ns : Name) (stx : Syntax) : Array Name :=
  match stx with
  | .node _ kind args =>
    if kind == ``Parser.Command.declaration &&
        (stx[0].find? (·.isOfKind ``Parser.Command.private)).isSome then #[]
    else if kind == ``Parser.Command.declId then
      let id := stx[0].getId
      #[if rootNamespace.isPrefixOf id then id.replacePrefix rootNamespace .anonymous else ns ++ id]
    else args.foldl (· ++ declared ns ·) #[]
  | _ => #[]

/-- Where Lean looks for the namespace `n` names from namespace `ns`, innermost first. -/
def scopeChain (ns n : Name) : List Name :=
  match ns with
  | .str p _ => (ns ++ n) :: scopeChain p n
  | _ => [n.replacePrefix rootNamespace .anonymous]

/-- What an `open` does to how the rest of the module parses, as Lean elaborates it: the scoped
syntax of the namespaces it opens, each one then resolving the next. The gate knows the namespaces
the build has but for one a declaration's own name makes, which it is only when a constant under it
was made too (`maybe`): an `open` that one of those could take from a namespace with syntax is
refused, the build and the gate parsing on with different syntax otherwise. -/
def openForParsing (maybe : NameSet) (decl : Syntax) : Command.CommandElabM Unit := do
  let resolved (id : Syntax) : Command.CommandElabM (List Name) := do
    let scope ← Command.getScope
    let env ← getEnv
    let chain := scopeChain scope.currNamespace id.getId
    if let some i := chain.findIdx? env.isNamespace then
      if (Parser.parserExtension.ext.getState env).scopedEntries.map.contains chain[i]! then
        if let some other := (chain.take i).find? maybe.contains then
          throwErrorAt id m!"`open {id.getId}` brings in the syntax of {chain[i]!}, and the build \
            may open {other} instead, which a declaration names: open it outside that namespace"
    return ResolveName.resolveNamespace env scope.currNamespace scope.openDecls id.getId
  let opened (ns : Name) (except : List Name) : Command.CommandElabM Unit := do
    activateScoped ns
    Command.modifyScope fun s => { s with openDecls := .simple ns except :: s.openDecls }
  match decl with
  | `(Parser.Command.openDecl| $nss*) =>
    for id in nss do
      for ns in ← resolved id do opened ns []
  | `(Parser.Command.openDecl| scoped $nss*) =>
    for id in nss do
      for ns in ← resolved id do activateScoped ns
  | `(Parser.Command.openDecl| $ns hiding $ids*) =>
    if let [n] ← resolved ns then opened n (ids.map (·.getId)).toList
  | _ => pure ()

/-- Parse and check commands until the end of the module, elaborating what changes how the rest
parses; `false` on failure. -/
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
  if r.syntaxAllowed || scopeCommands.contains cmd.getKind then
    elabCommandAtFrontend cmd
  else if cmd.getKind == ``Parser.Command.open then
    let maybe ← r.maybe.get
    runCommandElabM (Command.withLoggingExceptions (openForParsing maybe cmd[1]))
  else
    -- The namespaces the declarations will make in the build, for the `open`s after them.
    for name in declared scope.currNamespace cmd do
      runCommandElabM (modifyEnv fun env => (namePrefixes name).foldl Environment.registerNamespace env)
      if isNamespaceName name then
        r.maybe.modify (·.insert name)
        r.own.modify (·.insert name)
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
  let mut imported : NameSet := {}
  for m in env.header.moduleNames do
    let names := modToFilePath out m "names"
    if (`DN).isPrefixOf m && (← names.pathExists) then
      let some found := (Json.parse (← IO.FS.readFile names) >>= fromJson? (α := Array Name)).toOption
        | IO.eprintln s!"{names}: not the names the gate wrote"; return 1
      imported := found.foldl NameSet.insert imported
  let rules := { commands := kinds `command, attributes := kinds `attr,
                 syntaxAllowed := a.syntaxAllowed, maybe := ← IO.mkRef imported, own := ← IO.mkRef {} }
  let (ok, s) ← (processCommands rules { inputCtx := ctx }).run
    { commandState := Command.mkState env messages a.opts, parserState, cmdPos := parserState.pos }
  unless ok do return 1
  let olean := modToFilePath out module "olean"
  if let some dir := olean.parent then IO.FS.createDirAll dir
  writeModule s.commandState.env olean
  IO.FS.writeFile (modToFilePath out module "names") (toJson (← rules.own.get).toArray).compress
  return 0
