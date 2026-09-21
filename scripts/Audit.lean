import Lean

/-!
Standalone proof audit for the `DN` library, run after `lake build`:

  LEAN_PATH=.lake/build/lib/lean lean --run scripts/Audit.lean --regressions N [--root DIR]...

Every `.lean` file under `<root>/DN` is imported, and every constant defined in those
modules (including private and top-level names) is checked. Axiom dependencies are
recomputed from declaration bodies; axiom summaries stored in `.olean` files are not
trusted. Initializers of imported modules are not executed. Kernel re-checking of the
same modules is done separately by `leanchecker`.

With `--export-list` instead of `--regressions N`, nothing is checked; the arguments that make
`lean4export` export the same declarations for an independent kernel are printed instead.
-/

open Lean

def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def discover (root : System.FilePath) : IO (Array Name) := do
  let dir := root / "DN"
  let files ← dir.walkDir
  files.filterMapM fun file => do
    if file.extension != some "lean" then return none
    let some rel := (file.withExtension "").toString.dropPrefix? (dir.toString ++ "/")
      | throw <| IO.userError s!"cannot name the module of {file}"
    return some <| rel.toString.splitOn "/" |>.foldl Name.mkStr `DN

def dependencies (info : ConstantInfo) : Array Name :=
  let body := match info.value? (allowOpaque := true) with
    | some value => value.getUsedConstants
    | none => #[]
  let extra := match info with
    | .inductInfo v => v.ctors.toArray
    | .recInfo v => v.rules.toArray.flatMap (·.rhs.getUsedConstants)
    | _ => #[]
  info.type.getUsedConstants ++ body ++ extra

/-- Constants reachable from `roots`, each with its direct dependencies. -/
def reachable (env : Environment) (roots : Array Name) : Std.HashMap Name (Array Name) := Id.run do
  let mut graph : Std.HashMap Name (Array Name) := {}
  let mut stack := roots
  while h : stack.size > 0 do
    let name := stack[stack.size - 1]
    stack := stack.pop
    unless graph.contains name do
      let deps := (env.find? name).map dependencies |>.getD #[]
      graph := graph.insert name deps
      stack := stack ++ deps.filter (!graph.contains ·)
  return graph

/-- Constants that reach an axiom outside `allowedAxioms`, by reverse propagation. -/
def tainted (env : Environment) (graph : Std.HashMap Name (Array Name)) : NameSet := Id.run do
  let mut users : Std.HashMap Name (Array Name) := {}
  for (name, deps) in graph do
    for dep in deps do
      users := users.insert dep ((users.getD dep #[]).push name)
  let mut seen : NameSet := {}
  let mut queue : Array Name := #[]
  for (name, _) in graph do
    if let some (.axiomInfo _) := env.find? name then
      unless allowedAxioms.contains name do
        seen := seen.insert name
        queue := queue.push name
  while h : queue.size > 0 do
    let name := queue[queue.size - 1]
    queue := queue.pop
    for user in users.getD name #[] do
      unless seen.contains user do
        seen := seen.insert user
        queue := queue.push user
  return seen

def forbiddenAxiomsOf (env : Environment) (graph : Std.HashMap Name (Array Name))
    (bad : NameSet) (root : Name) : Array Name := Id.run do
  let mut found : NameSet := {}
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while h : stack.size > 0 do
    let name := stack[stack.size - 1]
    stack := stack.pop
    unless seen.contains name do
      seen := seen.insert name
      if let some (.axiomInfo _) := env.find? name then
        unless allowedAxioms.contains name do found := found.insert name
      stack := stack ++ (graph.getD name #[]).filter bad.contains
  return found.toArray.qsort Name.lt

/-- The compiler runs `X._unsafe_rec`, when it exists, in place of `X`. Lean creates it with
`partial` safety for a recursive definition `X` of the same module, safe or `partial`; any
other constant with such a name could make compiled code differ from the checked body. -/
def isRecursionHelper (env : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  match Compiler.isUnsafeRecName? name, info with
  | some base, .defnInfo v =>
    v.safety == .partial && env.getModuleIdxFor? base == env.getModuleIdxFor? name &&
      match env.find? base with
      | some (.defnInfo b) => b.safety == .safe
      | some (.opaqueInfo _) => true
      | _ => false
  | _, _ => false

/-- A `partial def` is an opaque constant implemented by its recursion helper. -/
def isPartialDef (env : Environment) (name : Name) (info : ConstantInfo) : Bool :=
  info matches .opaqueInfo _ && env.contains (Compiler.mkUnsafeRecName name)

/-- The modules `dn-compiler` is built from. Pinned so that the executable compiler cannot
start depending on another module without that being reviewed. -/
def compilerModules : Array Name :=
  #[`DN.Compiler.Abi, `DN.Compiler.Baseline, `DN.Compiler.ByteCopy, `DN.Compiler.Bytes,
    `DN.Compiler.Checked, `DN.Compiler.Clock, `DN.Compiler.Decimal, `DN.Compiler.Div10,
    `DN.Compiler.Kernels, `DN.Compiler.Keywords, `DN.Compiler.Lower, `DN.Compiler.Main,
    `DN.Compiler.NatToDec, `DN.Compiler.Region, `DN.Compiler.Semantics, `DN.Compiler.Syntax]

/-- What `dn-compiler` imports, transitively, read from the compiled module headers. -/
def compilerClosure (env : Environment) (ours : NameSet) : NameSet := Id.run do
  let mut headers : Std.HashMap Name (Array Name) := {}
  for h : idx in [0:env.header.moduleNames.size] do
    headers := headers.insert env.header.moduleNames[idx]
      ((env.header.moduleData[idx]!).imports.map (·.module))
  let mut seen : NameSet := {}
  let mut stack := #[`DN.Compiler.Main]
  while h : stack.size > 0 do
    let name := stack[stack.size - 1]
    stack := stack.pop
    if ours.contains name && !seen.contains name then
      seen := seen.insert name
      stack := stack ++ (headers.getD name #[])
  return seen

/-- Direct imports a `DN` module may have besides other audited modules. -/
def allowedImports : NameSet :=
  [`Init, `Lean.Data.Json].foldl NameSet.insert {}

def isRegression (name : Name) : Bool :=
  match name with
  | .str _ s => s.startsWith "regression_"
  | _ => false

/-- `name` as `lean4export` reads it back with `Syntax.decodeNameLit`; `toString` does not
escape names with macro scopes. NUL separates the arguments. -/
def literal (name : Name) : Except String String :=
  let text := name.toStringWithSep "." true
  if !text.contains '\x00' && Syntax.decodeNameLit ("`" ++ text) == some name then .ok text
  else .error s!"cannot write the name {repr name}"

/-- `name` as nanoda matches it against its permitted axioms: components joined by dots, without
escapes, and no dot after an empty prefix. -/
def nanodaName : Name → String
  | .anonymous => ""
  | .str p s => join (nanodaName p) s
  | .num p n => join (nanodaName p) (toString n)
where
  join (pre part : String) : String := if pre.isEmpty then part else pre ++ "." ++ part

/-- Arguments for `lean4export`, each ended by NUL: the modules, `--`, and every declaration the
kernel checks, which is all but unsafe and `partial` ones. Refused if any other axiom would pass
for a permitted one in nanoda. -/
def printExportList (env : Environment) (modules : Array Name) (decls : Array (Name × ConstantInfo)) :
    IO UInt32 := do
  let mut errors := env.constants.fold (init := #[]) fun acc name info =>
    if info matches .axiomInfo _ && !allowedAxioms.contains name &&
        allowedAxioms.any (nanodaName · == nanodaName name) then
      acc.push s!"{name} reads to nanoda as the axiom {nanodaName name}"
    else acc
  let checked := decls.filterMap fun (name, info) =>
    if info.isUnsafe || info matches .defnInfo { safety := .partial, .. } then none else some name
  if checked.isEmpty then errors := errors.push "no declarations found"
  match modules.mapM literal, checked.mapM literal with
  | .ok modules, .ok names =>
    if errors.isEmpty then
      IO.print <| String.join <| (modules ++ #["--"] ++ names).toList.map (· ++ "\x00")
      return 0
  | .error e, _ | _, .error e => errors := errors.push e
  for e in errors do IO.eprintln s!"proof audit: {e}"
  return 1

structure Args where
  roots : Array System.FilePath := #[]
  regressions : Option Nat := none
  exportList : Bool := false

def parseArgs : List String → Args → Except String Args
  | [], o => .ok o
  | "--root" :: dir :: rest, o => parseArgs rest { o with roots := o.roots.push dir }
  | "--export-list" :: rest, o => parseArgs rest { o with exportList := true }
  | "--regressions" :: n :: rest, o =>
    match n.toNat? with
    | some k => parseArgs rest { o with regressions := some k }
    | none => .error s!"--regressions expects a number, got {n}"
  | [flag@"--root"], _ | [flag@"--regressions"], _ => .error s!"{flag} expects a value"
  | arg :: _, _ => .error s!"unknown argument {arg}"

unsafe def main (args : List String) : IO UInt32 := do
  let opts ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  if opts.exportList == opts.regressions.isSome then
    IO.eprintln "usage: Audit (--regressions N | --export-list) [--root DIR]..."
    return 2
  let expected := opts.regressions.getD 0
  let roots : Array System.FilePath := if opts.roots.isEmpty then #["lean"] else opts.roots
  let mut modules : Array Name := #[]
  for root in roots do
    modules := modules ++ (← discover root)
  if modules.isEmpty then
    IO.eprintln "proof audit: no modules found"; return 1
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map ({ module := · })) {}
  let ours : NameSet := modules.foldl NameSet.insert {}
  let inOurs (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some idx => ours.contains env.header.moduleNames[idx.toNat]!
    | none => false
  let decls := env.constants.fold
    (fun acc name info => if inOurs name then acc.push (name, info) else acc) #[]
  if opts.exportList then
    return ← printExportList env modules decls
  let graph := reachable env (decls.map (·.1))
  let bad := tainted env graph
  let mut errors : Array String := #[]
  if ours.contains `DN.Compiler.Main then
    let closure := compilerClosure env ours
    for name in compilerModules do
      unless closure.contains name do
        errors := errors.push s!"dn-compiler no longer needs {name}; update compilerModules"
    for name in closure.toList do
      unless compilerModules.contains name do
        errors := errors.push s!"dn-compiler now also needs {name}; review that and update compilerModules"
  for h : idx in [0:env.header.moduleNames.size] do
    let module := env.header.moduleNames[idx]
    if ours.contains module then
      let data := env.header.moduleData[idx]!
      for imp in data.imports do
        unless ours.contains imp.module || allowedImports.contains imp.module do
          errors := errors.push s!"{module} imports {imp.module}"
      -- The import keeps one copy of a theorem stored by several modules; the others are unchecked.
      for name in data.constNames, info in data.constants do
        if let some kept := env.find? name then
          unless info.isTheorem == kept.isTheorem && info.type == kept.type &&
              info.value? (allowOpaque := true) == kept.value? (allowOpaque := true) do
            errors := errors.push s!"{module} stores another version of {name}"
      -- Read from the module data: extension state is not loaded by this import.
      for entry in Compiler.CSimp.ext.ext.getModuleEntries env idx do
        let e := match entry with
          | .global e | .scoped _ e => e
        errors := errors.push s!"csimp theorem: {e.thmName}"
  let mut theorems := 0
  let mut regressions := 0
  let mut cases : Array Name := #[]
  for (name, info) in decls do
    if info matches .thmInfo _ then theorems := theorems + 1
    if info matches .axiomInfo _ then errors := errors.push s!"axiom declared: {name}"
    if (Compiler.isUnsafeRecName? name).isSome then
      unless isRecursionHelper env name info do
        errors := errors.push s!"hand-written recursion helper: {name}"
    else
      if info.isUnsafe then errors := errors.push s!"unsafe declaration: {name}"
      if isPartialDef env name info || info matches .defnInfo { safety := .partial, .. } then
        errors := errors.push s!"partial definition: {name}"
    if let some impl := Compiler.getImplementedBy? env name then
      errors := errors.push s!"implemented_by {impl}: {name}"
    if isExtern env name then errors := errors.push s!"extern declaration: {name}"
    if hasInitAttr env name || isIOUnitInitFn env name then
      errors := errors.push s!"initializer: {name}"
    if let some symbol := getExportNameFor? env name then
      errors := errors.push s!"export {symbol}: {name}"
    if bad.contains name && !(info matches .axiomInfo _) then
      let axioms := forbiddenAxiomsOf env graph bad name |>.toList.map toString
      errors := errors.push s!"{name} depends on {", ".intercalate axioms}"
    if isRegression name then
      match info with
      | .defnInfo v =>
        if v.type == mkConst ``Bool then cases := cases.push name
        else errors := errors.push s!"regression is not a Bool definition: {name}"
      | _ => errors := errors.push s!"regression is not a Bool definition: {name}"
  if theorems == 0 then errors := errors.push "no theorems found"
  -- Regressions execute library code, so they run only once the static checks pass.
  if errors.isEmpty then
    IO.println s!"proof audit: {modules.size} modules, {decls.size} declarations, \
      {theorems} theorems checked; allowed axioms: {", ".intercalate (allowedAxioms.toList.map toString)}"
    for name in cases do
      match env.evalConst Bool {} name (checkMeta := false) with
      | .ok true => regressions := regressions + 1
      | .ok false => errors := errors.push s!"regression failed: {name}"
      | .error e => errors := errors.push s!"regression could not run: {name}: {e}"
    if regressions != expected then
      errors := errors.push s!"expected {expected} passing regressions, found {regressions}"
  for e in errors.qsort (· < ·) do IO.eprintln s!"proof audit: {e}"
  if !errors.isEmpty then return 1
  IO.println s!"proof audit: {regressions} regressions passed"
  return 0
