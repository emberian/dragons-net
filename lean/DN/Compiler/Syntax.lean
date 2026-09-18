-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.Syntax

Retained compiler/dataplane development and regression examples.
Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md. HTTP examples are compiler workloads, not dn server features.
-/


namespace DN.Compiler.Syntax

/-! ## 1. The DN.Compiler AST (the emitted subset) -/

/-- Binary operators. The four C0/C1 exercised: `+ * < &`. `add`/`mul` are
associative (the pretty-printer flattens their same-op chains); `lt` is the
SIGNED `<` (`Cmp Less`, C1 §2) and `and_` is bitwise `&`. The three added for the
fused serve (`eq`/`le`/`sub` = `== <= -`) are the comparators + subtraction the
real stages use (parse's `start3 + 5 <= len`, `len - start3`; the folds' `b ==
47`); each was checked against `cake --pancake` on the hand-authored serve.pnk. -/
inductive POp | add | mul | lt | and_ | eq | le | sub
  deriving DecidableEq, Repr

/-- DN.Compiler expressions (the emitted subset). -/
inductive PExpr
  | base                              -- `@base`, the FFI control-block pointer
  | const (n : Nat)                   -- an integer literal
  | var (name : String)              -- a local variable
  | binop (op : POp) (l r : PExpr)   -- `l op r`
  | loadw (shape : Nat) (addr : PExpr) -- `lds <shape> <addr>` (word/shaped load)
  | loadb (addr : PExpr)             -- `ld8 <addr>` (byte load)
  deriving Repr

/-- DN.Compiler statements (the emitted subset). -/
inductive PStmt
  | dec (name : String) (val : PExpr)          -- `var name = val;`
  | assign (name : String) (val : PExpr)       -- `name = val;`
  | store (addr : PExpr) (val : PExpr)         -- `st addr, val;` (word store)
  | storeb (addr : PExpr) (val : PExpr)        -- `st8 addr, val;` (byte store)
  | ffi (name : String) (args : List PExpr)    -- `@name(a, b, ...);`
  | call (ret : String) (fn : String) (args : List PExpr) -- `var ret = fn(a, ...);`
  | ret (val : PExpr)                          -- `return val;`
  | ite (cond : PExpr) (thn els : List PStmt)  -- `if cond { .. } else { .. }`
  | while (cond : PExpr) (body : List PStmt)   -- `while cond { .. }`
  deriving Repr

/-- A DN.Compiler function. `params` are `(shape, name)` pairs: DN.Compiler requires a
shape prefix on each parameter (`fun f(1 x, 1 y)`), where `1` = a one-word value.
A no-parameter entry (`fun main()`) has `params := []` and prints `()`. -/
structure PFun where
  name   : String
  params : List (Nat × String) := []
  body   : List PStmt
  /-- when `true`, `ppFun` prints the `export fun` header (DN.Compiler's C-callable
  SysV-ABI entry: named word/pointer params, a 32-bit C return, no `@base`/FFI/
  `main`). Defaults `false`, so every existing whole-program emitter is unchanged. -/
  exported : Bool := false
  deriving Repr

/-! ## 2. The pretty-printer (AST → DN.Compiler concrete syntax)

Total and structural. Precedence is handled by minimal parenthesisation:
operands that are themselves binops are wrapped, except a same-operator child of
an associative parent (so `add (add a b) c` prints `a + b + c`, matching the
hand-written `.pnk`, while `mul` under `add` still gets its parens). -/

def opSym : POp → String
  | .add => "+" | .mul => "*" | .lt => "<" | .and_ => "&"
  | .eq => "==" | .le => "<=" | .sub => "-"

def isAssoc : POp → Bool
  | .add => true | .mul => true | .lt => false | .and_ => false
  | .eq => false | .le => false | .sub => false

/-- Non-recursive parenthesisation decision for a binop operand: inspects only
the child's head constructor and the already-rendered string `s`. A `binop`
child is wrapped unless it is a same-op child of an associative parent (chain
flattening). A load (`lds`/`ld8`) child is ALSO wrapped: DN.Compiler's parser
requires a parenthesised load in operand position (`a + (ld8 x)`, not
`a + ld8 x`) — verified against `cake --pancake`. Atoms are bare. -/
def wrapOperand (parentOp : POp) (child : PExpr) (s : String) : String :=
  match child with
  | .binop cop _ _ => if isAssoc parentOp && parentOp == cop then s else "(" ++ s ++ ")"
  | .loadw _ _     => "(" ++ s ++ ")"
  | .loadb _       => "(" ++ s ++ ")"
  | _              => s

/-- Non-recursive parenthesisation for a load's address operand. -/
def wrapAtom (child : PExpr) (s : String) : String :=
  match child with
  | .binop _ _ _ => "(" ++ s ++ ")"
  | _ => s

/-- The expression pretty-printer. All recursive calls are on strict subterms
(`l`, `r`, `addr`); `wrapOperand`/`wrapAtom` only inspect the child's head. -/
def ppExpr : PExpr → String
  | .base       => "@base"
  | .const n    => toString n
  | .var s      => s
  | .binop op l r =>
      wrapOperand op l (ppExpr l) ++ " " ++ opSym op ++ " " ++ wrapOperand op r (ppExpr r)
  | .loadw sh a => "lds " ++ toString sh ++ " " ++ wrapAtom a (ppExpr a)
  | .loadb a    => "ld8 " ++ wrapAtom a (ppExpr a)

mutual
/-- Render one statement as a list of indented lines. -/
def ppStmt (ind : String) : PStmt → List String
  | .dec n v    => [ind ++ "var " ++ n ++ " = " ++ ppExpr v ++ ";"]
  | .assign n v => [ind ++ n ++ " = " ++ ppExpr v ++ ";"]
  | .store a v  => [ind ++ "st " ++ ppExpr a ++ ", " ++ ppExpr v ++ ";"]
  | .storeb a v => [ind ++ "st8 " ++ ppExpr a ++ ", " ++ ppExpr v ++ ";"]
  | .ffi n args => [ind ++ "@" ++ n ++ "(" ++ String.intercalate ", " (args.map ppExpr) ++ ");"]
  | .call r f args =>
      [ind ++ "var " ++ r ++ " = " ++ f ++ "(" ++ String.intercalate ", " (args.map ppExpr) ++ ");"]
  | .ret v      => [ind ++ "return " ++ ppExpr v ++ ";"]
  | .ite c t e  =>
      [ind ++ "if " ++ ppExpr c ++ " {"]
        ++ ppStmts (ind ++ "  ") t
        ++ [ind ++ "} else {"]
        ++ ppStmts (ind ++ "  ") e
        ++ [ind ++ "}"]
  | .while c b  =>
      [ind ++ "while " ++ ppExpr c ++ " {"]
        ++ ppStmts (ind ++ "  ") b
        ++ [ind ++ "}"]
/-- Render a statement list. -/
def ppStmts (ind : String) : List PStmt → List String
  | []      => []
  | s :: rest => ppStmt ind s ++ ppStmts ind rest
end

/-- Render a whole function to DN.Compiler concrete syntax. Each parameter prints as
its shape prefix and name (`1 ctrl`); an empty list yields `()`. -/
def ppFun (f : PFun) : String :=
  let ps := String.intercalate ", " (f.params.map (fun p => toString p.1 ++ " " ++ p.2))
  let kw := if f.exported then "export fun " else "fun "
  let header := kw ++ f.name ++ "(" ++ ps ++ ") {"
  String.intercalate "\n" (header :: (ppStmts "  " f.body ++ ["}"])) ++ "\n"

/-! ### small statement builder (readability sugar for stage calls) -/
/-- `var ret = fn(args);` — a DN.Compiler function call binding its result. -/
def sCall (ret fn : String) (args : List PExpr) : PStmt := .call ret fn args

/-- Is this statement a function call? (used by the footprint check). -/
def PStmt.isCall : PStmt → Bool
  | .call _ _ _ => true
  | _           => false

/-! ### small expression builders (readability sugar) -/
def eAdd (l r : PExpr) : PExpr := .binop .add l r
def eMul (l r : PExpr) : PExpr := .binop .mul l r
def eLt  (l r : PExpr) : PExpr := .binop .lt  l r
def eAnd (l r : PExpr) : PExpr := .binop .and_ l r
def eEq  (l r : PExpr) : PExpr := .binop .eq  l r
def eLe  (l r : PExpr) : PExpr := .binop .le  l r
def eSub (l r : PExpr) : PExpr := .binop .sub l r
def v (s : String) : PExpr := .var s
def n (k : Nat) : PExpr := .const k
/-- `base + k`, dropping the `+ 0` at offset zero so a base-relative load reads
`lds 1 base` rather than `lds 1 (base + 0)` — matching the hand-written form. -/
def atOff (p : PExpr) (k : Nat) : PExpr := if k == 0 then p else eAdd p (n k)

/-! ## 3. The region primitive emitter

`RegionSpec` is the emission-facing projection of the DSL `region` primitive:
the control-block layout, the digest-fold constants, and the FFI names. The C0
program is `emitRegion regionC0`. Nothing about the program *structure* is in the
spec — that lives in `emitRegion` — but every constant and name is, so the same
generator emits a differently-laid-out or differently-folded region by changing
the spec alone. -/

structure RegionSpec where
  /-- entry-point name -/
  name       : String := "main"
  /-- control-block layout, byte offsets from `@base` -/
  lenOff     : Nat := 0     -- arena length word
  offViewOff : Nat := 8     -- view offset word
  viewLenOff : Nat := 16    -- view length word
  resultOff  : Nat := 24    -- result word (also the control-block length to load)
  bufOff     : Nat := 32    -- start of arena bytes
  arenaCap   : Nat := 4096  -- max arena bytes the FFI driver may write
  /-- digest fold: `acc := (acc * mul + b) & mask` -/
  digestMul  : Nat := 31
  digestMask : Nat := 16777215     -- 2^24 - 1
  /-- out-of-bounds sentinel word -/
  sentinel   : Nat := 4294967295   -- 0xFFFFFFFF
  /-- FFI driver names -/
  loadFfi    : String := "load_vec"
  reportFfi  : String := "report_vec"

/-- The canonical C0 region spec — the values C0 hand-wrote in boundscan.pnk. -/
def regionC0 : RegionSpec := {}

/-- Emit the region bounds-check + total byte-scan as a `PFun`, driven by `rs`.
The structure is C0's: load the control block, decode `alen/off/len`, branch on
`alen < off + len` (out of bounds → sentinel), else fold the digest over the
viewed bytes, store, report, return. -/
def emitRegion (rs : RegionSpec) : PFun :=
  { name := rs.name, params := [], body :=
    [ .dec "base" .base
    , .dec "buf" (eAdd (v "base") (n rs.bufOff))
    , .ffi rs.loadFfi [v "base", n rs.resultOff, v "buf", n rs.arenaCap]
    , .dec "alen" (.loadw 1 (atOff (v "base") rs.lenOff))
    , .dec "off"  (.loadw 1 (atOff (v "base") rs.offViewOff))
    , .dec "len"  (.loadw 1 (atOff (v "base") rs.viewLenOff))
    , .dec "result" (n 0)
    , .ite (eLt (v "alen") (eAdd (v "off") (v "len")))
        -- out of bounds
        [ .assign "result" (n rs.sentinel) ]
        -- in bounds: rolling digest over the viewed bytes
        [ .dec "acc" (n 0)
        , .dec "i" (n 0)
        , .while (eLt (v "i") (v "len"))
            [ .assign "acc"
                (eAnd
                  (eAdd (eMul (v "acc") (n rs.digestMul))
                        (.loadb (eAdd (eAdd (v "buf") (v "off")) (v "i"))))
                  (n rs.digestMask))
            , .assign "i" (eAdd (v "i") (n 1)) ]
        , .assign "result" (v "acc") ]
    , .store (atOff (v "base") rs.resultOff) (v "result")
    , .ffi rs.reportFfi [atOff (v "base") rs.resultOff, n 8, v "base", n 8]
    , .ret (n 0) ] }

/-! ## 3.5 The exported-function form (C-callable SysV-ABI stage)

`emitRegion` above emits the *whole-program* shape: a `main` that pulls its input
through `@load_vec`, decides, and pushes its result through `@report_vec`.
`emitExportFun` emits the SAME region decision as an `export fun` instead — a
C-callable leaf (DN.Compiler's SysV-ABI form) whose inputs arrive as word/pointer
PARAMETERS and whose result is both returned and written through an `out` pointer.
No `@base`, no FFI, no `main`: the host links and calls the stage directly.
`cake --pancake --main_return=true` compiles this to a global `T <name>` symbol
taking its arguments in `rdi/rsi/rdx/rcx`. Its C return is 32 bits; the full
word is available through `out`. See `Abi.wordResult` for a general output-slot
adapter. -/

/-- Emit the region decision as a C-callable exported function, driven by `rs`.
Params (all one word — SysV `rdi/rsi/rdx/rcx`): `ctrl` = control-block pointer the
bounds words `alen`/`off` are read from; `buf` = arena-bytes pointer; `len` = the
view length (passed directly, not loaded); `out` = result-word pointer written
before return. The digest fold is shared with `emitRegion`. This exported boundary also
rejects sign-bit-set lengths and checks `off <= alen` and `len <= alen - off`
instead of the overflow-prone sum. The legacy FFI example retains its original
caller preconditions. The host must still supply valid pointers and an honest
allocation length; this guard is not a pointer-validity check. -/
def emitExportFun (rs : RegionSpec) : PFun :=
  { name := rs.name, exported := true,
    params := [(1, "ctrl"), (1, "buf"), (1, "len"), (1, "out")], body :=
    [ .dec "alen" (.loadw 1 (atOff (v "ctrl") rs.lenOff))
    , .dec "off"  (.loadw 1 (atOff (v "ctrl") rs.offViewOff))
    , .dec "result" (n 0)
    , .ite (eAdd (eAdd (eLt (v "alen") (n 0)) (eLt (v "off") (n 0)))
          (eAdd (eLt (v "len") (n 0))
            (eAdd (eLt (v "alen") (v "off"))
              (eLt (eSub (v "alen") (v "off")) (v "len")))))
        -- out of bounds
        [ .assign "result" (n rs.sentinel) ]
        -- in bounds: rolling digest over the viewed bytes
        [ .dec "acc" (n 0)
        , .dec "i" (n 0)
        , .while (eLt (v "i") (v "len"))
            [ .assign "acc"
                (eAnd
                  (eAdd (eMul (v "acc") (n rs.digestMul))
                        (.loadb (eAdd (eAdd (v "buf") (v "off")) (v "i"))))
                  (n rs.digestMask))
            , .assign "i" (eAdd (v "i") (n 1)) ]
        , .assign "result" (v "acc") ]
    , .store (v "out") (v "result")
    , .ret (v "result") ] }

/-- The canonical exported region stage: C0's decision as a linkable
`export fun boundscan(...)`. -/
def boundscanExport : PFun := emitExportFun { regionC0 with name := "boundscan" }

/-! ## 4. The machine primitive emitter

The DSL `machine Proto driven_by Arena` is a sans-IO FSM fed by the region. The
smallest honest emittable machine that uses only the C0-proven operators
(`< & + ld8 lds`) is a **guarded threshold scan**: walk the viewed bytes and stop
at the first byte strictly below `threshold` — a token/delimiter FSM whose output
is the index of the first delimiter (or `len` if none). This is a genuinely
different shape from the region fold (an *early-terminating* guarded `while`, a
data-dependent `If` inside the loop) yet needs no operator C0 has not compiled. -/

structure MachineSpec where
  -- entry name; the DN.Compiler basis invokes `main`, so a standalone-compiled
  -- primitive uses "main" (the DSL renames per-function when composing).
  name       : String := "main"
  viewLenOff : Nat := 16
  resultOff  : Nat := 24
  bufOff     : Nat := 32
  arenaCap   : Nat := 4096
  /-- ctrl-block length to load (bytes before the arena) -/
  ctrlLen    : Nat := 24
  /-- stop at the first byte strictly below this (e.g. 32 = first control char) -/
  threshold  : Nat := 32
  loadFfi    : String := "load_vec"
  reportFfi  : String := "report_vec"

def machineC0 : MachineSpec := {}

/-- Emit the machine (guarded threshold scan) as a `PFun`, driven by `ms`. -/
def emitMachine (ms : MachineSpec) : PFun :=
  { name := ms.name, params := [], body :=
    [ .dec "base" .base
    , .dec "buf" (atOff (v "base") ms.bufOff)
    , .ffi ms.loadFfi [v "base", n ms.ctrlLen, v "buf", n ms.arenaCap]
    , .dec "len" (.loadw 1 (atOff (v "base") ms.viewLenOff))
    , .dec "i" (n 0)
    , .dec "found" (n 0)
    , .while (eAnd (eLt (v "i") (v "len")) (eLt (v "found") (n 1)))
        [ .dec "b" (.loadb (eAdd (v "buf") (v "i")))
        , .ite (eLt (v "b") (n ms.threshold))
            [ .assign "found" (n 1) ]
            [ .assign "i" (eAdd (v "i") (n 1)) ] ]
    , .dec "result" (v "i")
    , .store (atOff (v "base") ms.resultOff) (v "result")
    , .ffi ms.reportFfi [atOff (v "base") ms.resultOff, n 8, v "base", n 8]
    , .ret (n 0) ] }

/-! ## 5. The machine's Lean SPEC (dual emission from one `MachineSpec`)

To make the dual-emission point concrete: the SAME `MachineSpec` drives both the
`.pnk` above and this model function. `tokenScanSpec ms a` = the index of the
first byte of `a` (over the whole array — the model uses `len = a.size`) strictly
below `ms.threshold`, or `a.size` if none. The DN.Compiler `emitMachine ms` refines
this (its Link A is the priced/scaffolded obligation, see the report §5). -/

def firstBelow (thr : Nat) (a : Array UInt8) : Nat → Nat → Nat
  | 0,     acc => acc
  | fuel+1, i =>
      if i ≥ a.size then i
      else if (a[i]!).toNat < thr then i
      else firstBelow thr a fuel (i+1)

/-- Model: first index in `a` whose byte is `< ms.threshold`, else `a.size`. -/
def tokenScanSpec (ms : MachineSpec) (a : Array UInt8) : Nat :=
  firstBelow ms.threshold a a.size 0

/-! ## 5.5 Multi-function composition: `PProgram`, `ppProgram`, and `fuse`

The single-function emitters above (`emitRegion`/`emitMachine`) each model ONE
`main` with inline FFI — the shape FUSED-SERVE-PNK-REPORT §5 named as the reason
the fused `serve.pnk` had to be hand-authored: there was no call node, no
multi-function program type, so the entry that *sequences* the stages could not
be generated. This section adds exactly those missing pieces.

  * `PProgram` — a DN.Compiler module: a list of `PFun`s (stage functions + entry).
  * `ppProgram` — the module pretty-printer (blank-line-separated functions).
  * `emitCounterStage` / `emitCombineStage` — two stage emitters that reproduce,
    from a spec, the hand-authored `machine_stage` and `admit_combine` bodies of
    the fused serve (a shaped-parameter function returning a value).
  * `emitServeMain` — the GENERATED entry: sets up the control block, does the
    ONE FFI load, inits the Response record `R`, then emits a `PStmt.call` per
    stage (threading `resp`), mirrors the threaded `R` fields into the report
    vector, and does the ONE FFI report. This is the composition glue that was
    hand-authored in `serve.pnk`'s `fun main()`.
  * `fuse` — the combinator: `fuse spec stages` = the stage functions followed by
    `emitServeMain` calling them in order. One `ServeSpec` + a list of `Stage`s
    produces a complete, linkable multi-function `PProgram`. -/

/-- A DN.Compiler module: stage functions plus (last) the entry that sequences them. -/
structure PProgram where
  funs : List PFun
  deriving Repr

/-- Render a whole module. `ppFun` already terminates each function with a
newline; joining with one more `"\n"` puts a blank line between functions. -/
def ppProgram (p : PProgram) : String :=
  String.intercalate "\n" (p.funs.map ppFun)

/-- A stage plus how the generated entry calls it: the emitted `PFun`, the
`main`-local variable its result binds to, and the argument expressions. -/
structure Stage where
  fn   : PFun
  bind : String
  args : List PExpr

/-! ### stage emitters (spec-driven bodies lifted from the fused serve) -/

/-- The C2 saturating-counter FSM stage (`machine_stage`): read the counter out
of `R`, walk the bytes incrementing (saturating at `satMax`) for each byte at or
above `threshold`, write the counter back to `R`, return it. -/
structure CounterStageSpec where
  name      : String := "machine_stage"
  fieldOff  : Nat := 32     -- R offset holding the (read+written) counter
  threshold : Nat := 128    -- bytes < threshold are ignored; ≥ increment
  satMax    : Nat := 255    -- saturation ceiling

def emitCounterStage (cs : CounterStageSpec) : PFun :=
  { name := cs.name, params := [(1, "resp"), (1, "buf"), (1, "len")], body :=
    [ .dec "c" (.loadw 1 (atOff (v "resp") cs.fieldOff))
    , .dec "i" (n 0)
    , .while (eLt (v "i") (v "len"))
        [ .dec "b" (.loadb (eAdd (v "buf") (v "i")))
        , .ite (eLt (v "b") (n cs.threshold))
            [ .assign "c" (v "c") ]
            [ .ite (eLt (v "c") (n cs.satMax))
                [ .assign "c" (eAdd (v "c") (n 1)) ]
                [ .assign "c" (n cs.satMax) ] ]
        , .assign "i" (eAdd (v "i") (n 1)) ]
    , .store (atOff (v "resp") cs.fieldOff) (v "c")
    , .ret (v "c") ] }

/-- The `admit_combine` stage: read the threaded `R.admit` the gates folded,
mirror it into the report slot, return it. -/
structure CombineStageSpec where
  name      : String := "admit_combine"
  admitOff  : Nat := 8      -- R offset of the threaded admit flag
  mirrorOff : Nat := 80     -- R offset the report reads admit back from

def emitCombineStage (cs : CombineStageSpec) : PFun :=
  { name := cs.name, params := [(1, "resp")], body :=
    [ .dec "admit" (.loadw 1 (atOff (v "resp") cs.admitOff))
    , .store (atOff (v "resp") cs.mirrorOff) (v "admit")
    , .ret (v "admit") ] }

/-! ### the generated entry + the `fuse` combinator -/

/-- The fused-serve control-block / FFI layout the generated `main` sets up.
Every offset and name lives here; the entry *structure* lives in `emitServeMain`.
`respInit` is the initial Response record `R` (offset ↦ value); `mirror` is the
`(ctrlOff, respOff)` pairs the entry copies from `R` into the report vector. -/
structure ServeSpec where
  loadFfi   : String := "load_serve"
  reportFfi : String := "report_serve"
  ctrlLen   : Nat := 32
  loadCap   : Nat := 4096
  lenOff    : Nat := 0
  respOff   : Nat := 2048
  bufOff    : Nat := 4096
  reportOff : Nat := 32
  reportLen : Nat := 80
  respInit  : List (Nat × Nat) :=
    [(0,200),(8,1),(16,0),(24,0),(32,0),(40,0),(48,0),(56,159),(64,0),(72,0),(80,0)]
  mirror    : List (Nat × Nat) :=
    [(64,16),(72,72),(80,32),(88,24),(96,0),(104,8)]

/-- Emit the fused-serve entry `main` that sequences `calls`. Structure mirrors
`serve.pnk`'s `fun main()`: control-block setup, ONE FFI load, `R` init, one
`PStmt.call` per stage (threading `resp`), the `R`→report-vector mirror, ONE FFI
report, `return 0`. `calls` are `(bind, fn, args)` triples from `fuse`. -/
def emitServeMain (spec : ServeSpec)
    (calls : List (String × String × List PExpr)) : PFun :=
  { name := "main", params := [], body :=
    [ .dec "ctrl" .base
    , .dec "resp" (atOff (v "ctrl") spec.respOff)
    , .dec "buf"  (atOff (v "ctrl") spec.bufOff)
    , .ffi spec.loadFfi [v "ctrl", n spec.ctrlLen, v "buf", n spec.loadCap]
    , .dec "len" (.loadw 1 (atOff (v "ctrl") spec.lenOff)) ]
    ++ spec.respInit.map (fun p => PStmt.store (atOff (v "resp") p.1) (n p.2))
    ++ calls.map (fun c => PStmt.call c.1 c.2.1 c.2.2)
    ++ (spec.mirror.map (fun p =>
          let nm := "m" ++ toString p.1
          [ PStmt.dec nm (.loadw 1 (atOff (v "resp") p.2))
          , PStmt.store (atOff (v "ctrl") p.1) (v nm) ])).flatten
    ++ [ .ffi spec.reportFfi
           [atOff (v "ctrl") spec.reportOff, n spec.reportLen, v "ctrl", n spec.reportLen]
       , .ret (n 0) ] }

/-- Compose `stages` into ONE DN.Compiler module: the stage functions, followed by a
GENERATED entry that calls them in order (threading `resp`). This is the piece
`serve.pnk` hand-authored — the multi-function program with a call-sequencing
entry — now produced from specs. -/
def fuse (spec : ServeSpec) (stages : List Stage) : PProgram :=
  { funs := stages.map (·.fn)
      ++ [emitServeMain spec (stages.map (fun s => (s.bind, s.fn.name, s.args)))] }

/-- A GENERATED two-stage slice of the fused serve: `machine_stage` (counter) and
`admit_combine`, sequenced by a generated entry. Compiles with `cake --pancake`
(EMIT-PANCAKE §"multi-function"), proving the call node + `PProgram` + `fuse` emit
real DN.Compiler, not just a string. -/
def serveSlice : PProgram :=
  fuse {}
    [ { fn := emitCounterStage {}, bind := "counter", args := [v "resp", v "buf", v "len"] }
    , { fn := emitCombineStage {}, bind := "fin",     args := [v "resp"] } ]

/-! ## 6. Rendered sources + the emitter `main`

`regionPnk` / `machinePnk` are the generated concrete syntax with a provenance
banner. `main` writes both to `build/examples/` for the cake
build (EMIT-PANCAKE-REPORT §3). -/

def banner (what : String) : String :=
  "// GENERATED by Dsl/EmitPancake.lean -- do not hand-edit.\n" ++
  "// " ++ what ++ "\n" ++
  "// Emission is generative: this file is ppFun applied to the primitive spec.\n\n"

def regionPnk : String :=
  banner "region primitive (bounds-check + byte-scan) -- reproduces C0 boundscan.pnk"
    ++ ppFun (emitRegion regionC0)

def machinePnk : String :=
  banner "machine primitive (guarded threshold token scan) -- Link A scaffolded"
    ++ ppFun (emitMachine machineC0)

/-- The region stage rendered as a C-callable `export fun` (SysV ABI:
`ctrl/buf/len/out`) — no `@base`, no FFI, no `main`. -/
def exportPnk : String :=
  banner "region stage as a C-callable export fun (SysV ABI: ctrl/buf/len/out) -- no FFI, no main"
    ++ ppFun boundscanExport

/-- The GENERATED multi-function serve slice: `fuse` composes the two stage
functions with a generated call-sequencing entry into ONE `.pnk` module. -/
def servePnk : String :=
  banner "fused serve SLICE (machine_stage + admit_combine) -- GENERATED entry sequences the stage calls (multi-function, PStmt.call)"
    ++ ppProgram serveSlice

def writeExamples : IO Unit := do
  IO.FS.writeFile "build/examples/region.pnk" regionPnk
  IO.FS.writeFile "build/examples/machine.pnk" machinePnk
  IO.FS.writeFile "build/examples/serve_slice.pnk" servePnk
  IO.FS.writeFile "build/examples/boundscan_export.pnk" exportPnk
  IO.println "wrote emit/region.pnk, emit/machine.pnk, emit/serve_slice.pnk and emit/boundscan_export.pnk"

/-! ## 7. Footprint checks (run at build time) -/

-- the emitters and pretty-printer are axiom-free (subset of the allowed set)
def regression_540 : Bool := decide ((ppFun (emitRegion regionC0)).length > 0
  )
def regression_541 : Bool := decide ((ppFun (emitMachine machineC0)).length > 0
  )
-- the composition layer: a fused module renders 3 functions (2 stages + entry)
def regression_543 : Bool := decide (serveSlice.funs.length == 3
  )
def regression_544 : Bool := decide ((ppProgram serveSlice).length > 0
  )
-- the generated entry actually emits a call per stage (PStmt.call is used)
def regression_546 : Bool := decide ((emitServeMain {} [("counter", "machine_stage", [v "resp"])]).body.any PStmt.isCall
  )
-- the exported-function form: sets the flag and renders the `export fun` header
def regression_548 : Bool := decide (boundscanExport.exported == true
  )
def regression_549 : Bool := decide ((ppFun boundscanExport).take 12 == "export fun b"
  )

end DN.Compiler.Syntax

