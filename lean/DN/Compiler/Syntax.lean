-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.Syntax

Adapted from the compiler extraction recorded in docs/provenance.json.
These definitions and theorems concern the Lean model. Correspondence to the
HOL4 backend, pretty-printer/parser, ABI and executable is tracked separately
in docs/assurance.md. The model is a restricted 64-bit Pancake fragment.
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
  SysV-ABI entry: named word/pointer params, a returned word, no `@base`/FFI/
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
taking its arguments in `rdi/rsi/rdx/rcx`. -/

/-- Emit the region decision as a C-callable exported function, driven by `rs`.
Params (all one word — SysV `rdi/rsi/rdx/rcx`): `ctrl` = control-block pointer the
bounds words `alen`/`off` are read from; `buf` = arena-bytes pointer; `len` = the
view length (passed directly, not loaded); `out` = result-word pointer written
before return. The body is C0's bounds branch + rolling digest fold — the same
decision `emitRegion` emits; only the plumbing (params/return instead of FFI)
differs. -/
def emitExportFun (rs : RegionSpec) : PFun :=
  { name := rs.name, exported := true,
    params := [(1, "ctrl"), (1, "buf"), (1, "len"), (1, "out")], body :=
    [ .dec "alen" (.loadw 1 (atOff (v "ctrl") rs.lenOff))
    , .dec "off"  (.loadw 1 (atOff (v "ctrl") rs.offViewOff))
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
    , .store (v "out") (v "result")
    , .ret (v "result") ] }

/-- The canonical exported region stage: C0's decision as a linkable
`export fun boundscan(...)`. -/
def boundscanExport : PFun := emitExportFun { regionC0 with name := "boundscan" }


end DN.Compiler.Syntax
