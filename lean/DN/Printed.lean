-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Baseline
import DN.Compiler.Canon
import DN.Compiler.Kernels
import DN.Dsl.Example
import DN.Server.Skeleton
import DN.Server.Session
import DN.News.FramerProg
import DN.News.CrcProg

/-!
# DN.Printed

Every program `dn-compiler` prints, with the canonical tree of its lowering, for
`scripts/parser_contract.py` to hold against the tree CakeML's parser builds from the source. The
commands that print one program take it from here, so no program is printed that the contract
does not see.
-/

namespace DN.Printed

open DN.Compiler DN.Compiler.Syntax

/-- A printed program: its source, and the canonical tree of its lowering, which carries the
source too. -/
structure Program where
  source : String
  tree : Lean.Json

/-- A function as the given gate prints it. -/
def checkedBy (gate : PFun → Except Checked.Reason String) (f : PFun) : Except String Program := do
  let source ← (gate f).mapError Checked.Reason.message
  return ⟨source, ← Canon.program f source⟩

/-- An exported function as the gate prints it. -/
def checked (f : PFun) : Except String Program := checkedBy Checked.emit f

/-- A differential fixture, through the output-slot rewrite, as the native lane compiles it. -/
def word (f : PFun) : Except String Program := do
  let source ← (Abi.emitWord f).mapError Checked.Reason.message
  return ⟨source, ← Canon.program (Abi.wordResult f) source⟩

/-- The region kernel. -/
def region : PFun := emitExportFun { regionC0 with name := "dn_region" }

/-- The reply table of the language. -/
def reply : Except String Program := do
  let source ← Dsl.emit Dsl.Example.name Dsl.Example.replies
  return ⟨source, ← Canon.program (Dsl.respond Dsl.Example.name Dsl.Example.replies) source⟩

/-- The server's loop, a whole program that reaches its host through two external calls. -/
def skeleton : Except String Program :=
  checkedBy (Checked.emitMain [Server.Layout.nextName, Server.Layout.emitName]) Server.Skeleton.main

/-- The NNTP session, a whole program that reaches its host through two external calls. -/
def session : Except String Program :=
  checkedBy (Checked.emitMain [Server.SessionLayout.nextName, Server.SessionLayout.emitName])
    Server.Session.main

/-- The framers: command lines of at most 512 octets, as the session reads them, and of at most
four, for the lane's exhaustive run; blocks for a buffer of 64 bytes and of four. The buffer the
store needs is set by the store; the framing is proven for every size below 2^62. -/
def framers : List (String × Except String Program) :=
  [("frame-line", checked (News.FramerProg.frameLine "dn_frame_line" 512)),
   ("frame-line-4", checked (News.FramerProg.frameLine "dn_frame_line_4" 4)),
   ("frame-block-64", checked (News.FramerProg.frameBlock "dn_frame_block_64" 64)),
   ("frame-block-4", checked (News.FramerProg.frameBlock "dn_frame_block_4" 4))]

/-- The programs `emit-NAME` prints, by name. -/
def named : List (String × Except String Program) :=
  [("region", checked region), ("echo", checked Kernels.echo), ("render", checked Kernels.render),
   ("reply", reply), ("skeleton", skeleton), ("session", session),
   ("crc", checked News.CrcProg.crcKernel)] ++ framers

/-- Every program the compiler prints: the named ones, one accepted function per rule of the
gate, and the differential fixtures. -/
def all : Except String (List Program) := do
  let fixtures := Baseline.functions ++ [Baseline.control, Baseline.control2] ++
    Baseline.nestedFunctions
  return (← named.mapM (·.2)) ++
    (← Checked.catalog.mapM fun (c : Checked.RuleCase) => checkedBy c.gate c.accepted) ++
    (← fixtures.mapM word)

end DN.Printed
