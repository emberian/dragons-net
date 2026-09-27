-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Kernels
import DN.Compiler.Baseline
import DN.Compiler.StateCorpus
import DN.Dsl.Example
import DN.Compiler.Canon
import DN.Compiler.Precedence

/-! Source emitter for the checked native examples. Emission is not a binary
correctness certificate: see docs/assurance.md for the remaining connections. -/

open DN.Compiler.Syntax DN.Compiler.Lower

private def output (result : Except String String) : IO UInt32 :=
  match result with
  | .ok text => IO.print text *> pure 0
  | .error e => IO.eprintln ("error: " ++ e) *> pure 1

/-- The region kernel, as `emit-region` prints it. -/
private def region : PFun := emitExportFun { regionC0 with name := "dn_region" }

/-- Every program this compiler prints, with the canonical tree of its lowering, for
`scripts/parser_contract.py` to hold against the tree CakeML's parser builds from the source. The
differential fixtures go through the output-slot rewrite, as the native lane compiles them; each
source is the text the command that prints it prints. -/
private def trees : Except String String := do
  let checked (f : PFun) : Except String Lean.Json := do
    DN.Compiler.Canon.program f (← (DN.Compiler.Checked.emit f).mapError DN.Compiler.Checked.Reason.message)
  let word (f : PFun) : Except String Lean.Json := do
    DN.Compiler.Canon.program (DN.Compiler.Abi.wordResult f)
      (← (DN.Compiler.Abi.emitWord f).mapError DN.Compiler.Checked.Reason.message)
  let plain := [region, DN.Compiler.Kernels.echo, DN.Compiler.Kernels.render] ++
    DN.Compiler.Checked.catalog.map (·.accepted)
  let reply ← DN.Compiler.Canon.program (DN.Dsl.respond DN.Dsl.Example.name DN.Dsl.Example.replies)
    (← DN.Dsl.emit DN.Dsl.Example.name DN.Dsl.Example.replies)
  let wrapped := DN.Compiler.Baseline.functions ++
    [DN.Compiler.Baseline.control, DN.Compiler.Baseline.control2] ++ DN.Compiler.Baseline.nestedFunctions
  return (Lean.Json.arr ((← plain.mapM checked) ++ [reply] ++ (← wrapped.mapM word)).toArray).compress

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit-region"] =>
    output ((DN.Compiler.Checked.emit region).mapError DN.Compiler.Checked.Reason.message)
  | ["emit-echo"] =>
    output ((DN.Compiler.Checked.emit DN.Compiler.Kernels.echo).mapError
      DN.Compiler.Checked.Reason.message)
  | ["emit-render"] =>
    output ((DN.Compiler.Checked.emit DN.Compiler.Kernels.render).mapError
      DN.Compiler.Checked.Reason.message)
  | ["emit-reply"] => output (DN.Dsl.emit DN.Dsl.Example.name DN.Dsl.Example.replies)
  | ["emit-reply-cases"] => output (.ok DN.Dsl.Example.cases.compress)
  | ["emit-baseline"] => output (DN.Compiler.Baseline.fixture.map (·.compress))
  | ["emit-trees"] => output trees
  | ["emit-cells"] => output (DN.Compiler.Precedence.cells.map (·.compress))
  | ["dump-states"] =>
    -- The corpus of stopping states, with what the model makes of each case;
    -- `scripts/state_check.py` recomputes the same answers independently.
    IO.println DN.Compiler.StateCorpus.dump
    return 0
  | ["--help"] | [] =>
    IO.println "dn-compiler {emit-region|emit-echo|emit-render|emit-reply|emit-reply-cases|emit-baseline|emit-trees|emit-cells|dump-states}\nEmit checked native examples, differential fixtures or the state corpus."
    return 0
  | _ =>
    IO.eprintln "usage: dn-compiler {emit-region|emit-echo|emit-render|emit-reply|emit-reply-cases|emit-baseline|emit-trees|emit-cells|dump-states}"
    return 2
