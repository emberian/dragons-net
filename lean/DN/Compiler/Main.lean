-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Baseline
import DN.Compiler.StateCorpus
import DN.Compiler.Precedence
import DN.Compiler.Gen
import DN.Compiler.GenCorpus
import DN.Dsl.Example
import DN.Printed
import DN.News.FrameModel

/-! `dn-compiler`: prints the checked native examples, the server's loop and the layout it shares
with its host, the differential fixtures, the programs and
precedence cells the parser contract compares, generated programs and their recorded cases, and
the corpus of stopping states. Printing is not a correctness certificate: see docs/assurance.md
for the remaining connections. -/

open DN.Compiler

private def commands : List String :=
  ["emit-region", "emit-echo", "emit-render", "emit-reply", "emit-skeleton", "emit-frame-line",
   "emit-frame-line-4", "emit-frame-block-64", "emit-frame-block-4", "frame-model", "emit-layout",
   "emit-reply-cases", "emit-baseline",
   "emit-trees", "emit-cells", "emit-fuzz SEED COUNT VECTORS", "run-fuzz", "fuzz-samples",
   "emit-corpus", "dump-states"]

private def usage : String := "dn-compiler {" ++ "|".intercalate commands ++ "}"

private def help : String :=
  "Emit checked native examples, differential fixtures, generated programs or the state corpus."

private def output (result : Except String String) : IO UInt32 :=
  match result with
  | .ok text => IO.print text *> pure 0
  | .error e => IO.eprintln ("error: " ++ e) *> pure 1

def main (args : List String) : IO UInt32 := do
  if let [command] := args then
    if let some (_, program) := DN.Printed.named.find? (command == "emit-" ++ ·.1) then
      return ← output (program.map (·.source))
  match args with
  | ["emit-layout"] => output (.ok DN.Server.Layout.header)
  | ["frame-model"] =>
    -- Framing cases on standard input, answered by the framers `DN.News.FramerCode` is proven to run.
    let input ← (← IO.getStdin).readToEnd
    output (DN.News.FrameModel.runAll input)
  | ["emit-reply-cases"] => output (.ok DN.Dsl.Example.cases.compress)
  | ["emit-baseline"] => output (Baseline.fixture.map (·.compress))
  | ["emit-trees"] =>
    output (DN.Printed.all.map fun ps => (Lean.Json.arr (ps.map (·.tree)).toArray).compress)
  | ["emit-cells"] => output (Precedence.cells.map (·.compress))
  | ["emit-fuzz", seed, count, vectors] =>
    match seed.toNat?, count.toNat?, vectors.toNat? with
    | some s, some c, some v =>
      if s < 2 ^ 64 then output ((Gen.batch (UInt64.ofNat s) c v).map (·.compress))
      else IO.eprintln "error: the seed is a 64-bit number" *> pure 2
    | _, _, _ => IO.eprintln "error: emit-fuzz SEED COUNT VECTORS takes three numbers" *> pure 2
  | ["run-fuzz"] =>
    -- Programs given as data on standard input, as the reducer and the corpus give them.
    let input ← (← IO.getStdin).readToEnd
    let answer : Except String Lean.Json := do Gen.replay (← Lean.Json.parse input)
    output (answer.map (·.compress))
  | ["fuzz-samples"] => output (.ok Gen.samples.compress)
  | ["emit-corpus"] => output (GenCorpus.json.map (·.compress))
  | ["dump-states"] =>
    -- The corpus of stopping states, with what the model makes of each case;
    -- `scripts/state_check.py` recomputes the same answers independently.
    IO.println StateCorpus.dump
    return 0
  | ["--help"] | [] =>
    IO.println usage
    IO.println help
    return 0
  | _ =>
    IO.eprintln ("usage: " ++ usage)
    return 2
