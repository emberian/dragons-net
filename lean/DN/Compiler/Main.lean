-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Baseline
import DN.Compiler.StateCorpus
import DN.Compiler.Precedence
import DN.Compiler.Gen
import DN.Compiler.GenCorpus
import DN.Dsl.Example
import DN.Printed
import DN.News.FrameModel
import DN.News.SessionModel
import DN.News.AbnfModel
import DN.News.ArticleModel
import DN.News.JournalModel
import DN.News.RecoveryModel
import DN.News.FsCases
import DN.News.StoreCases
import DN.Compiler.Analyzer
import DN.Compiler.AnalyzerCertGen

/-! `dn-compiler`: prints the checked native examples, the server's loop and the layout it shares
with its host, runs the framing, grammar, article, journal, recovery, file system, store and session
models, prints the differential fixtures, the programs and precedence cells the parser contract
compares, generated programs and their recorded cases, and the corpus of stopping states. Printing
is not a correctness certificate: see docs/assurance.md for the remaining connections. -/

open DN.Compiler

private def commands : List String :=
  ["emit-region", "emit-echo", "emit-render", "emit-stamp", "emit-reply", "emit-skeleton", "emit-crc",
   "emit-sip", "emit-scan", "emit-recover", "emit-grammar", "emit-article", "emit-frame-line", "emit-frame-line-4",
   "emit-frame-block-64", "emit-frame-block-4",
   "frame-model",
   "session-model [--mutant NAME]", "abnf-model [--mutant NAME]", "article-model [--mutant NAME]",
   "journal-model [--mutant NAME]", "recovery-model [--mutant NAME]", "fs-model [--mutant NAME]",
   "store-model",
   "emit-layout", "emit-session", "emit-session-layout", "emit-scan-layout",
   "emit-recover-layout", "emit-grammar-layout", "emit-grammar-mutant NAME",
   "emit-article-layout", "emit-article-mutant NAME",
   "analyze-session", "analyze-recover", "analyze-grammar", "analysis-cert session|recover [BUDGET]",
   "emit-reply-cases", "emit-baseline",
   "emit-trees", "emit-cells", "emit-fuzz SEED COUNT VECTORS", "run-fuzz", "fuzz-samples",
   "emit-corpus", "dump-states"]

/-- The most lines `session-model` reads. -/
private def sessionLines : Nat := 100000000

/-- Turns on standard input, answered a line at a time by `DN.News.SessionSpec` or by one of its
mutants, so that a host simulator can decide each batch from the answers to the last. -/
private def sessionModel (mutant : DN.News.SessionMutant.Mutant) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut m : DN.News.SessionModel.Model := { mutant }
  for _ in [0:sessionLines] do
    let line ← stdin.getLine
    if line.isEmpty then
      if m.atRest then return 0
      IO.eprintln "error: the input ended inside a turn"
      return 2
    match DN.News.SessionModel.step m line.trimAsciiEnd.toString with
    | .error e =>
      IO.eprintln ("error: " ++ e)
      return 2
    | .ok (m', answer) =>
      m := m'
      unless answer.isEmpty do
        stdout.putStr answer
        stdout.flush
  IO.eprintln "error: more lines than the model reads"
  return 2

private def usage : String := "dn-compiler {" ++ "|".intercalate commands ++ "}"

private def help : String :=
  "Emit checked programs and layouts, run the framing, grammar, article, journal, recovery, " ++
    "file system, store and session models and the safety analysis, and print differential " ++
    "fixtures, generated programs or the state corpus."

/-- What the safety analysis says of a lowered `main`. -/
private def analyzed (size : Nat) : Option PancakeProg → Except String String
  | none => .error "the program does not lower"
  | some p => (Analyzer.check size p).map fun _ => "safe\n"

/-- How much of the analysis one declaration of a certificate's claims may cost
(`Analyzer.Gen.cost`). -/
private def certBudget : Nat := 150000

/-- How much the claims one declaration of a program's checks may cost together. -/
private def claimsBudget : Nat := 60000

private def sessionCert : Analyzer.Gen.ProgramTarget :=
  { module := "DN.Server.SessionCert", imports := ["DN.Server.Session"],
    functions := "DN.Server.Session.functions", program := "DN.Server.Session.main",
    size := "DN.Server.SessionLayout.size",
    doc := "The safety analysis of the session's program (decision 0004) in pieces: the claims " ++
      "of\n" ++
      "certificates of `DN.Compiler.AnalyzerCert`, of its functions together as their costs " ++
      "allow and\n" ++
      "of its `main` one declaration each." }

private def recoverCert : Analyzer.Gen.Target :=
  { module := "DN.News.RecoverCert", imports := ["DN.News.RecoverProg"],
    program := "DN.News.RecoverProg.analysisMain",
    size := "DN.News.RecoverProg.analysisAt + DN.News.RecoverProg.size",
    doc := "The safety analysis of recovery's step in a loop (`RecoverProg.analysisMain`) in\n" ++
      "pieces: the claims of a certificate of `DN.Compiler.AnalyzerCert`, one declaration each." }

private def output (result : Except String String) : IO UInt32 :=
  match result with
  | .ok text => IO.print text *> pure 0
  | .error e => IO.eprintln ("error: " ++ e) *> pure 1

private def usageError : IO UInt32 := IO.eprintln ("usage: " ++ usage) *> pure 2

private def noMutant (name : String) : IO UInt32 := IO.eprintln s!"error: no mutant {name}" *> pure 2

/-- A command of no arguments, which computes nothing until it is run. -/
private def plain (run : Unit → IO UInt32) : List String → IO UInt32
  | [] => run ()
  | _ => usageError

/-- What a model answers of the cases on standard input. -/
private def onInput (answer : String → Except String String) : IO UInt32 := do
  output (answer (← (← IO.getStdin).readToEnd))

namespace DN.Compiler.Cli

/-- Each command but the printed programs' and what runs it, given the arguments after it: a
command's handler is all of the library it reaches, which is what a check that ran it rests on. -/
def table : List (String × (List String → IO UInt32)) :=
  [("emit-layout", plain fun _ => (output (.ok DN.Server.Layout.header))),
   ("emit-session-layout", plain fun _ => (output (.ok DN.Server.SessionLayout.header))),
   ("emit-scan-layout", plain fun _ => (output (.ok DN.News.ScanProg.header))),
   ("emit-recover-layout", plain fun _ => (output (.ok DN.News.RecoverProg.header))),
   ("emit-grammar-layout", plain fun _ => (output (.ok DN.News.AbnfProg.header))),
   ("emit-grammar-mutant", fun
    | [name] => match DN.News.AbnfProg.mutantNames.lookup name with
      | some m => output ((DN.Printed.grammar m).map (·.source))
      | none => noMutant name
    | _ => usageError),
   ("emit-article-layout", plain fun _ => (output (.ok DN.News.ArticleProg.header))),
   ("emit-article-mutant", fun
    | [name] => match DN.News.ArticleProg.mutantNames.lookup name with
      | some m => output ((DN.Printed.article m).map (·.source))
      | none => noMutant name
    | _ => usageError),
   ("analyze-grammar", plain fun _ =>
    let (fs, f) := DN.News.AbnfProg.program
    output (match fs.mapM (fun g => (Lower.lower g).map (g.name, g.params.map (·.2), ·)),
        Lower.lower f with
      | some fns, some p => (Analyzer.checkProgram DN.News.AbnfProg.heapSize fns p).map fun _ => "safe\n"
      | _, _ => .error "the program does not lower")),
   ("analyze-recover", plain fun _ => (output (analyzed (DN.News.RecoverProg.analysisAt +
      DN.News.RecoverProg.size) (Lower.lower DN.News.RecoverProg.analysisMain)))),
   ("analysis-cert", fun
    | "session" :: rest =>
      let budget := (rest.head?.bind String.toNat?).getD certBudget
      let size := DN.Server.SessionLayout.size
      let fns := DN.Server.Session.functions.map fun g =>
        (g.name, g.params.map (·.2), (Lower.lower g).getD .skip)
      match Lower.lower DN.Server.Session.main with
      | some p => output ((Analyzer.Gen.certifyProgram size budget fns p).map fun (cs, k, _) =>
          Analyzer.Gen.renderProgram sessionCert size claimsBudget cs p k)
      | none => output (.error "the program does not lower")
    | what :: rest =>
      let budget := (rest.head?.bind String.toNat?).getD certBudget
      let target : Option (Analyzer.Gen.Target × Nat × Option PancakeProg) := match what with
        | "recover" => some (recoverCert,
            DN.News.RecoverProg.analysisAt + DN.News.RecoverProg.size,
            Lower.lower DN.News.RecoverProg.analysisMain)
        | _ => none
      match target with
      | some (t, size, some p) =>
        output ((Analyzer.Gen.certifyMain size budget p).map fun (k, _) =>
          Analyzer.Gen.render t size claimsBudget p k)
      | some (_, _, none) => output (.error "the program does not lower")
      | none => output (.error s!"no certificate for {what}")
    | [] => usageError),
   ("analyze-session", plain fun _ =>
    output (match DN.Server.Session.functions.mapM (fun g =>
        (Lower.lower g).map (g.name, g.params.map (·.2), ·)),
      Lower.lower DN.Server.Session.main with
      | some fns, some p =>
        (Analyzer.checkProgram DN.Server.SessionLayout.size fns p).map fun _ => "safe\n"
      | _, _ => .error "the program does not lower")),
   -- Framing cases, answered by the framers whose programs (`DN.News.FramerProg`)
   -- `DN.News.FramerCode` proves to make the same steps.
   ("frame-model", plain fun _ => (onInput DN.News.FrameModel.runAll)),
   -- Header field cases, answered by the grammar the RFCs give, or by a mutant of its interpreter.
   ("abnf-model", fun
    | [] => onInput (DN.News.AbnfModel.runAll .none)
    | ["--mutant", name] => match DN.News.AbnfMutant.names.lookup name with
      | some m => onInput (DN.News.AbnfModel.runAll m)
      | none => noMutant name
    | _ => usageError),
   -- Proto-articles, answered as a POST accepts them and what it adds.
   ("article-model", fun
    | [] => onInput (DN.News.ArticleModel.runAll DN.News.ArticleSpec.spec)
    | ["--mutant", name] => match DN.News.ArticleSpec.names.lookup name with
      | some m => onInput (DN.News.ArticleModel.runAll (DN.News.ArticleSpec.rulesOf m))
      | none => noMutant name
    | _ => usageError),
   -- Journals, records and names, read and written as the store does.
   ("journal-model", fun
    | [] => onInput (DN.News.JournalModel.runAll DN.News.Journal.spec)
    | ["--mutant", name] => match DN.News.Journal.names.lookup name with
      | some m => onInput (DN.News.JournalModel.runAll (DN.News.Journal.rulesOf m))
      | none => noMutant name
    | _ => usageError),
   -- Runs of the store's program on directories a crash left.
   ("store-model", plain fun _ => (onInput DN.News.StoreCases.runAll)),
   -- Operations on the file system and what a crash may leave.
   ("fs-model", fun
    | [] => onInput (DN.News.FsCases.runAll .none)
    | ["--mutant", name] => match DN.News.FsMutant.names.lookup name with
      | some m => onInput (DN.News.FsCases.runAll m)
      | none => noMutant name
    | _ => usageError),
   -- Directories, read as the store's recovery does.
   ("recovery-model", fun
    | [] => onInput (DN.News.RecoveryModel.runAll .none)
    | ["--mutant", name] => match DN.News.RecoveryMutant.names.lookup name with
      | some m => onInput (DN.News.RecoveryModel.runAll m)
      | none => noMutant name
    | _ => usageError),
   ("session-model", fun
    | [] => sessionModel .none
    | ["--mutant", name] => match DN.News.SessionMutant.names.lookup name with
      | some m => sessionModel m
      | none => noMutant name
    | _ => usageError),
   ("emit-reply-cases", plain fun _ => (output (.ok DN.Dsl.Example.cases.compress))),
   ("emit-baseline", plain fun _ => (output ((Baseline.fixture ()).map (·.compress)))),
   ("emit-trees", plain fun _ => (output ((DN.Printed.all ()).map fun ps =>
      (Lean.Json.arr (ps.map (·.tree)).toArray).compress))),
   ("emit-cells", plain fun _ => (output (Precedence.cells.map (·.compress)))),
   ("emit-fuzz", fun
    | [seed, count, vectors] =>
      match seed.toNat?, count.toNat?, vectors.toNat? with
      | some s, some c, some v =>
        if s < 2 ^ 64 then output ((Gen.batch (UInt64.ofNat s) c v).map (·.compress))
        else IO.eprintln "error: the seed is a 64-bit number" *> pure 2
      | _, _, _ => IO.eprintln "error: emit-fuzz SEED COUNT VECTORS takes three numbers" *> pure 2
    | _ => usageError),
   -- Programs given as data, as the reducer and the corpus give them.
   ("run-fuzz", plain fun _ => (onInput fun input => do
      let answer ← Gen.replay (← Lean.Json.parse input)
      return answer.compress)),
   ("fuzz-samples", plain fun _ => (output (.ok Gen.samples.compress))),
   ("emit-corpus", plain fun _ => (output ((GenCorpus.json ()).map (·.compress)))),
   -- The corpus of stopping states, with what the model makes of each case;
   -- `scripts/state_check.py` recomputes the same answers independently.
   ("dump-states", plain fun _ => IO.println StateCorpus.dump *> pure 0)]

end DN.Compiler.Cli

def main (args : List String) : IO UInt32 := do
  if let [command] := args then
    if let some (_, program) := DN.Printed.named.find? (command == "emit-" ++ ·.1) then
      return ← output ((program ()).map (·.source))
  match args with
  | ["--help"] | [] =>
    IO.println usage
    IO.println help
    return 0
  | command :: rest =>
    match DN.Compiler.Cli.table.lookup command with
    | some run => run rest
    | none => usageError
