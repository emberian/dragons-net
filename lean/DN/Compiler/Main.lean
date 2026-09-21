import DN.Compiler.Kernels
import DN.Compiler.Baseline

/-! Source emitter for the supported region example. Emission is not a binary
correctness certificate: see docs/assurance.md for the remaining connections. -/

open DN.Compiler.Syntax DN.Compiler.Lower

private def output (result : Except String String) : IO UInt32 :=
  match result with
  | .ok text => IO.print text *> pure 0
  | .error e => IO.eprintln ("error: " ++ e) *> pure 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit-region"] =>
    let program := emitExportFun { regionC0 with name := "dn_region" }
    output ((DN.Compiler.Checked.emit program).mapError DN.Compiler.Checked.Reason.message)
  | ["emit-echo"] =>
    output ((DN.Compiler.Checked.emit DN.Compiler.Kernels.echo).mapError
      DN.Compiler.Checked.Reason.message)
  | ["emit-baseline"] => output (DN.Compiler.Baseline.fixture.map (·.compress))
  | ["--help"] | [] =>
    IO.println "dn-compiler {emit-region|emit-echo|emit-baseline}\nEmit checked native examples or differential fixtures."
    return 0
  | _ =>
    IO.eprintln "usage: dn-compiler {emit-region|emit-echo|emit-baseline}"
    return 2
