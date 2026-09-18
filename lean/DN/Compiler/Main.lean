import DN.Compiler.Lower

/-! Source emitter for the supported region example. Emission is not a binary
correctness certificate: see docs/assurance.md for the remaining connections. -/

open DN.Compiler.Syntax DN.Compiler.Lower

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit-region"] =>
    let program := emitExportFun { regionC0 with name := "dn_region" }
    if (lower program).isNone then
      IO.eprintln "error: example uses an unsupported construct"
      return 1
    IO.print (ppFun program)
    return 0
  | ["--help"] | [] =>
    IO.println "dn-compiler emit-region\nEmit the bounded region digest example as Pancake source."
    return 0
  | _ =>
    IO.eprintln "usage: dn-compiler emit-region"
    return 2
