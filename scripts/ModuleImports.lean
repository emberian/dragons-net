-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean

/-!
The modules each `.olean` imports, as its header records them and as `leanchecker` reads them:

  lean --run scripts/ModuleImports.lean FILE.olean...

prints a line for each file: the file, a tab, its imports separated by spaces.
-/

open Lean

def main (files : List String) : IO Unit := do
  for file in files do
    let (data, _) ← readModuleData file
    IO.println s!"{file}\t{" ".intercalate (data.imports.toList.map (·.module.toString))}"
