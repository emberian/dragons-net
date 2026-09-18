import Lean

/-! A build-failing transitive axiom audit over every imported DN declaration.
This does not prove that a theorem's specification is adequate. -/

open Lean Elab Command

syntax "#audit_dn" : command

elab_rules : command
  | `(#audit_dn) => do
    let env ← getEnv
    let mut count := 0
    let mut declarations := 0
    for (name, info) in env.constants.toList do
      if (`DN).isPrefixOf name then
        match info with
        | .axiomInfo _ => throwError "DN audit: project axiom {name} is forbidden"
        | .thmInfo _ => count := count + 1
        | _ => pure ()
        let axioms ← collectAxioms name
        let extra := axioms.filter fun a =>
          ![``propext, ``Classical.choice, ``Quot.sound].contains a
        unless extra.isEmpty do
          throwError "DN audit: unapproved axioms in {name}: {extra}"
        declarations := declarations + 1
    if count == 0 then throwError "DN audit: no project theorems imported"
    logInfo m!"DN audit: {declarations} declarations including {count} theorems checked; only standard kernel axioms permitted"
