import Lean

/-! A build-failing transitive axiom audit over every imported DN theorem.
This does not prove that a theorem's specification is adequate. -/

open Lean Elab Command

syntax "#audit_dn" : command

elab_rules : command
  | `(#audit_dn) => do
    let env ← getEnv
    let mut count := 0
    for (name, info) in env.constants.toList do
      if (`DN).isPrefixOf name then
        match info with
        | .axiomInfo _ => throwError "DN audit: project axiom {name} is forbidden"
        | .thmInfo _ =>
          let axioms ← collectAxioms name
          let extra := axioms.filter fun a =>
            ![``propext, ``Classical.choice, ``Quot.sound].contains a
          unless extra.isEmpty do
            throwError "DN audit: unapproved axioms in {name}: {extra}"
          count := count + 1
        | _ => pure ()
    if count == 0 then throwError "DN audit: no project theorems imported"
    logInfo m!"DN audit: {count} theorems checked; only standard kernel axioms permitted"
