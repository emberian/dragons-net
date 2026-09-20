# Working on dn

Read README.md, docs/handoff.md, and docs/assurance.md before extending claims.
`dn` is the compiler/dataplane project. The adjacent `fn` directory is separate.

Run `bash scripts/check.sh` for the model and host baseline and
`bash scripts/lint.sh` for static checks (both Linux x86-64; they download or
build pinned tools). Lean is pinned and uses only its core libraries. Set
LEAN_NUM_THREADS (default 4); never start overlapping Lake builds in the same
build directory. No Mathlib or sibling checkout is needed.

Every module under lean/DN is audited by scripts/Audit.lean and re-checked by
leanchecker and by nanoda, an independent kernel. Code from lean/ must not be
able to act on the system while it is built: before the build,
scripts/SourceGate.lean parses each module with Lean and checks every command
before it is elaborated. It accepts only imports of DN modules and
Lean.Data.Json, fixed sets of commands, attributes and options, and syntax
definitions in files pinned by hash in scripts/check_structure.py; it rejects
unsafe code and terms that run code from the module, including tactic
configuration values. The gate is a tripwire, not a sandbox. Add named proofs
for general facts and executable regression cases for examples. Do not introduce
sorry, custom axioms, native_decide, build-time IO, or weaken a theorem to make
it green.
An inhabited precondition still needs review for semantic adequacy.

The emitted sources are pinned in tests/golden. If a change to the emitter is
intended, regenerate them with `.lake/build/bin/dn-compiler emit-region` and
`emit-echo`, and say in the commit why the output changed.

Read docs/baseline.md before modifying the maintained compiler subset.
Read docs/reviews/README.md before reusing inherited compiler or reactor code;
its unresolved identity/lifetime/contract obligations are not covered by green CI.
The native lane is Linux x86-64. Run bash scripts/check_all.sh for the complete
baseline, including differential compilation and actual TCP echo. It executes real generated code with no fallback.
The backend proof lane is separate and pinned in backend/lock.json. Never infer a
whole-program theorem from a successful compiler run, source digest, test, or
theorem about a hand-transcribed model.

`migration/dataplane` is source reference, not the dn binary. Preserve its original
bytes and hashes; port changes into active modules. Never run its old deployment
scripts against a user's machines. Source projects are read-only ancestors.

Do not commit `.deps`, `.lake`, target directories, credentials, or generated
binaries. Keep attribution/provenance when moving source. Prefer small coherent
commits on main; do not rewrite existing history. Do not contact contributors.
