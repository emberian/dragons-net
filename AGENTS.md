# Working on dn

Read README.md, docs/handoff.md, and docs/assurance.md before extending claims.
`dn` is the compiler/dataplane project. The adjacent `fn` directory is separate.

Run `bash scripts/check.sh` for the portable baseline. Lean is pinned and uses
only its core libraries. Set LEAN_NUM_THREADS (default 4); never start overlapping
Lake builds in the same build directory. No Mathlib or sibling checkout is needed.

Every lean/DN module belongs in DN/Audit.lean. The structure gate checks coverage;
the Lean command checks transitive theorem axioms. Add named proofs for general
facts and executable regression cases for examples. Do not introduce sorry,
custom axioms, native_decide, build-time IO, or weaken a theorem to make it green.
An inhabited precondition still needs review for semantic adequacy.

The native lane is Linux x86-64. It executes real generated code with no fallback.
The backend proof lane is separate and pinned in backend/lock.json. Never infer a
whole-program theorem from a successful compiler run, source digest, test, or
theorem about a hand-transcribed model.

`migration/dataplane` is source reference, not the dn binary. Preserve its original
bytes and hashes; port changes into active modules. Never run its old deployment
scripts against a user's machines. Source projects are read-only ancestors.

Do not commit `.deps`, `.lake`, target directories, credentials, or generated
binaries. Keep attribution/provenance when moving source. Prefer small coherent
commits on main; do not rewrite existing history. Do not contact contributors.
