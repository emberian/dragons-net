# What the checks establish

We want strong claims about native behavior. The current evidence is deliberately separated so that useful partial work does not masquerade as a completed proof.

| Evidence | Establishes | Does not establish |
| --- | --- | --- |
| Lean kernel checking | Imported theorem statements follow from their definitions and allowed axioms | That definitions match NNTP, HOL, the host, or hardware |
| `DN.ProofAudit` and module inventory | All imported `DN` declarations have only allowed transitive axioms: `propext`, `Classical.choice`, `Quot.sound` | Nonvacuity, useful specifications, exhaustive theorem coverage outside `DN`, or runtime behavior |
| `Certificate.witness` | A packaged precondition has at least one satisfying model state | Adequacy for every real caller or correctness of the native adapter |
| 434 executable examples | Those closed computations return their expected values | Universal proofs |
| Rust unit tests | Selected host primitive behaviors, including stale-token and partial-write handling | Model refinement or OS integration |
| 25 Loom tests | Selected algorithms and counterexamples under bounded scheduling exploration | Every unbounded execution or the full native reactor |
| Native region check | Real generated machine code agrees with a C reference on 99,240 cases | A compiler theorem, full memory safety, or NNTP performance |
| Native differential and TCP checks | Recorded arithmetic/control cases agree across independent references; real connections exercise the generated copy kernel | General compiler preservation, a verified host, or optimized dataplane performance |
| Source and artifact digests | Identity of recorded bytes | Correctness or trustworthy bootstrap by themselves |

The current audit covers 7,022 declarations, including 2,982 theorem declarations and generated ones. It is a tripwire against unsound dependencies, not a measure of project completeness. The negative gate test deliberately introduces a foreign axiom into both a theorem and an isolated executable definition and checks rejection. The inventory gate detects a newly added module omitted from the audit.

The [inherited-code review](reviews/README.md) distinguishes fixed maintained-path defects from documented integration blockers. Corrected source comments now match these assurance boundaries.

## Open proof connections

1. **Semantics correspondence.** `DN.Compiler.Semantics` is a Lean transcription, not an automatically certified translation of the upstream HOL4 semantics. Agreement with the pinned backend remains an obligation.
2. **Source representation.** Model lowering, printed Pancake, and the backend parser need a general connection. The differential suite exercises 20,928 arithmetic/control cases across Python, the Lean model, and native execution. General preservation remains open.
3. **Backend identity.** The native lane uses the release pinned in `tools.lock.json`. The curated datacake patch applies to the older source pinned in `backend/lock.json`. Neither lane proves that the other artifact contains its changes. The patched HOL proof rebuild and compiler bootstrap have not yet been completed here.
4. **Native ABI and memory.** The pinned export trampoline returns 32 bits to C; full-word results now use output slots via `Abi.wordResult`. See [the baseline findings](baseline.md). The C adapter, heap/stack sizing, generated machine code, and memory model need an explicit contract. The current adapter provisions 1 MiB each for heap and stack; these are tested allocations, not proven minima.
5. **Host refinement.** The Rust primitives and preserved OS reactors are not connected by a refinement theorem to the Lean dataplane models. FFI and kernel behavior are assumptions to articulate, not erase.
6. **Protocol and persistence.** NNTP semantics, article parsing, durable acceptance, and crash recovery are not implemented. The CRLF theorem concerns a delimiter counter, not a bounded parser.

Inherited interfaces also deserve specification review. In particular, universal well-formedness conditions in `ProofProducing` are contradictory for the reviewed bound-local and memory-domain demonstrations on inhabited state types. `AssuranceChecks.lean` records that fact; these are not usable certificates. The new `Certificate` requires an inhabited precondition but does not retrofit every inherited proof. Fuel/clock bounds describe model execution, not elapsed CPU time.

## Reproducibility boundaries

The portable baseline pins Lean and Rust and uses locked Cargo dependencies. Linux CI obtains digest-pinned elan and CakeML release archives. The tool bootstrap trusts its local extracted cache after checking its archive marker; use a fresh checkout or a fresh `.deps/tools` directory when artifact provenance matters. It is not a hermetic build of every system dependency.

CI uploads logs, emitted source, assembly, and a native report with hashes. Benchmark results vary with CPU, OS, compiler, and workload. A local region-digest measurement is a kernel microbenchmark and must not be reported as news-server throughput.
