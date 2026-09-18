# What the checks establish

We want strong claims about native behavior. The current evidence is deliberately separated so that useful partial work does not masquerade as a completed proof.

| Evidence | Establishes | Does not establish |
| --- | --- | --- |
| Lean kernel checking | Imported theorem statements follow from their definitions and allowed axioms | That definitions match NNTP, HOL, the host, or hardware |
| `DN.ProofAudit` and module inventory | All imported `DN` theorem declarations have only allowed transitive axioms: `propext`, `Classical.choice`, `Quot.sound` | Nonvacuity, useful specifications, exhaustive theorem coverage outside `DN`, or runtime behavior |
| `Certificate.witness` | A packaged precondition has at least one satisfying model state | Adequacy for every real caller or correctness of the native adapter |
| 430 executable examples | Those closed computations return their expected values | Universal proofs |
| Rust unit tests | Selected host primitive behaviors, including stale-token and partial-write handling | Model refinement or OS integration |
| 25 Loom tests | Selected algorithms and counterexamples under bounded scheduling exploration | Every unbounded execution or the full native reactor |
| Native region check | Real generated machine code agrees with a C reference on 99,044 cases | A compiler theorem, full memory safety, or NNTP performance |
| Source and artifact digests | Identity of recorded bytes | Correctness or trustworthy bootstrap by themselves |

The current audit counts 2,966 theorem declarations, including generated ones. It is a tripwire against unsound dependencies, not a measure of project completeness. The negative gate test deliberately introduces a foreign axiom and checks rejection. The inventory gate detects a newly added module omitted from the audit.

## Open proof connections

1. **Semantics correspondence.** `DN.Compiler.Semantics` is a Lean transcription, not an automatically certified translation of the upstream HOL4 semantics. Agreement with the pinned backend remains an obligation.
2. **Source representation.** Model lowering, printed Pancake, and the backend parser need a general connection. Running a sample through the actual compiler tests one path through this boundary.
3. **Backend identity.** The native lane uses the release pinned in `tools.lock.json`. The curated datacake patch applies to the older source pinned in `backend/lock.json`. Neither lane proves that the other artifact contains its changes. The patched HOL proof rebuild and compiler bootstrap have not yet been completed here.
4. **Native ABI and memory.** The C adapter, heap/stack sizing, generated machine code, and memory model need an explicit contract. The current adapter provisions 1 MiB each for heap and stack; these are tested allocations, not proven minima.
5. **Host refinement.** The Rust primitives and preserved OS reactors are not connected by a refinement theorem to the Lean dataplane models. FFI and kernel behavior are assumptions to articulate, not erase.
6. **Protocol and persistence.** NNTP semantics, article parsing, durable acceptance, and crash recovery are not implemented. The CRLF theorem concerns a delimiter counter, not a bounded parser.

Inherited interfaces also deserve specification review. In particular, universal well-formedness conditions in `ProofProducing` can be too strong for programs requiring bound locals or valid memory. The new `Certificate` requires an inhabited precondition but does not retrofit every inherited proof. Fuel/clock bounds describe model execution, not elapsed CPU time.

## Reproducibility boundaries

The portable baseline pins Lean and Rust and uses locked Cargo dependencies. Linux CI obtains digest-pinned elan and CakeML release archives. The tool bootstrap trusts its local extracted cache after checking its archive marker; use a fresh checkout or a fresh `.deps/tools` directory when artifact provenance matters. It is not a hermetic build of every system dependency.

CI uploads logs, emitted source, assembly, and a native report with hashes. Benchmark results vary with CPU, OS, compiler, and workload. A local region-digest measurement is a kernel microbenchmark and must not be reported as news-server throughput.
