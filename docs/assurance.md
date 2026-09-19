# What the checks establish

We want strong claims about native behavior. The current evidence is deliberately separated so that useful partial work does not masquerade as a completed proof.

| Evidence | Establishes | Does not establish |
| --- | --- | --- |
| Lean kernel checking | Imported theorem statements follow from their definitions and allowed axioms | That definitions match NNTP, HOL, the host, or hardware |
| `scripts/Audit.lean` and `leanchecker` | Every declaration defined in a `lean/DN` module is re-checked by the kernel, is not an axiom, `unsafe`, `partial`, `extern`, `export`, `implemented_by`, an initializer or a `csimp` theorem (Lean's own `_unsafe_rec` helpers for recursive definitions excepted), and depends only on `propext`, `Classical.choice` and `Quot.sound` | Nonvacuity, useful specifications, or runtime behavior |
| `Certificate.witness` | A packaged precondition has at least one satisfying model state | Adequacy for every real caller or correctness of the native adapter |
| 434 executable examples | Those closed computations return their expected values | Universal proofs |
| Rust unit tests | Selected host primitive behaviors, including stale-token and partial-write handling | Model refinement or OS integration |
| 25 Loom tests | Selected algorithms and counterexamples under bounded scheduling exploration | Every unbounded execution or the full native reactor |
| Native region check | Real generated machine code agrees with a C reference on 99,240 cases | A compiler theorem, full memory safety, or NNTP performance |
| Native differential and TCP checks | Recorded arithmetic/control cases agree across independent references; real connections exercise the generated copy kernel | General compiler preservation, a verified host, or optimized dataplane performance |
| Source and artifact digests | Identity of recorded bytes | Correctness or trustworthy bootstrap by themselves |

The current audit covers 7,426 declarations, including 3,255 theorems and generated ones. It is a tripwire against unsound dependencies, not a measure of project completeness. Gate tests compile probe modules containing a foreign, private or top-level axiom, an axiom reached only through a constructor, `sorry`, `native_decide`, `implemented_by`, `extern`, `export`, `csimp`, initializers, `partial`, `unsafe`, hand-written `_unsafe_rec` helpers, a failing, mistyped or non-executable regression, and a declaration added without kernel checking, and require each to be rejected.

Because the build precedes these checks, the source gate (`scripts/SourceGate.lean`) runs first. It parses every module with Lean's own parser, in import order, and checks each command before Lean elaborates it. Commands, attributes, options and imports are allow-listed; syntax definitions are accepted only in files pinned by hash; `by_elab`, `run_tac`, `include_str`, `idbg`, tactic configuration values (compiled as unsafe code) and `unsafe` code are refused. Lean still evaluates library code in some places, for example for `decide +native`, but only as safe definitions, which cannot use unsafe primitives. The rules were reviewed for Lean 4.30.0, and a different `lean-toolchain` fails the gate until they are reviewed again. The audit re-checks every module's imports from its compiled header. `scripts/check.sh` refuses to start when git tracks build outputs, such as `.lake`, compiled `.olean` files, Lake traces or `.pyc` files, which Lake and Python would otherwise trust. It builds without Lake's shared artifact cache and fails if any repository file changes during the gate or the build.

The source gate is a tripwire, not an isolation boundary. Building Lean code runs code, so a missed construct would run with the rights of the build; untrusted changes must be built and checked in an isolated environment without secrets or network access. CI does so: the build job has no secrets, builds without network and cannot regain root, and the kernel re-check and the audit's static checks run on a fresh machine from the build output before any built code is executed. These checks establish what the build produced; that the output corresponds to the sources still rests on the build running no code from the change. The checking scripts come from the change itself, so changes to scripts and workflows need review, and CI status is advisory unless the repository requires it for merges.

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

The portable baseline pins Lean and Rust and uses locked Cargo dependencies. `tools.lock.json` pins by digest the elan, Lean, CakeML and lint tool archives; CI links the verified Lean release into elan instead of letting elan download it, and installs the Python linters from hash-pinned wheels. The bootstrap verifies stored archives on every use but trusts its extracted cache after checking its archive marker; use a fresh checkout or a fresh `.deps/tools` directory when artifact provenance matters. It is not a hermetic build of every system dependency.

CI uploads logs, emitted source, assembly, and a native report with hashes. Benchmark results vary with CPU, OS, compiler, and workload. A local region-digest measurement is a kernel microbenchmark and must not be reported as news-server throughput.
