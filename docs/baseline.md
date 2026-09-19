# Wisper’s compiler baseline

The compiler has a useful, executable core. It also has a large inherited body of model proofs and examples whose names can suggest more integration than exists. Treat those as two different levels of evidence. The maintained baseline now exercises real code generation, a documented C ABI, and a small TCP service; it is not a certification of every inherited compiler feature.

The follow-up [four-reviewer audit and triage](reviews/README.md) fixes a nested-load printer bug and CI failure-propagation hole, and identifies concrete inherited contracts and lifecycle gaps. Read it before extending or porting the preserved modules.

## Reproduce the baseline

On Linux x86-64, install the prerequisites from the root README, then run:

```sh
bash scripts/check_all.sh
```

This command fails if any required lane fails. It does not skip native tests on unsupported hosts. `bash scripts/check.sh` remains the portable model/host baseline. CI runs the same constituent lanes and uploads source, assembly, logs, and JSON reports. `build/native/report.json` and `build/baseline/report.json` identify the tested compiler and artifacts; failed native reruns remove stale reports.

The default native compiler is the digest-pinned release in `tools.lock.json`. Setting `CAKE` deliberately selects a different compiler, whose digest is recorded. Neither choice silently claims the separate patched HOL backend has been rebuilt.

## What is covered

| Check | Current coverage | Important limit |
| --- | --- | --- |
| Lean build, kernel re-check and proof audit | Every declaration defined in `lean/DN` modules, including private, top-level and executable ones; 7,426 declarations, including 3,255 theorems | Allowed axioms and type-correct statements do not ensure adequate specifications |
| Inherited examples | 434 executable cases | Examples, not proofs or a complete workload inventory |
| Arithmetic differential tests | 108 expression shapes × 192 input pairs, all seven current operators, both nestings of every operator pair, sign-bit boundaries, overflow, large literals | Deterministic bounded sampling, not an arbitrary-program theorem |
| Nested memory expressions | Four byte/word load nesting pairs checked by the real compiler; two inner-word cases also execute through valid native pointer cells, with independent/model expected values | Inner-byte absolute pointers are parser/model cases only |
| Control-flow differential tests | 192 cases: locals, branches, assignments, loops, and early return | One structured control workload |
| Three-way comparison | Independent Python arithmetic/control reference, Lean model, actual CakeML-compiled native code; 20,928 cases | Shared assumptions about the intended word semantics still need review |
| ABI adapter | Full-word output slots checked in the model and native execution, with native guard words | Output pointer alignment, writability, and disjointness are caller obligations |
| Region kernel | 99,240 native/reference comparisons, including 196 extreme-range cases; invalid inputs receive a protected buffer | Caller must report the real allocation length and supply valid control/output pointers |
| Copy kernel | 6,215 cases: byte offsets, lengths through 4 KiB, preserved surrounding bytes, protected pointers on rejection | Requires disjoint source/destination; not memmove |
| Test sensitivity | A separately compiled copy kernel with its store removed must fail the real copy test | One mutation family, not a mutation score for the whole project |
| TCP integration | Binary bytes, arbitrary application chunks, 4 KiB boundaries, a 512 KiB stream, eight concurrent clients, slow reads, half-close, reset, slot reuse, capacity admission, idle expiry | Reference `poll` adapter; no io_uring, TLS, persistence, or NNTP |
| Host/concurrency | Runtime unit tests and 25 bounded Loom tests | Abstract algorithms are not automatically the native host implementation |

Some inherited Lean files produce nonfatal style/unused-variable warnings. They are visible in CI; the baseline does not suppress them or treat a warning-free log as a correctness argument.

## Concrete findings fixed during baseline work

### Exported region bounds could overflow

The original guard compared `alen < off + len` using signed 64-bit words. For example, `off = 2^64 - 1` and `len = 1` wrap the sum to zero, allowing an invalid byte access. The former native tests exercised only small offsets and could not find it.

The exported function now rejects sign-bit-set sizes/offsets/lengths, requires `off <= alen`, and compares `len` with `alen - off`. Regressions exist in the executable Lean model and in the real native test with inaccessible memory. The historical FFI-oriented `emitRegion` example still has its original small-range caller assumptions; do not expose it as an unchecked native API.

### We assumed a 64-bit C return that the backend does not provide

The pinned x86-64 export trampoline uses `mov %edi, %eax` at `cake_return`. Our old C prototype claimed a 64-bit return. The existing digest fits in 24 bits and hid the problem; the new probe `0 + 2^32` returned zero to C despite computing the full word internally.

The native interfaces now declare a 32-bit result. `Abi.wordResult` rewrites value returns, including returns nested in control flow, to write a caller-owned word and return status zero. The model and native baseline check that transformation on all 109 fixture functions. The echo kernel returns only a bounded length (0–4096) or `UINT32_MAX`. This is an explicit adaptation to the backend ABI, not an assembly patch or a claimed upstream compiler fix.

### The theorem-only audit missed isolated definitions

An unapproved axiom inside a `DN` definition could previously escape if no audited theorem depended on it. The audit is now a standalone program that imports every module under `lean/DN` and checks every declaration they define; negative gate tests exercise this case among others.

### Raw printing and lowering were not an emission contract

`lower` intentionally handles a restricted model and ignores function-level ABI details. `ppFun` is a printer, not a validator. `Checked.emit` now checks scalar parameters, a conservative ASCII identifier/keyword policy, unique names, local scope, word-sized literals, allowed effects, and an explicit final return before CLI emission. Unsupported shapes, calls, and FFI are rejected in this exported profile. It does not establish memory safety, pointer validity, or termination.

## Which parts should Wisper trust enough to build on?

**Maintained native subset:** `Syntax`, `Lower`, `Checked`, `Abi`, `Kernels`, and the explicit paths in `Main`. Scalar 64-bit arithmetic uses modular add/subtract/multiply, bitwise AND, equality, and signed comparisons. Memory is supplied by the host. Whole-word results cross the C boundary through output slots. Start changes here and extend differential coverage with each new construct.

**Reusable model results:** `Semantics`, `Region`, `Clock`, `Bytes`, `ByteCopy`, `Certificate`, and the dataplane models. The emitted echo loop lowers definitionally to `ByteCopy.copyByteWhile`, the loop used by the existing copy proof. The wrapper/host/native path still needs a complete refinement argument. Clocks represent model fuel, not CPU time.

**Inherited research/compiler workloads:** `Stage*`, `Serve*`, serializers, structure emitters, and `ProofProducing`. They compile, participate in the axiom audit, and retain their examples. They do not all have native integration tests or useful inhabited caller contracts. The data-dependent universal-state well-formedness assumptions in `ProofProducing` have now been proved contradictory for states with an inhabited FFI type; the affected demonstrations are quarantined until the interface is indexed by useful preconditions. We have not reviewed every line of those modules.

**Preserved source:** `migration/dataplane` is still a reference snapshot. The echo host is new, small, and uses `poll`; it does not activate the old io_uring/kqueue product or prove correspondence to the abstract concurrency models.

## Next useful contributions

1. Expand differential fixtures with generated bounded ASTs, scope/shadowing cases, nested memory expressions, and explicit invalid-memory semantics. Keep seeds and minimized failures in the repository.
2. Turn `Abi.wordResult` and checked lowering into general preservation theorems under explicit, inhabited memory and scope contracts. Connect the Lean transcription to HOL semantics and the printer to the real parser.
3. Port one native reactor behind the same echo workload. Keep the reference host as a differential target; add real completion/cancellation and ownership tests before performance claims.
4. Replace the copy kernel with a bounded NNTP session step, starting with framing and discovery. Add the durable store before accepting articles.

The honest baseline claim is: **this maintained subset builds, rejects known unsupported inputs, agrees with independent references on the recorded suite, and drives a tested real TCP service.** There is no evidence yet for “the entire inherited compiler has few bugs”; the two boundary failures above are why this narrower, repeatable claim matters.
