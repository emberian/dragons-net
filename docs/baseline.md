# Wisper’s compiler baseline

The compiler has a useful, executable core: real code generation, a documented C ABI, and a small TCP service. The inherited workloads whose names suggested more integration than existed have been removed (see below); what is left is the emitted subset, its proofs and the dataplane models.

The follow-up [four-reviewer audit and triage](reviews/README.md) fixes a nested-load printer bug and CI failure-propagation hole, and identifies concrete inherited contracts and lifecycle gaps. Read it before extending or porting the preserved modules; the inherited compiler workloads it discusses were removed afterwards.

## Reproduce the baseline

On Linux x86-64, install the prerequisites from the root README, then run:

```sh
bash scripts/check_all.sh
```

This command fails if any required lane fails. It does not skip native tests on unsupported hosts. `bash scripts/check.sh` remains the model/host baseline without the native lanes, and `bash scripts/lint.sh` the static checks. CI runs the same lanes as one sequential chain (lint, build without network, proofs on a fresh machine, tests) and uploads source, assembly, logs, and JSON reports. `build/native/report.json` and `build/baseline/report.json` identify the tested compiler and artifacts; failed native reruns remove stale reports.

The default native compiler is the digest-pinned release in `tools.lock.json`. Setting `CAKE` deliberately selects a different compiler, whose digest is recorded. Neither choice silently claims the separate patched HOL backend has been rebuilt.

## What is covered

| Check | Current coverage | Important limit |
| --- | --- | --- |
| Lean build, kernel re-checks (Lean and nanoda) and proof audit | Every declaration defined in `lean/DN` modules, including private, top-level and executable ones; 4,790 declarations, including 2,258 theorems; the kernels skip the 57 `_unsafe_rec` helpers Lean generates | Allowed axioms and type-correct statements do not ensure adequate specifications |
| Executable examples | 91 executable cases | Examples, not proofs or a complete workload inventory |
| Arithmetic differential tests | 113 expression shapes × 192 input pairs, all seven current operators and the logical right shift at its boundaries, both nestings of every operator pair, sign-bit boundaries, overflow, large literals | Deterministic bounded sampling, not an arbitrary-program theorem |
| Nested memory expressions | Four byte/word load nesting pairs checked by the real compiler; two inner-word cases also execute through valid native pointer cells, with independent/model expected values | Inner-byte absolute pointers are parser/model cases only |
| Control-flow differential tests | 384 cases over two workloads: locals, branches, assignments, loops, early return, and returns in an `else` branch at the top level and inside a loop | Two structured control workloads |
| Three-way comparison | Independent Python arithmetic/control reference, Lean model, actual CakeML-compiled native code; 22,080 cases | Shared assumptions about the intended word semantics still need review |
| ABI adapter | Full-word output slots checked in the model and native execution, with native guard words | Output pointer alignment, writability, and disjointness are caller obligations |
| Region kernel | 99,240 native/reference comparisons, including 196 extreme-range cases; invalid inputs receive a protected buffer | Caller must report the real allocation length and supply valid control/output pointers |
| Decimal render | 976 numbers, including every power-of-two boundary and the whole-word maximum, checked against the C library's own conversion, with the bytes outside the digits required to stay untouched | The digit sequence lowers definitionally to the proven model; the saved start pointer, the returned count, and the host are not covered by that equality |
| Copy kernel | 24,869 cases: byte offsets, lengths through 4 KiB, four capacities per length (the length itself, one more, halfway to the buffer, and the whole buffer), preserved surrounding bytes, a page with no access right after the destination, protected pointers on rejection | Requires disjoint source/destination; not memmove |
| Stopping states | 97 cases, 95 of which stop — missing local, address outside the domain, timeout, return, external call ending the run, reply of the wrong length — compared field by field against an independent implementation of the same clauses, plus five write-back cases for the clause an external call cannot reach (`scripts/state_check.py`) | Two transcriptions agreeing is not a proof against the HOL source |
| Test sensitivity | A separately compiled copy kernel with its store removed must fail the real copy test | One mutation family, not a mutation score for the whole project |
| TCP integration | Binary bytes, arbitrary application chunks, 4 KiB boundaries, a 512 KiB stream, eight concurrent clients, slow reads, half-close, reset, slot reuse, capacity admission, idle expiry | Reference `poll` adapter; no io_uring, TLS, persistence, or NNTP |
| Host/concurrency | Runtime unit tests and 30 Loom tests, three of them driving the shipped admission gate itself; a recorded set of defects that the tests must catch (`scripts/mutate_rust.py`) | Loom checks the C11 model it implements, treats `SeqCst` accesses as `AcqRel` and does not model load buffering; the models of the historical reactor are not that reactor |

The Lean build carries no warnings, and `--wfail` makes one fail the build; Lake replays a module's stored log, so this holds on a warm cache as well as on a fresh checkout. A warning-free log is a hygiene property, not a correctness argument. `autoImplicit` is off, so a mistyped name is an error instead of a silent new variable.

## Concrete findings fixed during baseline work

### Exported region bounds could overflow

The original guard compared `alen < off + len` using signed 64-bit words. For example, `off = 2^64 - 1` and `len = 1` wrap the sum to zero, allowing an invalid byte access. The former native tests exercised only small offsets and could not find it.

The exported function now rejects sign-bit-set sizes/offsets/lengths, requires `off <= alen`, and compares `len` with `alen - off`. Regressions exist in the executable Lean model and in the real native test with inaccessible memory. The historical FFI-oriented `emitRegion` example still has its original small-range caller assumptions; do not expose it as an unchecked native API.

### We assumed a 64-bit C return that the backend does not provide

The pinned x86-64 export trampoline uses `mov %edi, %eax` at `cake_return`. Our old C prototype claimed a 64-bit return. The existing digest fits in 24 bits and hid the problem; the new probe `0 + 2^32` returned zero to C despite computing the full word internally.

The native interfaces now declare a 32-bit result. `Abi.wordResult` rewrites value returns, including returns nested in control flow, to write a caller-owned word and return status zero. The model and native baseline check that transformation on all 110 fixture functions. The echo kernel returns only a bounded length (0–4096) or `UINT32_MAX`. This is an explicit adaptation to the backend ABI, not an assembly patch or a claimed upstream compiler fix.

### The theorem-only audit missed isolated definitions

An unapproved axiom inside a `DN` definition could previously escape if no audited theorem depended on it. The audit is now a standalone program that imports every module under `lean/DN` and checks every declaration they define; negative gate tests exercise this case among others.

### Raw printing and lowering were not an emission contract

`lower` intentionally handles a restricted model and ignores function-level ABI details. `ppFun` is a printer, not a validator. `Checked.emit` checks scalar parameters, ASCII identifiers, keywords, unique names, local scope, word-sized literals, allowed effects, an exported name inside the `dn_` namespace, and an explicit final return before CLI emission. Each rule has its own refusal reason, and `Checked.catalog` carries a rejected/accepted pair per reason: a rule with no pair, or a pair refused by a different rule, fails the build. That an accepted function has a model image is proven (`Checked.accepted_lowers`), not checked at runtime. Unsupported shapes, calls, and FFI are rejected in this exported profile. It does not establish memory safety, pointer validity, or termination.

What the gate accepts, the compiler must accept silently: every accepted example of the catalog is compiled in the native lane and any diagnostic fails the build. The gate is not a copy of the compiler's own analyses, though. It does not reproduce the check that a store address is derived from a pointer the caller supplied, so a program storing through a literal address passes the gate and is then refused by the build for the compiler's warning rather than by the gate. Treat the diagnostics as the boundary of the profile, not the gate alone.

The keyword list is not written by hand: `scripts/gen_keywords.py` generates `DN.Compiler.Keywords` from `get_keyword_def` in the Pancake lexer of each pinned revision, the scheduled job regenerates it and fails on a difference, and the native lane checks the table against the compiler it actually runs — a word the table calls a keyword must be refused as a name, and a word it records only for the other revision must be accepted. Two details of the lexer matter to anyone writing `.pnk` by hand: `@base`, `@top` and `@biw` are keywords only with the `@` (and `@top` lexes to the same token as `@base`), and a leading digit in a declaration is read as a shape, so `var 1x = a;` silently declares `x`.

### Decimal rendering took time proportional to the number

The digit loop divided by ten by repeated subtraction, so rendering `m` cost about `m/10`
iterations: 238,609,298 of them for the largest article number RFC 3977 allows. Pancake has
no division and its multiplication yields only the low half of a product, so the quotient is
now built from two multiplications by `3435973837`, one per half of the word, with
`2^32 = 429496729 * 10 + 6` carrying the remainder between them (`DN.Compiler.Div10`). The
correspondence with division is proven for every machine word, and a separate theorem
states that no intermediate product overflows (`Div10.div10w_products_fit`), which is why
Pancake's truncating multiplication loses nothing here.

A digit now costs no clock at all — the model spends clock only in loops — so the render
spends one tick per digit after the first, and never more than nineteen for any machine
word (`NatToDec.natToDecProg_sem` with `renderFuel_le_nineteen`); two theorems run it on a
concrete state, for 404 and for zero. The same render is emitted as `dn_render` and run
natively against the C library's conversion. The model has the shape the emitter prints:
the working names are declared once, ahead of the loop, and assigned inside it, so the
emitted digit sequence lowers definitionally to the program the theorem runs
(`Kernels.render_body_lowering`, `Kernels.digit_loop_lowering`). What is still read rather
than proven is the rest of the emitted function — the saved start pointer and the returned
byte count — and the native host, as for the other kernels. The rendering specification and
its byte-level postcondition are the ones that were there before.

## Which parts should Wisper trust enough to build on?

**Maintained native subset:** `Syntax`, `Lower`, `Checked`, `Abi`, `Kernels`, and the explicit paths in `Main`. Scalar 64-bit arithmetic uses modular add/subtract/multiply, bitwise AND, equality, and signed comparisons. Memory is supplied by the host. Whole-word results cross the C boundary through output slots. Start changes here and extend differential coverage with each new construct.

**Reusable model results:** `Semantics`, `Region`, `Clock`, `Bytes`, `ByteCopy`, `Certificate`, and the dataplane models. The emitted echo loop lowers definitionally to `ByteCopy.copyByteWhile`, the loop used by the existing copy proof. The wrapper/host/native path still needs a complete refinement argument. Clocks represent model fuel, not CPU time.

**Removed inherited workloads:** the `Stage*`, `Serve*`, serializer and structure-emitter modules were removed. Their certificates required premises that no model state satisfies, their "compiler" ignored the program it compiled, and their memory model put one byte in each machine word, which the CakeML compiler theorem never provides. The emitted code is unchanged, byte for byte; `tests/golden` now pins it. The extraction manifest records where they came from, and git history keeps them.

**Preserved source:** `migration/dataplane` is still a reference snapshot. The echo host is new, small, and uses `poll`; it does not activate the old io_uring/kqueue product or prove correspondence to the abstract concurrency models.

## Next useful contributions

1. Expand differential fixtures with generated bounded ASTs, scope/shadowing cases, nested memory expressions, and explicit invalid-memory semantics. Keep seeds and minimized failures in the repository.
2. Turn `Abi.wordResult` and checked lowering into general preservation theorems under explicit, inhabited memory and scope contracts. Connect the Lean transcription to HOL semantics and the printer to the real parser.
3. Port one native reactor behind the same echo workload. Keep the reference host as a differential target; add real completion/cancellation and ownership tests before performance claims.
4. Replace the copy kernel with a bounded NNTP session step, starting with framing and discovery. Add the durable store before accepting articles.

The honest baseline claim is: **this maintained subset builds, rejects known unsupported inputs, agrees with independent references on the recorded suite, and drives a tested real TCP service.** There is no evidence yet for “the entire inherited compiler has few bugs”; the two boundary failures above are why this narrower, repeatable claim matters.
