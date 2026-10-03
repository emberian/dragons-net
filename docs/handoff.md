# Contributor handoff

Use the [project backlog](project.md) and [live roadmap](https://github.com/emberian/dragons-net/issues/28)
to choose scoped work; issues record acceptance criteria and hard dependencies.

Start with the [inherited-code review and prioritized repairs](reviews/README.md), [the compiler baseline](baseline.md) and [the runnable echo example](echo.md). Read the root README, [architecture](architecture.md), and [assurance](assurance.md) first. Run `bash scripts/check.sh` and `python3 scripts/check_models.py --loom`. On Linux x86-64, run the native check from the README. All active Lean/Rust dependencies are defined within this repository and its lock files; the old monorepo is not needed for these checks.

## Where to start reading

1. `lean/DN/Compiler/Main.lean`, `Syntax.lean`, `Lower.lean`, `Checked.lean`, and `Abi.lean`: the actual emitted example and the supported lowering boundary.
2. `Semantics.lean`, `Region.lean`, `Clock.lean`, and `Certificate.lean`: model execution and composition, including a certificate requiring an inhabited precondition.
3. `ByteCopy.lean`, `ByteLit.lean`, `Decimal.lean`, `Div10.lean`, `NatToDec.lean`, `LowerBridge.lean` and `LowerBridgeSem.lean`: byte-addressed writes, decimal rendering, and the bridge from the lowered program to its execution.
4. `lean/DN/Dsl`: the source language, its compilation and the proof that covers every program; [why it is embedded deeply](decisions/0001-embedding.md). [How the server enters the generated code and which memory it uses](decisions/0002-entry-and-memory.md): a loop in `main`, the host through external calls, buffers in the heap.
5. `lean/DN/Dataplane`, `crates/dn-runtime`, and `models`: proof models, usable host primitives, and bounded concurrency exploration respectively.
6. [Native source migration map](../migration/dataplane/README.md): io_uring/kqueue and FFI source to adapt, with its old coupling explicitly retained for inspection. Read [the porting risks](porting-risks.md) before reusing any of it: the ownership and lifetime decisions in that snapshot are the part that has to be redesigned.

## First milestones and acceptance criteria

The criteria that bind are in the [roadmap](https://github.com/emberian/dragons-net/issues/28) and the issues it links; what each milestone below calls acceptance is what a reviewer should expect to see, and the issue is what decides.

### 1. Make the compiler boundary explicit

Write down the accepted source language and the mapping from its syntax through `Lower` to the modeled Pancake semantics. Unsupported forms must fail explicitly. `lean/DN/Dsl` does this for a first, small language: its mapping to the model is proven for every program, and `emit` refuses what the proof does not cover. `LowerTests.lean` already covers nonscalar loads, unsupported calls, FFI arity, and comparison lowering.

Extend `Certificate` to a useful memory-reading/writing component with concrete preconditions. Demonstrate a caller state that satisfies the contract, compose two components, and compare emitted execution with an independent reference. Do not restate a precondition as a condition on every model state: such premises are contradictory, as `AssuranceChecks.lean` records.

Close the printed-source/parser and model/HOL bridges before claiming verified code generation. `scripts/parser_contract.py` holds the printed source against the pinned parsers program by program; a proof that the parser reads every printed program as its lowering is still to be written. Keep counterexamples when assumptions fail: `scripts/native_fuzz.py` reduces a disagreement it finds to a small case in `build/fuzz/minimized/`; once fixed, keep it in `tests/corpus/found/` and in `DN.Compiler.GenCorpus.found`, and every run requires it to agree again. The curated backend proof rebuild and the compiler bootstrap have both been run; [instructions](../backend/README.md) identify the pins and what each establishes.

### 2. Extract a protocol-neutral native reactor

Port the buffer ownership and completion machinery from the preserved native source into an active crate. Use the existing generated-code echo service as the socket workload and reference behavior. Linux io_uring is the performance target; kqueue source is also available. The kernel may touch the generated program's heap only as the [entry decision](decisions/0002-entry-and-memory.md) fixes. Keep protocol decisions outside the OS adapter.

Acceptance: a real loopback connection; input split at arbitrary byte boundaries; partial output completion; bounded queues; EOF/error/cancellation cleanup; stale-generation rejection; no double recycle. Demonstrate which tests execute the native path, and retain a deliberately broken variant in the concurrency model where useful. A successful model test does not establish correspondence to the adapter.

### 3. Deliver the smallest useful NNTP slice

Follow [the NNTP plan](nntp.md). The first slice is built: greeting, capability discovery, HELP, QUIT, HEAD and STAT against an empty store, and error handling, run in the generated program's `main` ([decision 0002](decisions/0002-entry-and-memory.md)) behind a reference `poll` host ([decision 0003](decisions/0003-nntp-slice.md), [details](baseline.md#nntp-server)), without claiming READER support. Next is the durable store (#17), whose design is [decision 0005](decisions/0005-article-store.md); complete the reader/posting profile before advertising its capabilities.

Acceptance: transcript tests against an independent client, command/article framing under arbitrary chunk splits, dot transparency, bounded input, stable Message-ID deduplication, crosspost indexing, and crash/restart tests around article acceptance. A POST success response needs a specified durability point.

### 4. Measure and expand

Benchmark the same workload through a simple reference host and the optimized adapter. Record compiler, CPU, OS, input distribution, connection count, queue bounds, latency distribution, throughput, allocations, and CPU usage. Do not promote the native digest benchmark into a server performance claim.

Add peering, authenticated access, offline bundles, and a human UI after the storage/session contracts stabilize. The initial scope is documented without advertising unfinished features.

## Working conventions

`AGENTS.md` describes automated-agent expectations; the same assurance discipline applies to all contributors. Every module under `lean/DN` is picked up by the proof audit automatically. Put kernel theorems and executable examples in their respective lanes. Use `scripts/check.sh` before committing and the native/Loom lanes when touching their boundaries. CI uploads logs and native artifact digests.

`migration/` preserves original source bytes. Port into active modules rather than editing that snapshot. Retain provenance and update the documentation when a reference component becomes active. Old deployment scripts are historical evidence, not instructions to run against a machine.

Known gaps: there is no general source-language CLI, NNTP daemon beyond the first slice, durable spool, TLS/authentication adapter, optimized OS reactor, or end-to-end compiler theorem. The native lanes run the release compiler, and no theorem covers either it or the one built from the patched source (`backend/bootstrap-record.json`). These are concrete next tasks, not hidden dependencies of the green baseline.
