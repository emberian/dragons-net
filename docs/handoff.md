# Contributor handoff

Use the [project backlog](project.md) and [live roadmap](https://github.com/emberian/dragons-net/issues/28)
to choose scoped work; issues record acceptance criteria and hard dependencies.

Start with the [inherited-code review and prioritized repairs](reviews/README.md), [Wisper’s baseline](baseline.md) and [the runnable echo example](echo.md). Read the root README, [architecture](architecture.md), and [assurance](assurance.md) first. Run `bash scripts/check.sh` and `python3 scripts/check_models.py --loom`. On Linux x86-64, run the native check from the README. All active Lean/Rust dependencies are defined within this repository and its lock files; the old monorepo is not needed for these checks.

## Where to start reading

1. `lean/DN/Compiler/Main.lean`, `Syntax.lean`, `Lower.lean`, `Checked.lean`, and `Abi.lean`: the actual emitted example and the supported lowering boundary.
2. `Semantics.lean`, `Region.lean`, `Clock.lean`, and `Certificate.lean`: model execution and composition, including a certificate requiring an inhabited precondition.
3. `ByteCopy.lean`, `ByteLit.lean`, `Decimal.lean`, `NatToDecCompile.lean`, `NatToDecFull.lean`, `LowerBridge.lean` and `LowerBridgeSem.lean`: byte-addressed writes, decimal rendering, and the bridge from the lowered program to its execution.
4. `lean/DN/Dataplane`, `crates/dn-runtime`, and `models`: proof models, usable host primitives, and bounded concurrency exploration respectively.
5. [Native source migration map](../migration/dataplane/README.md): io_uring/kqueue and FFI source to adapt, with its old coupling explicitly retained for inspection.

## First milestones and acceptance criteria

### 1. Make the compiler boundary explicit

Write down the accepted source language and the mapping from its syntax through `Lower` to the modeled Pancake semantics. Unsupported forms must fail explicitly. `LowerTests.lean` already covers nonscalar loads, unsupported calls, FFI arity, and comparison lowering.

Extend `Certificate` to a useful memory-reading/writing component with concrete preconditions. Demonstrate a caller state that satisfies the contract, compose two components, and compare emitted execution with an independent reference. Do not restate a precondition as a condition on every model state: such premises are contradictory, as `AssuranceChecks.lean` records.

Close the printed-source/parser and model/HOL bridges before claiming verified code generation. Keep counterexamples when assumptions fail. The curated backend proof rebuild and subsequent compiler bootstrap are separate milestones; [instructions](../backend/README.md) identify the pins.

### 2. Extract a protocol-neutral native reactor

Port the buffer ownership and completion machinery from the preserved native source into an active crate. Use the existing generated-code echo service as the socket workload and reference behavior. Linux io_uring is the performance target; kqueue source is also available. Keep protocol decisions outside the OS adapter.

Acceptance: a real loopback connection; input split at arbitrary byte boundaries; partial output completion; bounded queues; EOF/error/cancellation cleanup; stale-generation rejection; no double recycle. Demonstrate which tests execute the native path, and retain a deliberately broken variant in the concurrency model where useful. A successful model test does not establish correspondence to the adapter.

### 3. Deliver the smallest useful NNTP slice

Follow [the NNTP plan](nntp.md). First make greeting, capability discovery, HELP, QUIT, and error handling work over the real adapter, without claiming READER support. Then add mandatory HEAD/STAT access and the durable store; complete the reader/posting profile before advertising its capabilities.

Acceptance: transcript tests against an independent client, command/article framing under arbitrary chunk splits, dot transparency, bounded input, stable Message-ID deduplication, crosspost indexing, and crash/restart tests around article acceptance. A POST success response needs a specified durability point.

### 4. Measure and expand

Benchmark the same workload through a simple reference host and the optimized adapter. Record compiler, CPU, OS, input distribution, connection count, queue bounds, latency distribution, throughput, allocations, and CPU usage. Do not promote the native digest benchmark into a server performance claim.

Add peering, authenticated access, offline bundles, and a human UI after the storage/session contracts stabilize. The initial scope is documented without advertising unfinished features.

## Working conventions

`AGENTS.md` describes automated-agent expectations; the same assurance discipline applies to all contributors. Every module under `lean/DN` is picked up by the proof audit automatically. Put kernel theorems and executable examples in their respective lanes. Use `scripts/check.sh` before committing and the native/Loom lanes when touching their boundaries. CI uploads logs and native artifact digests.

`migration/` preserves original source bytes. Port into active modules rather than editing that snapshot. Retain provenance and update the documentation when a reference component becomes active. Old deployment scripts are historical evidence, not instructions to run against a machine.

Known gaps: there is no general source-language CLI, NNTP daemon, durable spool, TLS/authentication adapter, optimized OS reactor, or end-to-end compiler theorem. A bounded reference `poll` host now drives the generated echo kernel. The backend HOL proof lane is scaffolded but not yet rebuilt here. These are concrete next tasks, not hidden dependencies of the green baseline.
