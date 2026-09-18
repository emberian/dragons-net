# Inherited-code review and triage

Unfinished work is tracked in the [project backlog](../project.md) and
[GitHub roadmap](https://github.com/emberian/dragons-net/issues/28).

Four Sol reviewers independently examined the compiler assurance, emission, dataplane models, and native integration around baseline `94785d2` on 2026-09-18. The lead reviewer reproduced the maintained printer failure with the pinned CakeML executable, inspected the critical native paths, and reviewed CI failure propagation. These were bounded reviews, not exhaustive audits. Report line references generally identify the reviewed revision; subsequent comment corrections can shift them.

**Assessment:** keep building on the maintained native subset, but do not port the preserved reactors wholesale or count inherited conditional theorems as a completed assurance chain. The active echo path was not found to have the blocking lifetime defects described below. The preserved source remains outside the active build.

## Findings and disposition

| Finding | Evidence / affected area | Disposition in this review |
| --- | --- | --- |
| CI logging could mask failed checks | Actual prior run used implicit `bash -e`; a failing command piped into `tee` exited zero | **Fixed:** explicit Bash with pipefail, plus an intentionally failing pipeline probe in both jobs |
| Checked emission produced unparsable nested loads | `ld8 ld8 p` accepted by our checker, rejected by pinned CakeML | **Fixed:** parenthesize nested loads; compile all four byte/word nesting pairs and execute two valid native pointer cases |
| Some purported certificates have impossible premises | Lean-checked contradiction from universally bound locals or universally addressable memory | **Contained:** source warnings and permanent contradiction theorems; full precondition-indexed API repair remains open |
| Slab keys can leave the token partition | Unbounded generation, 64-bit/tagged namespace constraints, concrete receive-tag collision | **Partial repair:** checked `Key.toToken?` with decode/bound proofs; allocator exhaustion policy and native linkage remain open |
| One-shot completion models are described as native reactor guarantees | No non-final multishot/cancellation product state; inline placeholder identity is not a valid kernel token | **Contained:** corrected model claims; lifecycle and identity redesign required before porting |
| Deadline/receive proofs are weaker than their prose | Ordering and unbounded sequential conservation do not establish timer delivery, finite memory, or cancellation safety | **Contained:** corrected claims; native scheduling/capacity obligations remain open |
| Native proxy timeout drops state before outstanding work is reconciled | Static call-path review of `sweep_proxy_timeouts`, `take_proxy`, and slot-only CQE dispatch | **Blocking migration risk:** keep inactive; require cancellation/terminal-completion ownership protocol |
| Worker replies are addressed by reusable slot only | Static `on_wakeup` paths in preserved io_uring/kqueue sources | **Blocking migration risk:** require connection and request generation validation |
| Shutdown lacks a proven quiescence/unregister order | Userspace drop order and early return in preserved buffer-ring host | **Blocking migration risk:** resolve kernel lifetime contract and test real teardown before porting |
| Pool/lease APIs do not enforce bounded ownership | Idle pool retention is not a live-memory limit; recycle and buffer bounds rely on conventions | **Blocking migration risk:** explicit byte/job permits and checked lease ownership |
| Inherited HTTP exports omit required bounds/token checks | Ignored request length, no output capacity, prefix routing, unchecked config-frame reads | **Contained as research fixtures:** exact caller preconditions documented; not exposed by native CLI |
| FFI and copy contracts omit useful conditions/frame facts | Unconstrained oracle writeback length; copy scratch locals and state frame | **Documented:** retain raw semantics, require contracted oracle and strengthened composition rules before reuse |

“Contained” means misleading claims were corrected and the unsafe-to-assume boundary is explicit. It does **not** mean the missing native implementation or general theorem has been supplied. A static migration finding is not an experimentally reproduced exploit of the active dn server.

## Detailed reports

* [Compiler assurance](compiler-assurance.md): contradictory premises, AST-versus-printed-source claims, FFI writeback, copy composition.
* [Emission and integration](emission-integration.md): nested-load failure and unchecked inherited HTTP interfaces.
* [Dataplane models](dataplane-models.md): token partition, operation lifecycles, inline identity, timers, receive capacity, exhaustion.
* [Native integration](native-integration.md): reviewed lifetime/identity paths, mitigations, migration blockers, and source hashes.
* [CI failure propagation](ci-failure-propagation.md): the logging-gate reproducer and fix.

## Recommended next work for Wisper

### 1. Choose one identity and ownership contract

Specify connection, request, operation, and buffer-lease identities. Include the necessary generation and shard/owner information; a file descriptor or reusable slot is not enough. Choose an exhaustion policy compatible with the token partition. The new checked conversion rejects out-of-partition keys but does not stop `Io.Slab` allocating one, and the active Rust slab's `u64` generation is not the same layout.

Acceptance: an old CQE, old worker reply, stale deadline, and token routed to the wrong owner cannot affect a replacement connection. Include a barrier-controlled A-closes/B-reuses/A-reply-arrives regression. Prove successful key conversion and the allocator invariant together, then wire the native adapter to that checked path.

### 2. Make terminality explicit before io_uring porting

Specify live, cancel-requested, and terminal states, plus outstanding data/notification events. Cancellation submission is not release permission. Non-final multishot completions retain operation ownership. Zero-copy send notifications and buffer leases need their own terminal obligations.

Acceptance: deterministic traces for completion-first/cancel-first, cancellation “not found”, multishot MORE/final, disconnect during proxy I/O, and shutdown with every operation kind outstanding. Keep referenced buffers until the required terminal events have been reaped. Then test the real adapter under memory instrumentation where applicable.

### 3. Repair the reusable compiler contract

Replace universal-state data/memory assumptions with judgments indexed by explicit preconditions. Supply an inhabited witness, preserve unrelated locals/memory/FFI/base address, and state scratch-variable effects and fuel costs. `Certificate`/`RefinesClk` provide a starting point; the old `ProofProducing` APIs are not repaired by merely importing them.

Acceptance: concrete bound-local and finite-memory callers for the former stamp/redirect examples, composed without contradictory assumptions; direct model execution checks; printer/parser/native tests for the same emitted workloads. For FFI, state length and addressability constraints before claiming an effect frame.

### 4. Extend the native memory corpus and keep the reference host

Generate bounded expression/control trees including nested loads, stores, scope changes, and protected-page boundaries. Preserve minimized failures. Compile and run new constructors before promoting them into the maintained subset. Keep the current echo host as a behavioral reference when swapping in an optimized reactor; do not replace a known workload and its adapter simultaneously.

The next milestone should be a correctly owned native echo adapter with the same observed behavior and stronger lifecycle evidence. NNTP can then exercise the compiler without inheriting an unresolved completion/lifetime design.
