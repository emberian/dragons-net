# Review of inherited dataplane models

Review findings describe the inspected baseline. See [triage and current disposition](README.md) for fixes applied during this review and unresolved obligations.

Scope: read-only review of `/Users/ember/dev/dn/lean/DN/Dataplane`, with the
active `dn-runtime` slab and the independent Rust concurrency models used as
comparison points. I did not run a Lake build. The repository-wide assurance
document correctly says that host refinement remains open; findings below call
out places where individual model comments exceed that boundary or where a
missing transition/invariant blocks that refinement.

## Findings

### High — the pending-operation slab can mint keys outside the proven 64-bit token partition

**Location:** `lean/DN/Dataplane/Io/Slab.lean:80-101`, `:130-149`; conflicting
contract in `lean/DN/Dataplane/Flow/Token.lean:24-28`, `:55-67`, `:185-195`.

`Io.Slab.Key.pack` is proved to round-trip with only `idx < 2^32`. Its generation
is an unbounded `Nat`; every successful remove increments it, and insert reuses
that value without a bound. But `Flow.Token.Wf` permits slab generations only
below `2^31`, because larger generations overlap the tagged token namespaces.
The token model itself supplies the counterexample:

```text
Io.Key { idx := 5, gen := 0xBECF0000 }.pack
  = Flow.Token.encode (.recvMulti 5)
```

Thus a reachable slab slot after enough reuse can produce a word that native
dispatch interprets as multishot receive traffic for fd 5. `Key.unpack_pack`
still succeeds over `Nat`, so it does not establish the claimed kernel-word
round trip or namespace safety. This blocks using the slab theorem as the
correlator safety argument for a native reactor.

**Focused fix/tests:** unify `Io.Key` with `Flow.Token.slab`, add a slab
well-formedness invariant requiring `idx < 2^32` and `gen < 2^31`, and specify an
exhaustion transition (retire the slot or move to a disjoint encoding) before
increment would violate it. Prove insert preserves that invariant and always
returns a well-formed token. Add boundary regressions at generation `2^31-1`
and the existing `0xBECF0000` collision. If the intended implementation uses
the active runtime's `u64` generation and slot retirement, model that policy
instead of an unbounded increment.

### High — the completion reactor has no cancellation or multishot lifecycle, so its “running reactor” correspondence cannot cover native cleanup

**Location:** `lean/DN/Dataplane/Io/Reactor.lean:5-12`, `:23-29`, `:55-62`,
`:90-110`; `lean/DN/Dataplane/Io/CompletionHandler.lean:93-110`.

The only deferred-completion transition removes the operation on the first
matching CQE. There is no cancel request, cancel result, close/EOF, concurrent
cancel-versus-complete outcome, or multishot `more` state. Consequently:

* a multishot operation would be removed on its first non-final completion;
* cancellation cannot retain ownership until the kernel has resolved the race;
* the model cannot express the rule that buffers and operation state remain live
  until either the completion or cancellation terminal event wins;
* late CQEs are rejected only after unconditional removal, rather than after a
  modeled terminal transition.

The one-shot theorems are valid for their small machine, but the prose saying
the running io_uring/kqueue reactors “realize” it is stronger than the model and
conflicts with `docs/assurance.md`'s explicit open host-refinement obligation.
The separate ring LTS models multishot buffer leases, but there is no product or
coupling invariant connecting it to this operation slab.

**Focused fix/tests:** add operation kind and lifecycle states such as live,
cancel-requested, and terminal; make non-final multishot CQEs preserve the slab
entry; model both cancel-first and completion-first races and their late CQEs;
couple buffer leases to operation termination. Prove one terminal ownership
release per operation and one recycle per delivered buffer. Add traces for
disconnect with receive/send outstanding, cancel returning “not found” while a
CQE is pending, and multishot non-final then final completion.

### High — inline completions reuse the wakeup sentinel as a completion identity

**Location:** `lean/DN/Dataplane/Io/Reactor.lean:86-107`, `:181-196`;
`lean/DN/Dataplane/Flow/Token.lean:18-28`, `:72-101`.

`RState.inline` records an ordinary operation completion under key `(0,0)`,
while the token partition defines encoded word 0 as the wakeup sentinel and
explicitly excludes slab index 0. The `inline_eq_deferred` theorem hides this
difference by projecting each completion to `(op,result)` and discarding the
key. Any downstream component that dispatches, cancels, deduplicates, or audits
by the completion key cannot use the equivalence: encoding the inline key gives
a wakeup event, not an operation completion.

This is an actual representation conflict, rather than a problem with the
limited observational theorem itself.

**Focused fix/tests:** represent inline completion without a kernel correlator
(a separate sum constructor), or allocate a well-formed operation identity that
never enters kernel dispatch. State and prove equivalence over the full
consumer-visible event type. Add a dispatch test showing an inline completion
cannot take the wakeup branch.

### Medium — deadline safety depends on the caller choosing a generational key, but the interface admits fd-only keys

**Location:** `lean/DN/Dataplane/Io/Deadline.lean:52-57`, `:62-79`, `:211-220`;
`lean/DN/Dataplane/Flow/Deadline.lean:63-104`.

Both deadline queues are polymorphic over an arbitrary key. Their theorems show
correct list/heap behavior for equality on that key, but establish no ownership
link to a particular connection incarnation. If native integration instantiates
`K` with an fd, this trace is admitted: set timeout for connection A on fd 7;
close A; reuse fd 7 for B; the old timeout fires and is indistinguishable from
B's timeout. Lazy deletion helps only if every close path removes the exact key,
which is precisely the cancellation/cleanup obligation not modeled here.

The comment allowing “correlators or connection handles” makes the unsafe
instantiation appear supported. The heap results themselves are sound and are
an explicitly scoped abstraction of ordering.

**Focused fix/tests:** expose the native-facing queue over a generational
connection handle, or require/prove an `OwnedKey` invariant tying every live
deadline to a live slab incarnation. Add close/reopen/stale-fire traces and show
the old key cannot close the replacement connection.

### Medium — “cannot sleep through a deadline” is not established by the Flow deadline invariant

**Location:** `lean/DN/Dataplane/Flow/Deadline.lean:74-104`, `:186-192`.

`DeadlineQueue.Inv` says only that the model field `armed` contains a number no
later than each live deadline. `wake_scheduled` merely restates this invariant.
There is no transition for submitting/replacing a kernel timer, no token tying a
timer CQE to the arm generation, no failure result, and no progress/fairness
assumption that a timer at `t` produces `fire now`. A state such as
`live=[(k,10)], armed=some 0` satisfies the invariant indefinitely even if no
kernel timer exists. Therefore the statement “The reactor cannot sleep through
a deadline” is not a consequence of this model.

This does not invalidate the exact expiry/partition theorems for explicit
`fire` events; it limits them to functional queue behavior after the host
supplies an event.

**Focused fix/tests:** weaken the prose to the actual ordering invariant, or add
an arm-request/arm-ack/timer-CQE machine with generation-tagged timer tokens and
an explicit environment delivery assumption. Test rearm failure, stale CQE after
an earlier timer is replaced, and removal of the nearest deadline.

### Medium — the receive backpressure model is unbounded and turns cancellation into an instantaneous mode bit

**Location:** `lean/DN/Dataplane/Flow/Recv.lean:13-19`, `:26-64`, `:105-135`.

`arrive` appends arbitrary data to `kernelBuf` even while parked, with no
capacity, EOF, error, or dropped-data transition. `park` immediately makes every
subsequent `deliver` a no-op; there is no already-posted CQE or cancel race. The
resulting conservation proof is true because all arrivals can be retained in an
unbounded ghost/kernel list. It cannot justify the native claims that parking
closes the TCP window in time, that memory remains bounded, or that cancellation
cleanup is safe.

This is a useful sequential stream-order abstraction, and should remain labeled
as such. It becomes a defect only if used for bounded-memory or cancellation
assurance.

**Focused fix/tests:** add a finite receive capacity and explicit ownership
locations (kernel, CQE, handler, recycled), plus cancel-requested and terminal
states. Test arrival at capacity, CQE already published when park occurs,
cancel-versus-final-completion, EOF/error, and resume after cancellation.

### Low — the global-generation model's wraparound prose disagrees with the active runtime policy

**Location:** `lean/DN/Dataplane/Slab/Generation.lean:329-332`, `:395-445`;
`crates/dn-runtime/src/slab.rs:57-68`.

The Lean comment says a skip-zero rule preserves sentinel disjointness “through
wraparound” and later describes an implementation using wrapping increment.
The active runtime instead uses `checked_add` and permanently retires a slot at
`u64::MAX`; it does not wrap or skip zero. The Lean theorem is over unbounded
`Nat` and its native bridge requires `NoWrap`, so the proofs remain valid, but
the implementation description is stale and obscures the safer exhaustion
policy already present in Rust.

**Focused fix/tests:** document retirement as the chosen native policy and add
it to whichever Lean slab becomes authoritative. Prove exhausted slots are
never reallocated; retain the existing Rust exhaustion regression as
correspondence evidence once a refinement relation exists.

## Explicitly scoped abstractions that are not defects

* The ring conservation theorem requires `cfg.nodrop = true`, and the repository
  retains an explicit leak counterexample without `nodrop`. That precondition is
  meaningful and inhabited, not vacuous.
* `Ring.recycle_at_most_once` proves at-most-once recycling per modeled lease; it
  does not prove eventual recycling. The separate `recycle_enabled` lemma is
  only an enabledness fact, so no liveness conclusion should be inferred.
* `Io.Wake.wake_no_lost` covers the six sequentially consistent interleavings of
  one producer publication and one reactor sleep decision. The independent Rust
  model uses `SeqCst` for the load-bearing operations. It is a bounded protocol
  lemma, not a scheduler or syscall progress theorem.
* `SpanBytes.read_eq_denote` is a model-level, well-formed-span equivalence. It
  deliberately says nothing about Rust borrow lifetime, aliasing, mutation, or
  buffer ownership.

## Integration priority

Before porting a native reactor, choose one authoritative slab/key design and
connect it to the token partition. Then extend the reactor with cancellation and
multishot terminality and couple it to ring-buffer ownership. Those changes
address the two paths that can otherwise misroute a completion or recycle
storage while the kernel still owns it. Deadline and receive refinements can
then use the same generational ownership vocabulary.
