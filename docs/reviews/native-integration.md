# Native dataplane integration review

Review findings describe the inspected baseline. See [triage and current disposition](README.md) for fixes applied during this review and unresolved obligations.

Date: 2026-09-18

## Scope and classification

This is a selective safety review of the adjacent `dn` native reference host at
revision `94785d23dbdcfdd8ff78f571e86ecacb56bb0eb7`. It covers
`native/echo_server.c`, `native/cake_runtime.h`, `crates/dn-runtime`, and the
preserved `migration/dataplane/host` files `uring.rs`, `bufring.rs`, `kqueue.rs`,
`workers.rs`, `pool.rs`, and `cake_serve.rs`. The C implementation behind the
last Rust file was inspected where necessary to evaluate its declared ABI.

`dn/native` and `dn/crates/dn-runtime` are active baseline code. No critical
defect was found in those active paths in this review. `dn/migration/dataplane`
is explicitly a read-only source snapshot outside the active build. Findings in
that tree are therefore **migration risks**, not claims about the running `dn`
echo server. They become defects if copied without correction.

The review is static and selective. No reviewed implementation source was
modified and no build or deployment script was run. File hashes for the reviewed
inputs are recorded at the end.

Here, **blocking migration risk (static analysis)** means the preserved design
lacks a lifetime or identity argument required by dn's native-reactor acceptance
criteria and should not be ported until corrected and tested. It does not mean
the inactive snapshot was reproduced as an exploitable running vulnerability.

## Findings

### Blocking migration risk (static analysis) — io_uring proxy timeout drops kernel-referenced state and reuses an unversioned slot

**Locations:** `migration/dataplane/host/src/uring.rs:169-195`, `:899-946`,
`:1610-1663`, `:1668-1850`, and `:3841-3870`; compare active
`crates/dn-runtime/src/slab.rs:1-68`.

Every io_uring operation encodes only an operation tag and a 32-bit slab index
in `user_data`. There is no cancellation/drain state and no generation in the
CQE identity. The ordinary client receive/send flow is partly mitigating: it
normally has one operation in flight and reaches `close` from that operation's
terminal completion; `SendZc` retains its response through all expected data and
notification CQEs. This review did not find a normal steady-state path that
arbitrarily closes a client socket while an unrelated client receive/send SQE is
known to remain outstanding.

The native proxy timeout path is different. `sweep_proxy_timeouts` invokes
`proxy_dial_failed` or `close` while the timed-out connect/send/receive SQE is
still outstanding. `take_proxy` removes and drops the `ProxyDial`, including the
boxed connect address or receive vector referenced by that SQE, and closes its
fd without submitting or reaping a cancellation. `close` can then remove the
client `Conn` and immediately return the index to the free list.

**Trigger/effect:** let an upstream connect/send/receive exceed its operation
deadline. The sweep drops memory still named by the outstanding SQE. When its CQE
later arrives, it is dispatched by the old slot alone; if a new client has reused
that slot, the proxy handler can act on the new connection's state. The missing
cancel-and-reap lifetime guarantee is established by inspection. The precise
kernel access after fd close, completion result, and exploitability require a
real io_uring reproducer; this report does not claim they were experimentally
observed. Shutdown has the broader form of the same unresolved lifetime problem,
as described separately below.

**Required fix before porting:** use the active generational slab idea at the
reactor boundary and include `(shard, slot, generation, operation-generation)`
in every CQE and serve-reply identity. A connection must enter a closing state,
submit explicit cancellation for every outstanding operation (or use a kernel
operation/lifetime scheme with an equivalent documented guarantee), retain all
referenced buffers, and delay slot reuse until cancellation/completion and all
`SendZc` notifications are reaped. Treat the fd separately from the logical
connection identity because the kernel may reuse fd numbers.

**Tests:** force close at each point after SQE submission and before CQE reap;
delay and reorder old CQEs across slot and fd reuse; cover positive receive
completions, `-ECANCELED`, short sends, and `SendZc` data/notification pairs.
Run under ASan/Miri where applicable and add a deterministic fake-CQ test that
asserts stale generations neither mutate a new proxy/connection nor extend a
vector whose reserved tail did not receive that operation's bytes.

### Blocking migration risk (static analysis) — asynchronous serve replies can be delivered to a different connection

**Locations:** `migration/dataplane/host/src/uring.rs:522-560` and
`:1123-1152`; `migration/dataplane/host/src/kqueue.rs:107-112`, `:638-661`,
`:704-758`, and `:1496-1508` (reply structs are defined in the preserved
`host/src/serve.rs:1513-1564`).

Both reactors hand the serve thread only a reusable slab index. If the client
disconnects or times out while serving, the slot is removed and can be filled by
a new connection. When the old response arrives, `on_wakeup` looks up only that
index and stages the old response on whatever connection now occupies it. On
kqueue this is visible directly at lines 724-756. io_uring has the same routing
at lines 1132-1150 and may additionally misclassify the old payload as a stream
head or effect-step response according to the new connection's state.

**Trigger/effect:** dispatch request A, close A before the core replies, accept B
into A's slot, then receive A's reply. B receives A's bytes or has its state
machine driven by A's continuation. In a future news service this could cross
session, authentication, article, or transaction boundaries. It violates dn's stated
reactor acceptance criterion for stale-generation rejection in `docs/handoff.md`.

**Required fix before porting:** make the gateway reply carry an opaque
generational connection token plus a request/effect generation. Validate the
complete token before touching state. Cancellation must invalidate the request
generation even if the slot remains occupied. Do not use a raw slab index as an
external completion capability.

**Tests:** a barrier-controlled serve stub should hold A's reply while A closes
and B reuses the slot, then release it; assert B is unchanged and the old reply
is dropped/accounted. Repeat for normal, split, streaming-head, and effect-resume
replies on both reactors.

### Blocking migration risk (static analysis) — shutdown lacks a quiescence and registered-memory lifetime protocol

**Locations:** `migration/dataplane/host/src/bufring.rs:83-111` and
`:159-169`; construction/drop order in `migration/dataplane/host/src/uring.rs:693-760`
and the early shutdown return at `:863-866`.

`BufRing::drop` says unregistering is implicit when the owning ring fd closes,
but `BufRing` is a field of `Shard`, which is declared after the local `IoUring`.
Rust drops locals in reverse declaration order: `Shard` (and its `BufRing`) is
dropped and both userspace mappings are unmapped before `IoUring` closes. The
loop returns on shutdown without canceling and draining all accepts, receives,
sends, and provided-buffer operations.

**Trigger/effect:** request shutdown with a receive outstanding. The code has no
demonstrated point at which registered/provided buffers and ordinary SQE buffers
are known to be quiescent before their userspace owners are dropped. The mapping
order and absence of an explicit unregister/cancel/drain protocol are definite.
Whether Linux retains pins that make a particular unmap safe, when those pins are
released, and whether a submitted operation can access memory after this order
were not tested here. This is therefore a missing lifetime argument and blocking
porting risk, not an experimentally established kernel use-after-free.

**Required fix before porting:** implement an explicit reactor shutdown state:
stop admission, cancel all outstanding work, reap every terminal completion and
zero-copy notification, unregister the provided-buffer ring, then unmap it, and
only then close/drop the io_uring. Encode ownership so the buffer-ring registration
cannot outlive its `IoUring` and `Drop` cannot silently assume quiescence.

**Tests:** repeatedly shut down with accept, plain receive, selected-buffer
receive, partial send, and `SendZc` notification outstanding. Use kernel fault
injection where available and assert no registered mapping is unmapped before
unregister/drain.

### P1 — provided-buffer ownership is an unchecked convention (migration risk)

**Locations:** `migration/dataplane/host/src/bufring.rs:114-155`.

`slice` enforces `bid < entries` and `len <= buf_size` only with
`debug_assert!`; `recycle` accepts any `u16`, tracks no leased/free state, and can
publish the same id twice. `add` converts `buf_size` to `u32` without rejecting a
larger value, and `entries * buf_size` is unchecked. The current constants and a
correct kernel keep ordinary calls in range, but the type does not enforce the
property its safety argument relies on.

**Trigger/effect:** a duplicated recycle, corrupted/incorrect completion id, or
future oversized configuration can place one physical buffer in multiple kernel
leases, create overlapping mutable kernel writes, publish an address outside the
mapping, or make the advertised length differ from the allocation.

**Required fix before porting:** validate nonzero `buf_size <= u32::MAX`, checked
multiplication and rounding, and release-build completion bounds. Represent each
buffer as `Free` or `Leased(lease_generation)` and require the matching lease
object to borrow or recycle it exactly once. Make invalid kernel metadata a
reactor fault, not an unchecked slice construction.

**Tests:** duplicate/stale recycle, out-of-range id/length, tail wrap, allocation
overflow, and randomized deliver/recycle sequences with conservation checks.

### P1 — the buffer pool bounds idle retention, not live memory or queue pressure (migration risk)

**Locations:** `migration/dataplane/host/src/pool.rs:38-82`; unbounded std
mailboxes in `migration/dataplane/host/src/uring.rs:68`, `:724`, and kqueue's
corresponding `channel` use.

`BufferPool::take` allocates a new vector whenever the free list is empty. The
`max_retained` field only bounds buffers after return. Vectors can subsequently
grow beyond `buf_cap`. The serve completion mailboxes are unbounded. Thus a slow
runtime owner, slow clients, or many partial requests can grow live allocations
and queued responses without a pool-enforced byte/job ceiling.

**Trigger/effect:** admit many connections and keep one or more buffers/request
and response in flight, or let producers outrun the single owner/consumer. Memory
grows with concurrency, request sizes, and queued completions; the advertised
fixed-capacity pool does not provide dn's handoff requirement for bounded queues.

**Required fix before porting:** impose explicit global and per-session byte and
job permits before allocation/dispatch; use bounded channels and define overload
behavior. Check growth before every append/reserve and count in-flight, queued,
and kernel-pinned buffers, not just idle buffers.

**Tests:** a stalled core and stalled writers at maximum connections, oversized
fragmented input, and a producer flood must keep RSS/allocation counters and
queue lengths under declared limits while returning deterministic refusal or
backpressure.

### P1 — the Cake serve ABI permits an out-of-bounds read and lacks a fail-closed result contract (migration risk)

**Locations:** Rust declaration/call in
`migration/dataplane/host/src/cake_serve.rs:85-105` and `:178-195`; implementation
in `migration/dataplane/host/ffi/cake/cake_serve_ffi.c:120-150`.

The C adapter allocates a fixed 4096-byte `obuf`. It trusts the generated
function's returned `total`, converts it to `size_t`, and caps it only to the
caller's `out_cap`, not to 4096. A caller passing `out_cap > 4096` can therefore
make `memcpy` read beyond `obuf` if the generated result exceeds 4096. The loop at
lines 133-136 dereferences `req` before the null check at line 137 when
`req_len > 1`. Current Rust passes a valid request pointer and exactly 4096 output
bytes, so these are latent ABI hazards rather than an observed Rust-call defect.
The Rust side also calls `Vec::truncate(n)` without independently rejecting a C
return greater than the supplied capacity; safety currently depends wholly on C.

**Required fix before porting:** specify the ABI in one header with exact integer
widths, pointer validity/disjointness, alignment, maximum request/result lengths,
and error codes. Reject invalid pointer/length pairs before dereference. Reject a
generated result greater than the actual scratch capacity; do not silently
truncate a logically oversized response. Rust must check `n <= out.len()` before
truncate/use and treat violation as a boundary fault. Apply the active baseline's
32-bit-return/output-slot lesson rather than assuming a 64-bit Cake return ABI.

**Tests:** direct C ABI tests for null/zero and null/nonzero inputs, capacities on
both sides of 4096, generated returns of 4096, 4097, `SIZE_MAX`, and overlap.
Guard-page the scratch buffers and run ASan/UBSan.

### P2 — active primitives need stronger integration identities and progress contracts (active-code limitation)

**Locations:** `crates/dn-runtime/src/slab.rs:1-68` and
`crates/dn-runtime/src/output.rs:5-30`.

The active slab correctly increments generations and permanently retires a slot
on generation exhaustion. However, `Token` contains no slab/shard identity, so a
token from another slab with the same index and generation can successfully
address an unrelated value if an adapter misroutes it. Private fields prevent
manufacture, not cross-slab confusion. `OutputCursor::complete(0)` deliberately
allows no progress and documents that the adapter must avoid a busy loop; it
does not encode EOF, retry, cancellation, or ownership of an asynchronous kernel
borrow.

These are not bugs in the small primitives as specified. They are assumptions
that must not be lost when integrating them into dn's native reactor.

**Required fix/contract:** either brand tokens with an unforgeable slab/shard id
or make cross-shard routing structurally impossible. Wrap output progress in an
operation state that distinguishes retryable zero progress, terminal close,
cancellation, and stale completion, and pins the source bytes until completion.

**Tests:** deliberately route tokens between two same-capacity slabs; the
integration must reject them. Exercise repeated zero completions under a bounded
scheduler and cancellation/late-completion races.

### P2 — the Cake runtime header is a single-translation-unit adapter with assumed sizing (active-code limitation)

**Locations:** `native/cake_runtime.h:8-23`; `native/echo_server.c:18-19` and
`:66-76`.

The header defines external runtime hooks (`cml_clear`, `cml_err`, `cml_exit`)
rather than merely declaring them, so including it from multiple translation
units causes duplicate definitions. `dn_runtime_init` hard-codes adjacent 1 MiB
heap and stack regions and immediately calls `cml_main`; the baseline documents
these as tested allocations, not proven minima. There is no ABI/version/layout
handshake with the linked generated object.

This is acceptable for the current one-file echo harness and is not an active
failure. It is unsafe as a reusable dn adapter contract.

**Required fix/contract:** move definitions to one C translation unit, expose a
narrow header, and bind generated artifact identity to an explicit ABI descriptor
covering word size, export return convention, heap/stack alignment and required
sizes, initialization/re-entry rules, and supported target. Fail before entry on
mismatch.

**Tests:** compile/link from two consumers, probe undersized/guard-paged regions,
and run an ABI fixture whose result exceeds 32 bits to ensure dn uses the supported
output-slot convention.

### P3 — supervisor capacity and termination behavior must be treated as policy (migration risk)

**Locations:** `migration/dataplane/host/src/workers.rs:44-98`, `:103-178`, and
`:220-239`.

Initial worker spawn failures are omitted from `children`; restart slots are
created only for successful children, so requested capacity is silently reduced
for the process lifetime. Shutdown uses `Child::kill` (normally SIGKILL), bypassing
worker quiescence. This is not a correctness defect for the historical HTTP
snapshot, but it is incompatible with assuming orderly persistence or full
configured capacity.

**Required fix before porting:** keep all requested slots and retry failed initial
spawns under the same bounded policy. Define graceful stop, deadline, forced kill,
and recovery semantics; a forced kill must be modeled as a crash and must never
be interpreted as rollback or non-acceptance.

**Tests:** fail selected initial spawns, recover the resource, and verify capacity
returns; test graceful and forced shutdown around indeterminate commits.

## Positive observations and porting baseline

The active reference echo host retains pending output and advances `sent` only by
the actual `send` result (`native/echo_server.c:106-117`); it does not rerun the
generated transition after a partial write. Its poll snapshot is built before
event handling and accepts only after processing old slots (`:83-140`), avoiding
same-batch readiness inheritance. The active runtime slab rejects stale
generations and handles generation exhaustion, and `OutputCursor` rejects
over-completion. These are useful starting properties, subject to the integration
limits above.

For dn, the minimum inherited-native acceptance gate should therefore be:

1. generational identities for kernel operations, core requests/effects, storage
   transactions, and connection slots;
2. buffers pinned until terminal completion/cancellation, including zero-copy
   notifications;
3. explicit quiescent shutdown and ordered ring unregister/unmap;
4. bounded bytes and jobs across accumulation, core queues, response queues, and
   kernel-owned buffers;
5. a versioned, checked generated-code ABI; and
6. deterministic tests that inject delayed, duplicated, reordered, canceled, and
   stale completions across slot/fd reuse.

Meeting those conditions would support dn's stated host-refinement work; it would
not by itself prove the adapter, persistence, or protocol implementation.

## Reviewed input identities

SHA-256:

```text
44083840fe43dd394e7de9b68e915cda4cfe778ac3c49d0462846db3a2787bbf  native/echo_server.c
731d95177453cf8774dc8ad43f032b82ff56b488a9f9b039636271ab97e66b04  native/cake_runtime.h
846436f454b07346f1780a39605a3c260b4064a916548f1734c62627817be5ee  crates/dn-runtime/src/limit.rs
ff4c711f89c53932815387d57a6c43e6743b32708e8df2841852266d59176825  crates/dn-runtime/src/output.rs
30b41bcbe1e1050509e651d592ba17f75e94fef39d7dc0a10a7b80173329a1ad  crates/dn-runtime/src/slab.rs
d813d175b44afa7eca5e5f07fbe357bc01e5390744f6d7a9864737fca339edf1  migration/dataplane/host/src/uring.rs
e6c6fd7b1bdfe930094bfafdca4d20f4b39993b006a98d3e7e67974f572791cf  migration/dataplane/host/src/bufring.rs
c7deb261b3af34c7becc73ed4dc37f92196cd06197eed6807aa65b8b32878a6f  migration/dataplane/host/src/kqueue.rs
525cd951916404ee54072c9616ef0acef8fa60f23c5ad0ef4d1aec96fcad6c2a  migration/dataplane/host/src/workers.rs
144a32000a4b7b41671b0681697496f6432aaac751a7c6abe53cccc5148c06da  migration/dataplane/host/src/pool.rs
82069167a062a88da199967677ed40c0fc4d2b1640601f941d979deb48992131  migration/dataplane/host/src/cake_serve.rs
```
