# Native dataplane source for migration

This snapshot preserves the substantial native implementation we want to learn from and port. It is **outside the active Cargo/Lake builds**. Files retain their original names and bytes; `docs/provenance.json` records origins and hashes. New development belongs in active `DN` modules and crates.

## Extraction map

| Source | Useful material | Porting boundary |
| --- | --- | --- |
| `host/src/uring.rs`, `bufring.rs`, `l4_uring.rs` | Linux io_uring reactor, buffer-ring ownership, layer-4 path | Separate completion/buffer mechanics from HTTP dispatch and old FFI |
| `host/src/kqueue.rs` | BSD/macOS event-loop implementation | Extract the same protocol-neutral event interface |
| `host/src/pool.rs`, `workers.rs`, `blocking.rs` | Buffer pools and worker coordination | Connect generations and ownership to the active runtime contracts |
| `host/src/cake_serve.rs` | Existing CakeML/native integration | Review ABI, allocation, and fallback behavior; adapt for the new kernel |
| `host/src/stream_serve.rs`, `standing.rs` | Long-lived connection and streaming work | Review backpressure, partial writes, and disconnect cleanup |
| `ffi/linux_io.c`, `mac_io.c`, `durable.c` | OS and storage boundary examples | Specify the new ABI and error semantics before porting |
| `benchmarks/` | Performance experiments and audit notes | Replace HTTP workloads, old paths, and deployment assumptions |
| `scripts/` | Reachability and environment-flag audit approaches | Adapt checks to actual dn call sites and configuration |

The full host source is retained because its internals are coupled; a thin selection of headline files would hide important assumptions. Its original Cargo manifest references sibling crypto libraries and its build links old Lean/native artifacts. It is not a standalone dn reactor. The preserved HTTP, TLS, gateway, and other product modules are context, not advertised dn features.

The entire old orb product was not moved into the active project. All 45 compiler source modules were carried forward, plus reusable dataplane proofs and eight concurrency models. The remaining protocol-specific Lean application and its old deployment environment are not prerequisites for the current build. Source repositories remain untouched.

## Review gate before porting

The [native integration review](../../docs/reviews/native-integration.md) records blocking static migration risks around proxy timeout lifetimes, reusable-slot worker replies, and buffer-ring shutdown, plus lease and capacity gaps. The [triage](../../docs/reviews/README.md) specifies the required identity and lifecycle work. The current echo host does not use these implementations. Preserve this snapshot; repair and test an extracted adapter in active code.

## First port

Build one real TCP receive/respond loop with bounded buffers and explicit ownership transitions. Add partial-write, cancellation, stale-completion, and disconnect tests before reusing the fast path for NNTP. Identify the exact native call path exercised by each integration test. Compare it with the relevant model instead of assuming source similarity supplies a proof.

Do not run historical deployment or benchmark scripts unchanged: their paths, services, environment flags, and remote destinations belong to the ancestor project. Read them as source and migrate a focused local workload.
