# Dataplane PERF-AUDIT — the orb vs nginx, ground-truthed

Scope: the CURRENT native host (`crates/dataplane`) driving the leanc-compiled
proven serve, measured end to end over a real loopback socket, against a matched
nginx reference. This is the honest state after the recent keep-alive /
middleware / config-route / h2c work. Read with the concurrency finding and the
named lever below; the benchmark table is the "fast" gate's win condition.

Reproduce: `conformance/perf/bench.sh` (throughput matrix) and
`conformance/perf/body-scaling.sh` (response-body growth). Both build a matched
nginx (tiny reply, static file, reverse proxy to a shared origin) from scratch.
Per-call attribution: `crates/serve-bench` links the same archive and times
`drorb_serve` in a tight loop.

Toolchain: `HACL_DIST=$HOME/src/hacl-star/dist/gcc-compatible` (plus
`LIBRARY_PATH` / `DYLD_LIBRARY_PATH`); build
`ffi/build-dataplane-lib.sh && (cd crates/dataplane && cargo build --release)`.
Load generator `ab`; reference `nginx` (auto workers). Host: 12-core arm64,
macOS — so the io_uring path is Linux-only and NOT exercised here; the path under
test is the portable **blocking thread-per-connection** host (`src/blocking.rs`).

## ⚠ Measurement conditions — the machine was heavily contended

Every live run below was taken with a sibling agent saturating the box: load
average held **85–108 on 12 cores** for the entire session and never fell. That
inflates latency and depresses req/s for BOTH columns, and it hurts the orb
DISPROPORTIONATELY: the orb funnels all request compute onto ONE serve thread,
and a single starved thread among ~100 runnable threads loses far more than
nginx's 12 workers do. Treat the absolute req/s as a **contended-floor**, not the
quiet-machine ceiling. The orb:nginx ratios and the *shape* across concurrency /
body size are the robust signals and are what the findings rest on; the
quiet-machine ceiling comes from the per-call microbench. Re-run `bench.sh` on an
idle machine for clean absolutes.

## Benchmark table (ab; load ~85–108 throughout; median of samples)

Small body = `GET /health` → 200, 2-byte body (orb and nginx byte-matched).
p50/p99 in ms.

| scenario (c=concurrency)              | ORB req/s | ORB p50 | ORB p99 | NGINX req/s | NGINX p50 | NGINX p99 |
|---------------------------------------|-----------|---------|---------|-------------|-----------|-----------|
| small, conn-per-request, c=10         | ~420      | 24      | 39      | ~3990       | 1         | 23        |
| small, keep-alive, c=1                | ~420–530  | 1       | 27–40   | ~4460–7015  | 0         | 1–2       |
| small, keep-alive, c=10               | ~1170     | 2       | 90      | ~8950       | 0         | 12        |
| small, keep-alive, c=50               | ~1280     | 24      | 164     | ~14430      | 1         | 62        |
| small, keep-alive, c=100              | ~1450     | 64      | 191     | ~11510      | 3         | 206       |
| reverse-proxy /api, conn-per-req, c=10| ~420      | 24      | 34      | ~1670       | 3         | 74        |
| reverse-proxy /api, keep-alive, c=10  | ~2730–3350| 2       | 34–56   | (see note)  |           |           |

Reverse-proxy keep-alive note: nginx `-k` to a proxied `return 200` origin reset
under this load and `ab` aborted the summary; the conn-per-request row is the
parity comparison. The orb's proxy keep-alive number is higher than its own
`/health` keep-alive because the proxy path crosses only the cheap
`drorb_proxy_pick` seam on the serve thread and dials the backend on the
(parallel) connection thread — less work is serialized (see lever).

Large body (response-body construction, `body-scaling.sh`, single-request
min-of-8 wall time; ratio across sizes is the robust signal):

| body size | ORB min/req | nginx min/req |
|-----------|-------------|---------------|
| 1 KiB     | ~5.6 ms     | ~0.9 ms       |
| 8 KiB     | ~421 ms     | ~0.9 ms       |
| 64 KiB+   | inline-respond config no longer loads (0 bytes served) | ~1.6 ms |

8× the body → ~75× the orb time (pure O(N²) would be 64×): response construction
is **~quadratic** in body length. nginx is flat (`sendfile`). The orb has no
large-body route in the default serve, and a large inline `respond` body exceeds
the config parser's budget — both are downstream of the same cons-list cost.

## Per-call attribution (serve-bench: pure `drorb_serve`, single thread)

The FFI marshalling floor (wrap bytes in a runtime ByteArray, drop it) is
**~13 ns/call** — negligible. The entire per-request cost is the proven
`ByteArray → ByteArray` transform. On a lightly-loaded sample the whole
`/health` serve was **~50 µs/call → a ~20k req/s single-thread ceiling**;
`/admin`-401 short-circuit ~8 µs; `/nope`-404 ~8 µs (the 200 path is ~6× the
short-circuit because it runs the handler + builds the full header block + body).
Under the contended session the same calls measured several-fold higher — a
machine-load artifact, not the archive. The size sweep (robust internal ratio) is
the tell: `/health` per-call rose 50 µs → 85 µs → 125 µs → 238 µs as the request
grew 43 → 116 → 180 → 308 bytes — **superlinear**, the cons-list signature. (The
deployed `/health` also serializes the whole request into an `x-corr` header,
which is why its cost tracks request size; the effect is the same List-UInt8
O(N·len) serialize.)

## Concurrency finding: the serve is SERIALIZED (IO is parallel)

Ground truth from the code, then confirmed by measurement.

Code (`src/serve.rs`, "Concurrency model" + the `SINGLE-OWNER` note on
`spawn_serve_thread`): the runtime is a **process-global singleton** —
`initialize_Dataplane` installs top-level constants once and there is no way to
stand up N independent runtimes in one process. So every seam crossing is
confined to ONE dedicated `drorb-serve` thread that owns the runtime; it is the
only caller of `drorb_serve`. IO threads (`src/blocking.rs`: accept → spawn a
thread per connection) read and write in parallel and funnel completed requests
to that one serve thread over an mpsc channel, blocking on the reply. The serve
computation is serialized; the doc states the ceiling outright:
`1 / (serve latency)` — one core's worth of the proven pipeline, however many IO
cores feed it. There is NO Mutex around the runtime — there does not need to be,
because exactly one thread ever touches it.

Measurement confirms it. Keep-alive `/health` req/s vs concurrency:

```
c:      1      10     50     100
ORB:   ~420   1170   1280   1450     <- plateaus (single serve thread saturates)
NGINX: ~5000  8950  14430  11510     <- scales with concurrency (parallel workers)
```

The orb's throughput barely moves from c=10 to c=100 (~1.2×) while its p50/p99
climb (2→64 ms / 90→191 ms): added concurrency just queues behind the one serve
thread. nginx's throughput rises with concurrency. This is the textbook
serialized-server vs parallel-server shape.

Is multi-shard a lever? **No — not within one process.** The io_uring path
(Linux) shards IO across cores, and the blocking path already spawns a thread per
connection, so IO is not the bottleneck. But every shard/thread still funnels to
the ONE serve thread, because the runtime is a process-global singleton. More IO
shards cannot raise `1 / (serve latency)`. The only ways to lift it: (a) lower
the serve latency itself (the lever below), or (b) run N processes each with its
own runtime behind a balancer — a deployment workaround that scales throughput
but does not make the datapath fast, and is orthogonal to the goal.

## Top perf lever (with evidence): per-request serve latency = the cons-list

The single top lever is the **latency of the proven `ByteArray → ByteArray`
serve itself**, dominated by the `Bytes = List UInt8` cons-list representation
and the owned copy-in/copy-out ABI. Because the serve is serialized, the whole
single-process ceiling is exactly `1 / (serve latency)`, so this latency is not
one lever among several — it is THE lever for single-process throughput.

Evidence, converging:
1. **FFI floor ~13 ns vs ~50 µs serve** — the boundary is 0.03% of the cost; the
   cost is entirely inside the compiled transform, not the marshalling or IO.
2. **Superlinear in size** — per-call cost grows faster than input length
   (50→238 µs over 43→308 B); the O(N·len) append / traversal of a cons-list.
3. **Quadratic response build** — 1 KiB body 5.6 ms, 8 KiB body 421 ms; nginx
   flat. Building a response body over `List UInt8` is ~O(N²).
4. **The plateau** — live throughput ceilings at one serve thread's rate; halving
   serve latency ~doubles the ceiling, and nothing else does.

This CONFIRMS the durable-context claim that "the cons-list serve is the wall,"
with numbers. It is a **codegen / modeling** matter, not a shell matter: it lives
inside the proven core's data representation and its owned-ByteArray export ABI,
and is un-fixable from the Rust host or by adding IO shards. The standing fix is
the `Datapath/` refinement frontier — a `serveC` over borrowed buffers (affine
`ResponseBuilder` → in-place `OutBuf`, index-native span scanner, zero-copy
`writev`/send) proven to refine `servePipelineOf`, lowered by the verified
compiler path. Secondary, smaller levers once the representation changes: drop
the per-request `x-corr` request echo (superlinear header serialize on the hot
200 path), and the 5→~1–2 payload-copy reduction noted in the datapath
comparison. But the representation is the wall.

## Bottom line

- Serve is **serialized** (one runtime-owner thread), IO is **parallel** — proven
  in `serve.rs`/`blocking.rs` and confirmed by the concurrency plateau.
- Multi-shard is **not** a single-process lever (process-global runtime).
- The **top lever is per-request serve latency = the cons-list / owned ABI**, a
  codegen matter; the ceiling is `1 / (serve latency)` and quadratic in body size.
- Absolute req/s here is a contended floor (load ~90–105); re-run idle for the
  clean ~20k-rps-class small-body ceiling the microbench projects.
