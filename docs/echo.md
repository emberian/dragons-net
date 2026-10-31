# Generated-code TCP echo

The echo server is a small reference host for bringing up the compiler on a real network path. Every received payload passes through `dn_echo`, generated from `DN.Compiler.Kernels.echo`, compiled by CakeML, and linked into the host. There is no interpreted or C-copy fallback.

## Build and run

On Linux x86-64, after `bash scripts/check.sh build`:

```sh
cake=$(python3 scripts/bootstrap_tool.py cake)
python3 scripts/native_baseline.py --cake "$cake"
build/baseline/dn-echo --port 8119
```

The baseline command builds the server and runs its native and socket tests first. The server binds **127.0.0.1** and prints a JSON startup record. Port zero (the default) asks the OS for an available port. For example, in another terminal:

```sh
python3 - <<'PY'
import socket
with socket.create_connection(('127.0.0.1', 8119)) as s:
    s.sendall(b'hello, dragon\x00\r\n')
    s.shutdown(socket.SHUT_WR)
    chunks = []
    while chunk := s.recv(4096):
        chunks.append(chunk)
    print(repr(b''.join(chunks)))
PY
```

SIGINT/SIGTERM stops the server, closes its connections, and prints counters to stderr. This shutdown is immediate, not a promise to drain pending output.

## Contract and limits

* A single-threaded `poll` loop admits at most 32 connections. Additional connections may wait in the OS listen backlog until a slot is free.
* Each connection has one 4 KiB output buffer. Input is read only when pending output has drained, applying backpressure without an unbounded application queue.
* The generated kernel copies up to 4 KiB from a borrowed receive buffer into a disjoint output buffer. The host owns both allocations and checks the returned length.
* Output retains a cursor across sends. Read-half-close is observed after pending output drains; resets and errors release the slot.
* `--idle-ms` sets the inactivity timeout (50–60000 ms, default 30000). `--write-chunk` limits each send to 1–4096 bytes; the integration suite uses 7 to force repeated partial progress.
* Any progress on a connection renews its deadline: bytes received, and bytes sent, including a partial send. A slot still holding a reply expires like any other, so a client that stops reading cannot hold one forever. The counters the server prints on exit report both kinds of renewal and the expiries of slots with pending output.
* A failed `accept` does not cost the connections already being served, except in the one case where the listener itself is unusable and the server stops. Only a listener that cannot work at all (`EBADF`, `EINVAL`, `ENOTSOCK`, `EFAULT`) stops the server; the network errors `accept(2)` says to retry are retried at once, and anything else, including running out of a resource, leaves the listener out of the next polls for a moment. The startup check refuses to run without enough file descriptors for every slot, so the pause path is a guard rather than an expected state.
* `--send-buffer` sets `SO_SNDBUF` on accepted sockets; the integration suite uses a small value to make the handover take many rounds. Renewal on any progress means a client that keeps trickling bytes can hold a slot indefinitely: there is no absolute deadline per connection, and a limit on nearly idle slots is future work.
* The listening socket sets `SO_REUSEADDR`, so a restart does not have to wait out `TIME_WAIT` on a fixed port.
* Cake runtime memory is allocated once (1 MiB heap and 1 MiB stack), and native entry occurs on one thread. Concurrent entry into that shared runtime is unsupported.

## On io_uring

`native/echo_uring.c` serves the same echo on io_uring with the poll host's options, admission and counters, and `tests/echo_integration.py` runs against both. `bash scripts/native_lanes.sh uring` builds and checks it. A send is submitted as soon as the last completes, so a reply reaches the kernel sooner than the poll host's, which waits to be told the socket is writable.

* A thread a core the process may run on, pinned there, at most 8, each with its own ring and copy of the Cake image, since two threads cannot enter one; every global symbol of a copy is prefixed with `copyK_`. `--threads N` sets the count, by default the cores or fewer, to fit the descriptors.
* The main thread owns the listener and the admission count. It accepts only while fewer than 32 connections are held in all, hands each to a thread as a message on that thread's ring, and is told when one is let go.
* A connection keeps one receive or send in flight. Its end of input, an error, its idle deadline or the stop cancels that operation; its descriptor closes only once every completion of it is reaped. A completion's token names its slot's generation, and one for another generation is a violation (status 1).
* SIGTERM or SIGINT stops accepting, stops each thread so, waits for it, and only then closes the rings. Pending replies are not drained. A start that fails once a thread runs stops the threads the same way, with status 1.
* The rings come from `native/uring.c`: io_uring through its system calls, without liburing, opened disabled, restricted to the operations the host submits, then enabled; no flag and no further registration is taken. It needs Linux 6.6, for the newest setup flag it passes.
* io_uring missing or refused (seccomp, `kernel.io_uring_disabled`), an older kernel or a missing feature ends the host at the start with status 1. Nothing falls back to `poll`.
* Nothing is ported from `migration/dataplane`; its [blockers](porting-risks.md) are the design's constraints: a generation in each token, cancellation before close, an ordered stop, bounded tables.

The host is trusted C code compiled with warnings as errors. It is not the optimized dataplane, is not derived from the Rust runtime crate, and is not a formally verified socket adapter. The [baseline](baseline.md) spells out the tests and open connections. The service is TCP byte echo, not NTP and not an NNTP implementation.
