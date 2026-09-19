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
* Cake runtime memory is allocated once (1 MiB heap and 1 MiB stack), and native entry occurs on one thread. Concurrent entry into that shared runtime is unsupported.

The host is trusted C code compiled with warnings as errors. It is not the optimized dataplane, is not derived from the Rust runtime crate, and is not a formally verified socket adapter. The [baseline](baseline.md) spells out the tests and open connections. The service is TCP byte echo, not NTP and not an NNTP implementation.
