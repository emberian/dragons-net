# Porting risks in the preserved dataplane

`migration/dataplane` is a snapshot kept for extraction, not a build target: its bytes are the bytes
it arrived with, and `scripts/check_structure.py` refuses a change to them. Reading it is useful —
it is a working io_uring and kqueue reactor with a real workload behind it — but most of its
lifetime and ownership decisions cannot be carried over as they are. This document says which, and
what the port has to do instead, so that the answer is decided before the code is moved rather than
after it misbehaves.

The distinction that runs through all of it: **a submitted operation holds a reference into user
memory until its completion is reaped**, and nothing about closing a descriptor, dropping a
structure or unwinding a panic changes that. `io_uring_cancelation(7)`: "When a file descriptor is
closed (either via close(2) or IORING_OP_CLOSE), pending requests operating on that fd are *not*
automatically canceled … the pending read, recv, or other operation continues to hold a reference."

## Blockers: redesign before the code runs again

**A timeout frees memory the kernel still points at.** `host/src/uring.rs` sweeps proxy timeouts by
dropping the dial state and calling `close(2)` on the upstream descriptor while receives and sends
are still in flight, and in the streaming path the deadline that fires belongs to a different
operation than the one that is running. The man page settles the first consequence: the socket is
not really closed while an operation still holds it. The code settles the other two — the sweep
drops the buffers the outstanding submissions name, the dial's receive vector and its connect
address, and the close returns the connection's response buffer to the pool while a send is still in
flight. A port needs an explicit cancellation state: cancel by user data or by descriptor
(`IORING_ASYNC_CANCEL_FD|ALL`), keep the buffers and the slot until the terminal completion — and,
for zero-copy sends, until the notification — and only then close. A deadline has to be attached to
the operation it governs (`IORING_OP_LINK_TIMEOUT`), not to the connection as a whole.

**The completion token carries only a tag and a bare index.** After any early close the slot returns
to the free list, so a late completion of the old operation is applied to whoever owns the slot now.
The token has to identify the incarnation: shard, slot, connection generation and operation
generation, or an index into a separate operation table with its own generation, checked before the
completion is dispatched. The model of this check is `DN.Dataplane.Io.Slab`; the token layout that
keeps the namespaces apart is `DN.Dataplane.Flow.Token`.

**Responses are addressed by slot index.** Both reactors look a connection up by index alone when a
worker's reply arrives, so the new owner of a slot receives another connection's bytes. A response
has to carry an opaque token that names the connection incarnation and the request; a cancelled
request invalidates its generation, and a reply with a stale token is dropped.

**Zero-copy receive hands a raw pointer to another thread.** The buffer lease is returned to the
kernel on close, and on shard exit the ring's memory is unmapped before its descriptor is closed —
the registration outlives its mapping — while a worker may still be reading through that pointer.
The lease has to be an owning object whose lifetime ends when the reply has come back and the
connection is finished with it; `models/borrow-recycle` is the model of that discipline.

**There is no shutdown protocol.** Normal exit, an error and a panic all free memory that submitted
operations still reference. A port needs a state machine: stop accepting, cancel everything
(`IORING_ASYNC_CANCEL_ANY|ALL`), reap every terminal completion and notification, unregister the
buffer ring, unmap it, and only then close descriptors and release buffers.

**Buffer-ring ownership rests on convention.** Nothing checks that a buffer handed back to the
kernel is not still leased, and the kernel does not check it either: a recycled buffer that is still
being read is silently shared. Ownership has to be a value with states — free, or leased with a
generation — recycled only through that value, with the checks compiled in release builds too. The
ring's own sizing needs checking as well: a buffer size that does not fit the advertised 32-bit
length, or an entry count times buffer size that overflows, publishes a record the kernel will go on
to use.

**Nothing bounds live memory, queues or threads.** The pool grows, the queues are unbounded, and the
thread count follows the load. A port needs permits for bytes, jobs, connections and leases, bounded
channels that refuse rather than grow, and a pool with a fixed ceiling; `crates/dn-runtime` holds
the admission gate this project already uses.

**The C adapter to the compiled images is fail-open.** A capacity larger than the output buffer is
accepted and read past — no caller in the snapshot passes one, so that is a hazard of the interface
rather than a read happening today — a request pointer is dereferenced before it is checked for
null, and the Rust side never checks the returned length itself: it is saved only because the C side
clamps it and the truncation that follows saturates. The port needs one versioned ABI header: a
status code plus an output slot, the output capacity passed in and enforced, and every pointer
checked before use. The active native lane already passes the capacity in and writes through a
checked output slot (`native/`, `DN.Compiler.Abi`); the version and the status code are not there
either.

## To change while porting

**Panic isolation ignores kernel lifetimes.** Catching a panic and closing the connection leaves
whatever the handler had already submitted pointing into its buffers. Either the reactor thread
aborts on panic, or the connection is quarantined: mark it broken, cancel its operations, and
release memory only after the terminal completions. A panic in the accept or the wakeup handler is
followed by no reap at all, so an admission count taken when the connection was accepted is never
given back, and the gate closes against that source for good.

**A panic inside the wakeup handler disables the shard's reply channel.** The read of the event
descriptor is re-armed after the handlers run, so a panic anywhere in the loop stops the shard from
ever learning about replies again. Re-arm first, handle each reply in isolation, and put a bound on
the handler.

**One pipe per shard for static sends interleaves connections.** Concurrent static responses share a
single pipe and their bytes mix. A pipe per connection, a queue that allows one static send per
shard at a time, or a splice path without a shared pipe.

**Blocking work runs on the reactor thread and on the owner of the worker seam.** One slow client or
upstream stalls the whole shard, and one TLS connection occupies the seam owner. The reactor must
only perform non-blocking operations through the ring, and calls into the service have to be
asynchronous.

**The submission error policy loses the shard.** Any error from `io_uring_enter(2)` ends the shard,
with every leak above — including `EBADR`, which says completions were dropped, and `EAGAIN`, which
is backpressure. The completion queue also has to be sized for the maximum number of operations in
flight (`IORING_SETUP_CQSIZE`), which ties it to the connection limit.

**Accept spins when descriptors run out.** On `EMFILE` or `ENFILE` the accept is resubmitted
immediately and fails immediately, which is a completion storm at full CPU. Pause with a timer, or
keep a reserve descriptor to close and retry with, and count the event; the active host already
decides this way in `native/accept_policy.h`.

**Splice always goes to the worker pool.** `IORING_OP_SPLICE` runs in a blocking worker, so a fill
on an idle socket holds a kernel thread. Bound the workers (`IORING_REGISTER_IOWQ_MAX_WORKERS`),
give the transfers idle timeouts, and on an error in one direction shut down and cancel the other.

**Durability uses a descriptor reopened by path.** The write is flushed through a second descriptor
opened on the name, so it is not the file the data was written to if the name moved. Flush the same
descriptor that was written, before closing it, and treat a failed flush as a lost write: the
acceptance is not confirmed.

**Request assembly is quadratic and the body phase has no deadline.** Every receive copies and
rescans a buffer that may reach megabytes, and a slow body keeps the connection. NNTP needs
incremental framing with a saved offset anyway — multi-line commands and dot-stuffing make it
compulsory — and the body phase needs its own deadline.

**Streaming replies are recomputed per chunk.** The pure seam recomputes the answer for each chunk,
so the work grows as chunks times the cost of the answer. Keep a cursor, and stream large articles
from storage.

**SIGPIPE protection rests on the language runtime where the ring does not cover it.** The ring's
sends are safe — io_uring passes `MSG_NOSIGNAL` itself — and the kqueue path ignores the signal
explicitly, but the blocking path's `sendfile(2)` and its ordinary socket writes rely on the Rust
runtime having ignored SIGPIPE before `main`. A host that is not a Rust binary has to ignore it
itself.

**Kernel capabilities are not probed.** On kernels where zero-copy send or an extended argument is
missing, the shard either fails every send or dies at the first wait. Probe
(`IORING_REGISTER_PROBE`) and refuse to start with a clear message.

**The kqueue path repeats the same identity mistakes.** Registration errors arrive in the event list
and are handled as readiness, the user datum is the slot index, and deletions are deferred until
after the descriptor has been handed on. Check the error flag, put a generation in the datum, and
apply deletions with their own call before the descriptor is reused.

**Worker supervision is by signal.** A failed initial spawn silently reduces capacity and shutdown
is by `SIGKILL`. Send the terminating signal, wait, then kill; a kill is a fault in the model, not a
normal path.

**A raw descriptor number is used to wake another thread.** It is safe today only because the event
descriptor leaks on every restart. Hold an owning descriptor and check the result of the write.

**Close-on-exec is not set everywhere.** Any fork and exec inherits listening and client sockets.
Set it on every descriptor, and accept with the non-blocking and close-on-exec flags.

**The blocking host has no write timeouts and its rate-limit map grows.** A slow reader occupies one
of its threads indefinitely, and the map is only swept in some modes. Add write deadlines, sweep in
every mode, and group IPv6 clients by prefix rather than by address.

**Two details of the active code belong to the same family.** The token in
`crates/dn-runtime/src/slab.rs` has no mark for which table or shard it belongs to, and a completion
of length zero in `crates/dn-runtime/src/output.rs` does not distinguish a retry, an end of file and
a cancellation. The io_uring model that fits is the one where a buffer is *lent* to the operation
and comes back with its completion.

## How the models relate to this list

The Lean models under `lean/DN/Dataplane` are the specifications these risks argue for: a
generation-tagged store whose stale keys stay rejected for the rest of a trace, a deadline queue
that fires the earliest live deadline and keeps its tombstones bounded, a wakeup discipline that
loses no message, flow control that refuses rather than grows. None of them is connected by a
refinement theorem to the snapshot or to any reactor — that connection is the work, and this list is
what it has to account for.
