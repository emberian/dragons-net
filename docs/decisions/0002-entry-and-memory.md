# 0002. The server runs inside `main` and reaches the host through the FFI

Status: accepted, 2026-09-26.

## Question

Two questions decide whether CakeML's compiler theorem says anything about the running server
([assurance](../assurance.md#open-proof-connections), items 7 and 8): who calls whom — the C
host calling exported Pancake functions, or the program's `main` calling the host — and which
memory the generated code reads and writes.

## What the theorem requires

`pan_to_target_compile_semantics` (CakeML `ed31510`,
`pancake/proofs/pan_to_targetProofScript.sml:1257`) assumes, among others:

- `start = «main»` — the run it describes enters at `main`;
- `s.memaddrs = addresses (mc.target.get_reg ms mc.len_reg) (heap_len-globals_size)` — the
  program's ordinary memory is the heap from `@base` up to `@top`, below the globals;
- `pan_installed ... c'.lab_conf.shmem_extra ... s.memaddrs s.sh_memaddrs` — shared memory has a
  domain of its own, and the machine's initial state is fixed further, as below;
- `semantics_decls s start pan_code ≠ Fail`, for the FFI state `s.ffi` that describes the real
  host.

`pan_installed` (lines 290-326) requires the first five words of the heap to hold the address of
the compiled bitmaps, the two ends of the data buffer after them, and the two ends of the code
buffer. The start-up code CakeML emits writes those words for an ML program only
(`compiler/backend/x64/export_x64Script.sml:49-59`, `if ~pk`); a Pancake program is exported with
`pk = T` (`compiler/compilerScript.sml:747`), and its start-up code reads the words without
anyone having written them. Unless the host writes them, the premise is false on every run.

In the semantics (`pancake/semantics/panSemScript.sml`), a load or store outside `memaddrs` is
`Error`, and a run that reaches `Error` makes the whole semantics `Fail` (`semantics_def`,
line 783), so the last premise is false and the theorem says nothing. An external call reads and
writes its arrays through the same domain (`ExtCall`, lines 714-726). An access to shared memory
is an FFI event, `SharedMem MappedRead` or `MappedWrite`, in the trace (lines 510-547), and is
compiled to one memory instruction (`compiler/backend/lab_to_targetScript.sml:36`). A run that
never returns is `Diverge`, described by its trace of FFI events.

## What upstream and others do

Nothing in `pancake/proofs` mentions exported functions. Multiple entry points arrived in CakeML
pull request #1005 (2024) and were corrected in #1332 (2026: entry points did not save
callee-saved registers on ARMv8, RISC-V and MIPS); neither touches the proofs. The Pancake
drivers of seL4's device driver framework enter through `export fun notified`, outside the
theorem, and their authors say so. They added exported entries because the alternative they
had, branching in `main` on every entry, paid for re-initialisation each time [1]; a loop that
never leaves `main` pays for it once. A main loop is not the common path; it is the one path the
theorem covers.

## Options

1. **Exported step functions, called by C** — what the native lanes do today. Not covered: the
   entry is not `main`, and the host's buffers lie outside `memaddrs`.
2. **The loop in `main`, the host through external calls, buffers in the heap.** Covered: the
   run enters at `main`, its memory is the heap, and every exchange with the host is an FFI event.
3. **Host buffers through shared memory.** Covered by the same theorem and cheap per access, but
   every access is an event in the trace, so reasoning about the bytes becomes reasoning about the
   trace, and the Lean model of the semantics does not have these operations yet.
4. **Extend the upstream proof to exported entries.** A project in HOL of its own, which nobody
   is working on.

## Measurements

`scripts/entry_bench.py` builds the table of `dn_reply` into both designs with the release
compiler. Its `check`, which runs with the baseline, holds what the numbers rest on: every reply
in both designs matches the independent reference; the program writes nothing in its heap outside
its batch areas; the heap header the host writes is the one `pan_installed` requires, recomputed
from the assembly and the linked symbols; every array the program hands the host lies in its
heap; and a host that sends more events than a batch holds, a negative count, a length past its
slot or a negative one, stops the program. Each of these is also shown failing: a loop without
each of its four checks on what the host writes, a program that hands the host an array outside
the heap, a host that leaves the header unwritten and a server whose reply is wrong are all
refused.

`measure` writes `build/entry/report.json`; the run the figures below come from is kept as
[`0002-measurements.json`](0002-measurements.json), which also records the machine, the compiler
and the load, and a gate test holds this table to it. They are medians of five runs (three for
the network) on Linux x86-64, an AMD Ryzen 7 8745HS with 16 hardware threads, with the server and
the client pinned to two different cores, on a quiet machine (a load average of 0.27 at the
start; `measure` refuses a busier one unless asked).

| | exported functions | loop in `main` |
| --- | --- | --- |
| an empty crossing of the boundary | 2.4 ns | 4.1 ns |
| one reply, with the host's bookkeeping | 12.1 ns | 30.8 / 16.8 / 16.1 / 15.6 ns for batches of 1 / 8 / 16 / 64 |
| requests per second over loopback, 1 connection | 87,000 | 86,000 (batch 64), 86,000 (batch 1) |
| 32 connections | 251,000 | 257,000 (batch 64), 250,000 (batch 1) |
| 128 connections | 253,000 | 260,000 (batch 64), 251,000 (batch 1) |

The crossing costs nanoseconds against system calls that cost microseconds. What does cost is a
host that asks the kernel again on every call: fetching one event per call that way ran at
131,000 and 67,000 requests per second with 32 and 128 connections, three quarters lost at the
most. A host that hands out what one `poll` reported before polling again keeps one event per
call within 1 percent of exported functions, and batches of 64 are 2 to 3 percent faster than
those, repeatably. The client is one thread on the same machine, and it and the server each keep
a core busy, so these rows compare the designs, not the hardware.

## Decision

Option 2. The host's side of it:

1. The server is built without `--main_return` and exports no function, so the start-up code
   has no entry but `main` and the runtime cannot be entered twice.
2. Before `cml_main`, the host writes the five heap words `pan_installed` requires: the addresses
   of `cake_bitmaps`, `cake_bitmaps_buffer_begin`, `cake_bitmaps_buffer_end`,
   `cake_codebuffer_begin` and `cake_codebuffer_end`, as the start-up code of an ML program does.
   `cake_bitmaps` is a local label in the emitted assembly, so the build makes it global, which
   changes no instruction. `native/cake_header.c` does both halves: it writes the words, and the
   hosts of the entry benchmark check them before the program's first external call.
3. The program's buffers lie between `@base` and `@top`. Nothing but the program writes there
   except the external call that names an array, and that call writes nothing but the array:
   not its configuration bytes, not the rest of the heap. The same holds for the kernel, other
   threads and signal handlers, so no asynchronous operation may point into the heap. The host
   checks that every array it is given lies there.
4. The host hands out what the kernel has already reported before asking it again; a call may
   return a batch of events, which saves crossings and trace events but not system calls.
5. The host receives straight into the array during the call and sends from it during the call,
   so the loop costs no copy the exported design did not; what a send does not take stays with
   the program until the host reports progress.
6. The host stops the server inside a call, which the model sees as the end of the run, or by
   killing the process, of which the theorem describes only the trace up to that point.

The program's side: it checks every count, length and index the host writes before using it,
and reads nothing in its heap it has not written or been given in a call, so that the premise
`≠ Fail` can be proved for every FFI oracle and every initial content of the heap past its header
rather than for one host and one allocation.

What stays trusted is what CakeML's own statement trusts: that the host's functions behave as the
FFI model the theorem quantifies over, the runtime that sets up heap and stack, and the linker.

## Consequences

- The exported kernels (echo, render, reply) stay as tests of generated code, outside the
  theorem; the NNTP service (#16) is built as a loop in `main`.
- The vocabulary between host and program (#16) takes this shape: events in batches per call,
  with the batch size and a version fixed in the header; connections named by index and
  generation; write progress as an event; sockets owned by the host, buffers by the program.
- An asynchronous interface (io_uring, #9-#15) may neither write into the heap nor read from it
  outside a call. Its completions are copied in during the next call and its sends copied out,
  or its buffers become shared memory (option 3) when the copy has to go.
- The server does not return, so what can be said of it is said of its trace. The theorem allows
  the machine to stop with its resources exhausted at any point unless the stack is at least the
  bound the compiler computes; a server without recursion has one, and it has to be obtained and
  provisioned.
- One `main` is one thread. The runtime's heap and stack are globals of the process, so the
  server scales by processes, or by copies of the runtime under renamed symbols.
- The Lean side has work before any of this is a theorem here: calls and `@top` in the model of
  the semantics, external calls and loops in the emitter for `main`, `≠ Fail` over every clock and
  every oracle, and the step from the clocked model to the trace. The source language
  ([0001](0001-embedding.md)) fits: its theorems take the memory domain as a premise, and buffers
  in the heap satisfy it.
- Assurance items 7 and 8 are answered by design and stay open until the server is built this
  way.

## References

1. J. Zhao et al. Verifying device drivers with Pancake. arXiv:2501.08249, 2025, page 5.
   <https://arxiv.org/abs/2501.08249>
