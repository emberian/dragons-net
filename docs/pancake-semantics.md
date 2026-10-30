# The Lean transcription of Pancake's semantics

`lean/DN/Compiler/Semantics.lean` is a hand-written transcription of the Pancake
semantics that lives in HOL4, in the CakeML sources. This document says exactly
what it was compared against, clause by clause, what it leaves out, and which
parts are checked by machine rather than by reading.

The states a run stops in are checked on every run of the checks. `dn-compiler dump-states` prints the bounded corpus of `DN.Compiler.StateCorpus` with what the model makes of each case. `scripts/state_check.py` recomputes each with an independent implementation of these clauses and compares the result constructor, the locals, the memory, the external trace, the base address and the clock.

The write-back clause is compared on its own: an external call reads the region before it writes, so it never reaches a failing write-back. This guards the half of the semantics no differential lane over computed values reaches. HOL4 itself runs the same corpus, below.

## What it was compared against

The clauses live in the CakeML sources, the byte and alignment definitions they
rest on in HOL4's. Every file the tables below cite is recorded in
`backend/lock.json` with its revision and SHA-256, and `scripts/backend.py verify`
re-checks a fetched checkout against them; a pin with no recorded source is an
error, not a silent pass. `scripts/check_upstream_sources.py` fetches the files
themselves by revision, so a recorded digest that never matched upstream is
caught rather than waiting for someone to fetch a checkout; it needs network and
runs on a schedule.

| Source file | Repository | Revision |
| --- | --- | --- |
| `semantics/ffi/ffiScript.sml` | CakeML | `e8eca63`, `ed31510` (identical text) |
| `pancake/semantics/panSemScript.sml` | CakeML | `e8eca63`, `ed31510` |
| `pancake/panLangScript.sml` | CakeML | `e8eca63`, `ed31510` (the `Shift` node differs) |
| `misc/miscScript.sml` (`read_bytearray`) | CakeML | `e8eca63` |
| `compiler/backend/wordLangScript.sml` (`word_op`) | CakeML | `e8eca63` |
| `compiler/encoders/asm/asmScript.sml` (`word_cmp`) | CakeML | `e8eca63` |
| `src/n-bit/byteScript.sml` (`byte_index`, `get_byte`, `set_byte`) | HOL4 | `a9846eb` |
| `src/n-bit/alignmentScript.sml` (`byte_align`) | HOL4 | `a9846eb` |

`e8eca63` is the source revision of the release compiler the native lane runs;
`ed31510` is the revision the curated backend patch applies to.

The two differ in function calls: `e8eca63` keeps a function's return shape in
`code` and checks what a call returns against it, vacuous here, where every
value is one word. They also differ in an exception declaration, which this
subset does not model, and in `Shift`, which it does. Every other clause below
is the same text on both.

At `e8eca63`, `Shift` is `Shift sh e1 e2`, whose distance is an expression read
through `w2n`, and at `ed31510` it is `Shift sh e n`, whose distance is a
literal. The model follows `e8eca63`, the revision the native lane compiles
with, and the gate only accepts a literal distance, so the emitted programs stay
inside the form both grammars accept: the distance is printed bare, because at
`ed31510` the parser takes a literal there and nothing else.

## The modelled subset

The transcription covers what the emitted programs use and nothing else. The
emitter's own gate, `Checked.emit`, refuses a program that uses anything outside
this subset, so the emitted path stays inside it; the model itself simply has no
constructor for the rest.

Left out of `panLang$prog`: `Call`, `Primitive`, `Raise`, `Tick`, `Annot`,
`Break`, `Continue`, `Store32`, `ShMemLoad`, `ShMemStore`. Left out of
`panLang$exp`: structs (`RStruct`, `RField`, `NStruct`, `NField`), `Load` of a
shape other than one word, `Load32`, `Panop` other than multiplication,
`TopAddr`, `BytesInWord`, and `Var Global`.

Of `Shift`, `Lsr` and `Lsl` are modelled; `Asr` and `Ror` are not. Left out of
the state: `globals`, `structs`, `eshapes`, `sh_memaddrs`, `top_addr`; `code`
holds each function's parameters and body.

Values are words: every value the subset produces has shape `One`, so the shape
checks of `Dec`, `Assign` and `Return` are vacuous and the model does not carry
shapes. Memory is a total function to words, not `word_lab`, because the subset
never stores a label.

## Expressions (`eval_def`)

| HOL clause | Lean | Status |
| --- | --- | --- |
| `Const w` | `.const` | same |
| `Var Local v` | `.var` | same: the lookup, so an undeclared variable has no value |
| `BaseAddr` | `.base` | same |
| `Op op es` (arity 2: `Add`, `And`, `Sub`, `Xor`, `Or`) | `.op` | same on the five operators the subset emits |
| `Panop Mul [a;b]` | `.mul` | same |
| `Cmp cmp e1 e2` (`Less`, `Equal`, `NotLess`) | `.cmp` | same, including that `Less`/`NotLess` are signed |
| `LoadByte addr` | `.loadByte` | same: out of domain has no value |
| `Shift Lsr e1 e2`, `Shift Lsl e1 e2` | `.shiftR`, `.shiftL` | same at `e8eca63`, including that a nonzero shift of a whole word or more has no value |
| `Load One addr` | `.loadWord` | same: out of domain has no value |

## Programs (`evaluate_def`)

| HOL clause | Lean | Status |
| --- | --- | --- |
| `Skip` | `.skip` | same |
| `Dec v sh e prog` | `.dec` | same, less the vacuous shape check; the old binding is restored by `res_var` |
| `Assign vk v src` | `.assign` | same: `is_valid_value` needs the variable to be bound already, so assigning to an undeclared variable is an error |
| `Store dst src` | `.store` | same for the one-word value the subset stores |
| `StoreByte dst src` | `.storeByte` | same, including the low-byte truncation |
| `Seq c1 c2` | `.seq` | same, with `fix_clock` inlined as the clock clamp |
| `If e c1 c2` | `.cond` | same: zero is false, anything else is true |
| `While e c` | `.while_` | same: the clock is spent per iteration, `Break` leaves, `Continue` and normal completion loop, no clock is a timeout that empties the locals |
| `Return e` | `.ret` | same, less the vacuous size check |
| `ExtCall name ptr1 len1 ptr2 len2` | `.extCall` | same, through `callFFI` |
| `DecCall rt One f args prog1` | `.decCall` | same, less the vacuous shape check: the arguments through `OPT_MMAP` (`evalArgs`), the body through `lookup_code` (`lookupCode`), no clock a timeout, the body on its own locals with one tick less |
| `DecCall`, how the body ends | `.decCall`, `callEnded` | same: a `Return` binds `rt` for `prog1`, restored after; ending without a result, `Break` or `Continue` is an `Error` in the body's state, anything else ends with the locals emptied |

## Helpers

| HOL definition | Lean | Status |
| --- | --- | --- |
| `byte_align`, `byte_index`, `get_byte`, `set_byte` | `byteAlign`, `byteIndex`, `getByte`, `setByte` | same |
| `mem_load_byte`, `mem_store_byte` | `memLoadByte`, `memStoreByte` | same |
| `mem_store` (through `mem_stores` on one word) | `memStoreWord` | same for the single-word case |
| `read_bytearray` | `readByteArray` | same: any unreadable byte gives no array |
| `write_bytearray` | `writeByteArray` | same, including that a store out of range keeps the memory the call was given and so drops the writes of the tail |
| `set_var`, `res_var`, `empty_locals`, `dec_clock` | `setLocal`, `resVar`, `emptyLocals`, `decClock` | same |
| `fix_clock` | `clampClock`, inlined at the recursive boundaries | same clamp |
| `lookup_code`, `OPT_MMAP (eval s)` | `lookupCode`, `evalArgs` | same: distinct parameters, as many as the arguments, every value one word |
| `call_FFI` | `callFFI` | same: the empty name does not reach the oracle, and a reply whose length differs from the array ends the run |

## What the model does not carry

- **The IO trace.** `call_FFI` appends an `IO_event` to `io_events`; the model
  only threads the oracle's own state. Nothing here states a property of the
  trace, and a claim about observable behaviour would need it.
- **Labels in memory and shapes in values**, as described above.
- **The oracle's faithfulness to a real host.** The oracle is the assumption at
  the boundary: the model says what the program does with whatever the oracle
  answers, not what a C host will answer.

## What is checked by machine

Every branch where the semantics stops instead of carrying on is pinned by a
theorem in `Semantics.lean`, so a later edit that quietly makes the model more
permissive fails the build:

- reading an undeclared variable, an operand without a value, a byte or word
  load outside the memory domain;
- a declaration whose initialiser has no value; an assignment to an undeclared
  variable or without a value; a store, byte store, condition, loop guard or
  return without a value; a store or byte store outside the memory domain;
- a loop that runs out of clock;
- a call with an argument too many, of a function the code lacks, or of a body that ends
  without returning; a call that returns binds what it returns (`call_returns`, `call_errors`);
- an external call whose pointers or lengths have no value, whose configuration
  bytes cannot be read, or whose array cannot be read;
- at the external call itself: a reply that is too long ends the run, a reply of
  the declared length is written, and a reply that is accepted cannot disturb a
  byte outside the array (`Bytes.extCall_frame`, in `Bytes.lean`);
- in `callFFI`: a reply that is too long or too short, an oracle that ends the
  run, and the empty call name that never reaches the oracle.

Where an external call carries on, `Bytes.extCall_keeps` pins the rest of its
clause as a `Bytes.Frame`, the one form every "what a run leaves alone" statement
here takes: it changes the bytes of its array and the external world's state, and
leaves every local, the memory domain, the byte order, the base address and the
clock as they were.

The correspondence itself — that each clause above matches the HOL text — rests
on reading the recorded files at the recorded digests, on the run below, and on a
HOL copy of the model proven equal to `panSem`. The step from the Lean text to that
copy is read and run on the corpus, not proved.

## Run by HOL4

`scripts/check_semantics.sh` runs every case of the corpus through `panSem`'s own
`evaluate`, under `EVAL`, in the backend's CakeML tree at `ed31510`, and compares
each printed field with the model's. `backend/semantics/states.txt` is the corpus as the model
prints it; the state lane holds it equal to the printer.

`scripts/semantics_check.py` writes each case's input as a HOL term, the model's
answer left out. HOL's answer is a theorem about that term, printed in the dump's
form by `backend/semantics/dnShowScript.sml`.

A second run reads subtraction as addition and must disagree, and only where a
case subtracts. The backend workflow runs the lane: 146 cases and 6 write-backs
agree, with each way a call of the subset ends, in its body and after it.

Where `e8eca63` and `ed31510` differ, the model follows `e8eca63` and is not run
by HOL: a shift is compared at literal distances only, and the return-shape check
of a call, vacuous here, is `ed31510`'s.

## Proved in HOL4

`backend/semantics/dnModelScript.sml` is the model written again in HOL, clause by
clause: the same constructors, helpers and matches, words as `word64`. On the
subset with literal shift distances, the only ones the gate accepts,
`dnModelProofScript.sml` proves it equal to `panSem`'s `evaluate` at `ed31510`,
from every panSem state related to a model state:

- `dn_set_byte_thm` and its kin: the byte helpers are HOL's own;
- `dn_eval_thm`: an expression has the same word in both, or none in both;
- `dn_sem_thm`: a run ends with the same result, in related states: the same
  locals, memory, domain, byte order, base address, clock, oracle state and code.

The lane builds the proof, asks the prover that it rests on no oracle, and runs
the HOL copy on the corpus beside `panSem`: the same 146 cases and 6 write-backs
agree. That run and reading the two side by side tie the HOL text to the Lean one;
neither is a proof.

A related state holds words only in memory and locals, finite maps of locals and
code, and only subset bodies; its oracle is the model's on external calls and
fails a shared-memory call.

The relation leaves out `io_events`, the oracle's record of calls, which the Lean
model does not keep, and the fields the subset never reads. The proof covers
`Break` and `Continue`, which no subset program reaches.
