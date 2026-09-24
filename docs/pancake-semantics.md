# The Lean transcription of Pancake's semantics

`lean/DN/Compiler/Semantics.lean` is a hand-written transcription of the Pancake
semantics that lives in HOL4, in the CakeML sources. This document says exactly
what it was compared against, clause by clause, what it leaves out, and which
parts are checked by machine rather than by reading.

The states a run stops in are compared against an independent implementation of these clauses on every run of the checks: `DN.Compiler.StateCorpus` prints a bounded corpus with what the model makes of each case, and `scripts/state_check.py` recomputes it and compares the result constructor, the locals, the memory, the external trace, the base address and the clock; the write-back clause is compared on its own, because an external call reads the region before it writes and so never reaches a failing write-back. That is a guard against drift in the half of the semantics no differential lane over computed values can reach; it is not a connection to the HOL source, which remains the open obligation below.

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
`ed31510` is the revision the curated backend patch applies to. The two differ in
function calls (return shapes in `code` and `lookup_code`), in an exception
declaration, in the type of `code` — none of which this subset models — and in
`Shift`, which it does. Every other clause below is the same text on both.

`Shift` is the one clause that differs: at `e8eca63` it is `Shift sh e1 e2`, whose
distance is an expression read through `w2n`, and at `ed31510` it is `Shift sh e n`,
whose distance is a literal. The model follows `e8eca63`, the revision the native
lane compiles with, and the gate only accepts a literal distance, so the emitted
programs stay inside the form both grammars accept: the distance is printed bare,
because at `ed31510` the parser takes a literal there and nothing else.

## The modelled subset

The transcription covers what the emitted programs use and nothing else. The
emitter's own gate, `Checked.emit`, refuses a program that uses anything outside
this subset, so the emitted path stays inside it; the model itself simply has no
constructor for the rest.

Left out of `panLang$prog`: `Call`, `DecCall`, `Primitive`, `Raise`, `Tick`,
`Annot`, `Break`, `Continue`, `Store32`, `ShMemLoad`, `ShMemStore`. Left out of
`panLang$exp`: structs (`RStruct`, `RField`, `NStruct`, `NField`), `Load` of a
shape other than one word, `Load32`, `Panop` other than multiplication, `TopAddr`,
`BytesInWord`, and `Var Global`. Of `Shift`, only the logical right shift (`Lsr`) is
modelled; `Lsl`, `Asr` and `Ror` are not. Left out of the state: `globals`,
`structs`, `code`, `eshapes`, `sh_memaddrs`, `top_addr`.

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
| `Op op es` (arity 2: `Add`, `And`, `Sub`) | `.op` | same on the three operators the subset emits |
| `Panop Mul [a;b]` | `.mul` | same |
| `Cmp cmp e1 e2` (`Less`, `Equal`, `NotLess`) | `.cmp` | same, including that `Less`/`NotLess` are signed |
| `LoadByte addr` | `.loadByte` | same: out of domain has no value |
| `Shift Lsr e1 e2` | `.shiftR` | same at `e8eca63`, including that a nonzero shift of a whole word or more has no value |
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
- an external call whose pointers or lengths have no value, whose configuration
  bytes cannot be read, or whose array cannot be read;
- at the external call itself: a reply that is too long ends the run, a reply of
  the declared length is written, and a reply that is accepted cannot disturb a
  byte outside the array (`Bytes.extCall_frame`);
- in `callFFI`: a reply that is too long or too short, an oracle that ends the
  run, and the empty call name that never reaches the oracle.

The correspondence itself — that each clause above matches the HOL text — rests
on reading the recorded files at the recorded digests. It is not machine-checked,
and a bridge to HOL4 remains the open item.
