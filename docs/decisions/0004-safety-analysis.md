# 0004. A safety analysis proven sound once, for the session's program

Status: accepted, 2026-09-28.

## Question

Decision [0003](0003-nntp-slice.md) asks for a theorem that no run of the server's `main` fails.
For the loop that echoes payloads (`DN.Server.Skeleton`) it was proven by hand, statement by
statement, with the rules of `DN.Compiler.Safe` (`DN.Server.SkeletonSafe`): about 600 lines for 45
statements, which any change to the program breaks. The session's program is a thousand statements
and 42 loops, and it will grow with the store of #17. How is its theorem obtained?

## Decision

A static analysis of the model's Pancake subset (`DN.Compiler.Analyzer`), proven sound once
(`DN.Compiler.AnalyzerSound`) and run on the program by the kernel (`decide +kernel`) — the way
Verasco checks C programs with analyses proven against CompCert's semantics.

- A word is an interval of its signed value, or, for an address, of its offset from `@base`, with
  the remainder by eight when it is known. A load gives any value, except a word whose range a
  condition has just checked, which keeps it until the next store, call, or change of the local it
  is addressed by. Accesses must lie in a heap of the layout's size, words on word boundaries.
- A loop's invariant is searched for — joins, widening up to the guard, then widening — and then
  checked to hold on entry and to be kept by the body. Only the check is proven; the search can be
  changed freely.
- The analysis is written in structural recursion over `Nat` and `Int`, so the kernel reduces it.
  `dn-compiler analyze-session` runs the same analysis compiled and names the first alarm, which
  the kernel does not.
- Where intervals cannot see why an access is safe, the program is changed rather than the
  analysis: each action has the slot of its connection, so no slot number depends on a count, and
  each word the program reads back from its own area and uses as a length or a position is checked
  to be in the range the program keeps it in, stopping with code 10 otherwise.

## Consequences

- `DN.Server.SessionSafe.never_fails` and `printed_never_fails` state for the session what
  `SkeletonSafe` states for the echo loop. The premise, `Covers`, holds of the memory CakeML's
  theorem gives a program (`addresses base (heap_len - globals_size)`) when `@base` is on a word
  boundary and the heap has the layout's words; `covers_heap` proves it of such a set of words.
- The check costs about a minute in the build and another in `leanchecker`, about two in nanoda,
  and about 10 GB of memory while it runs; it grows with the program.
- The skeleton keeps its proof by hand: a counter bounded by another counter is beyond intervals.
- What is not proven stays as 0003 lists it: the transcription of the semantics, the parser, the
  stack bound, and anything about the program's behaviour beyond not failing.

## References

1. Jourdan, Laporte, Blazy, Leroy, Pichardie. A Formally-Verified C Static Analyzer. POPL 2015.
2. CakeML `ed31510`, `pancake/proofs/pan_to_targetProofScript.sml`: the memory the compiler's
   theorem gives a program.
