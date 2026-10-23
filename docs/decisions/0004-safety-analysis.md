# 0004. A safety analysis proven sound once, for the session's program

Status: accepted, 2026-09-28; amended while the slice was built, 2026-09-29.

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
  is addressed by. A condition cuts the range of a local or such a word it compares, or of `x` in
  `x + k` for a constant `k` when adding it cannot leave the words. Accesses must lie in a heap of
  the layout's size, words on word boundaries, and above its first 64 bytes, which hold the header
  CakeML's theorem fixes.
- A loop's invariant is searched for — joins, widening up to the guard, then widening — and then
  checked to hold on entry and to be kept by the body. Only the check is proven; the search can be
  changed freely.
- Functions are analysed in the order defined, each from any arguments, and may call only those
  before it: a call gives any word and forgets the cells. `checkProgram` takes a program so, and
  `program_never_fails` proves it from code holding its functions. A certificate takes calls too:
  each function has one, and claims of its own (`programC_never_fails`).
- The analysis is written in structural recursion over `Nat` and `Int`, so the kernel reduces it.
  `dn-compiler analyze-session` runs the same analysis compiled and names the first alarm, which
  the kernel does not.
- Where intervals cannot see why an access is safe, the program is changed rather than the
  analysis: each action has the slot of its connection, so no slot number depends on a count, and
  each word the program reads back from its own area and uses as a length or a position is checked
  to be in the range the program keeps it in, stopping with code 10 otherwise; the echo loop
  checks its count of actions against the batch, though its count of events already bounds it.

## Consequences

- `DN.Server.SkeletonSafe` proves by one run of the analysis that no run of its program fails
  (`never_fails`, `printed_never_fails`); `DN.Server.SessionSafe` and `DN.News.RecoverSafe` prove it
  by the claims of a certificate (below). The premise, `Covers`, asks
  for the heap's words from byte 64 up to the layout's size. It holds of the memory
  CakeML's theorem gives a program (`addresses base (heap_len - globals_size)`) when `@base` is on
  a word boundary and the heap has at least the layout's words: `covers_heap` proves it of such a
  set of words, and `covers_mono` of any memory that holds them.
- Within one declaration the kernel keeps every step of its reduction, so its memory grows with
  the locals in scope times the statements analyzed: one run on recovery's step took 18 GB, above
  the CI runner's 16.
- `DN.Compiler.AnalyzerCert` cuts the analysis along the program's structure, a certificate giving
  the state each piece ends in and the invariant of every loop; `analyzeC` checks the cuts as
  `analyze` checks its own (the result-checking of Besson, Jensen and Pichardie, ref. 3), and
  `DN.Compiler.AnalyzerCertSound` proves once that the claims holding make the program as safe.
- The claims are checked in runs, a declaration each, of a cost the kernel bears; `dn-compiler
  analysis-cert` prints the modules, `scripts/analysis_cert.py` writes them, a test keeps them
  current. Recovery's step alone takes 8 declarations (about 30 s). The session's program, 223
  functions, is written out as it lowers, which declarations hold to the lowering 20 functions at a
  time: the kernel computes a function from the program's source, up to 4.4 GB for one. Its 32
  declarations are dealt to two modules the build checks side by side, 177 s and 10.6 GB together.
  The build and `leanchecker` print their time and largest process on every run
  (`scripts/measured.py`), so that the cost shows as the program grows.
- What is not proven stays as 0003 lists it: the transcription of the semantics, the parser, the
  stack bound, and anything about the program's behaviour beyond not failing.

## References

1. Jourdan, Laporte, Blazy, Leroy, Pichardie. A Formally-Verified C Static Analyzer. POPL 2015.
2. CakeML `ed31510`, `pancake/proofs/pan_to_targetProofScript.sml`: the memory the compiler's
   theorem gives a program.
3. Besson, Jensen, Pichardie. Proof-carrying code from certified abstract interpretation and
   fixpoint compression. Theoretical Computer Science 364(3), 2006.
