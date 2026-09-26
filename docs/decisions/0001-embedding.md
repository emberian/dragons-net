# 0001. The source language is a deep embedding

Status: accepted, 2026-09-25.

## Question

Protocol code has to reach Pancake from Lean. Either it is written as ordinary Lean functions
and Pancake is obtained from them (a shallow embedding), or programs are values of a Lean type
that a Lean function compiles, with one proof that the compiler is right for all of them (a deep
embedding).

## What was already there

The compiler below the source language is deep already. `DN.Compiler.Syntax` is the printed
Pancake subset as a Lean type; `Checked.emit` gates it and prints it; `Lower` maps it onto the
model of the semantics (`DN.Compiler.Semantics`). Every emitted kernel so far is written directly
in that type and proved on its own: the decimal render (`dn_render`) takes 953 lines in
`NatToDec.lean` for one program, besides `Div10.lean` and `Decimal.lean`.

## Options

The trade-off is the familiar one [1][2]; what decides it here is the project's own constraints.

**Shallow, with an extractor.** Protocol code is Lean functions, and a tool reads their terms and
prints Pancake. Reading Lean terms is metaprogramming. Run while the library is built, it is
what the source gate refuses — custom elaborators, `run_tac`, `#eval` — because building the
library must not run code from it. Run outside the build, the extractor is trusted and unproved,
as KaRaMeL is for Low* [4], whose translation to C is proved on paper. Either way no theorem
connects the printed program to the function it came from.

**Shallow, with a proof-producing translation.** Each function is translated together with a
theorem that the translation means the same. CakeML's translator does this from HOL functions to
CakeML [3]; Rupicola does it from Coq functions to Bedrock2 by relational compilation [5]: the
target program is found by proof search over a library of compilation lemmas, and the kernel
checks every result. Nothing has to run at build time for this — a program of the language
below can be found by unification against lemmas about `Act.run`, and the kernel checks that it
computes the function. But it needs a target with a meaning and a lemma for every construct,
and that target is what the deep option builds.

**Deep.** An inductive type of programs, a denotation (`Act.run`, a Lean function giving each
program its meaning) and a compiler (`Act.compile`). One theorem, by induction over the type,
covers every program. The cost moves to the language: each construct needs its compile case and
its proof case before it can be used, so the language stays small and closed.

**Deep with a surface syntax.** Notation or macros over the deep type. This is independent of
the choice: syntax definitions are allowed in files the source gate pins by hash, and can come
later without changing the core.

## Decision

Deep, now. A proof-producing translation from shallow functions can be added over it later, and
would need it.

`lean/DN/Dsl` holds the language and its proof:

- `Action.lean`: `Act` with three constructors — append a byte literal, branch on whether the
  input starts with a keyword, sequence — its denotation `Act.run`, and `Act.compile` into the
  existing print-level syntax. Everything after that point (the gate, the printer, the lowering,
  the native lanes) is shared with the hand-written kernels. `respond` wraps an action as an
  exported function `name(inp, inlen, out, cap)`, and `emit` refuses an action the theorems do
  not cover (`emit_ok`).
- `Correct.lean`: `Act.compile_run`, for every action: the compiled code writes what `Act.run`
  says at the output cursor and changes nothing but its two working locals and the bytes it
  writes. `respond_correct`: the exported function returns the reply's length, below the refusal
  value, with the reply at the start of the buffer, memory outside the reply unchanged, and the
  same memory domain, byte order, clock and FFI state. `respond_refuses`: a negative length, or a
  buffer smaller than `Act.maxLen`, the most the action can write, is refused before anything is
  written. All of it is stated about the model of the semantics.
- `Example.lean`: a reply table emitted as `dn_reply`, a closed instance of `respond_correct`
  on a concrete call in the model (`quitCall_reply`), and the witnesses the audit requires for
  the predicates the theorems assume.

The proof is `Correct.lean` (683 lines) and three lemmas in `Action.lean`, and it uses no axiom
beyond the three the audit allows. A new program costs no proof of its own: `quitCall_reply`
applies the theorem to a concrete call in a dozen lines. That is not a like-for-like comparison
with the render, which has a loop and arithmetic the language does not have yet; it shows where
the cost goes. The release compiler and the compiler bootstrapped from the patched source
compile `dn_reply` to the same assembly, and the native lane checks 5,840 calls of it against
both the Lean denotation and an independent Python reference ([baseline](../baseline.md)).

## How the proof is built

- `PancakeSem` is defined by well-founded recursion, and Lean's derivation of a functional
  induction principle fails on it. The proofs therefore go by induction over `Act`, and each
  statement has continuation form: the code of an action followed by `rest` runs as `rest` does
  from the state the action leaves. Statement lists lower right-nested (`x :: rest` becomes
  `Seq x rest`), so this form also needs no lemma about lowering a concatenation.
- The state the code works in is one invariant, `Rep` (parameters bound, input bytes at `inp`,
  bytes written so far at `out`, cursor in `pos`, the buffer addressable and apart from the
  input), and what a step leaves alone is one frame, `Keeps`, bounded by the bytes written.
- `Act.compile_refinesClk` restates the theorem as `RefinesClk`, the form `Certificate` takes.
  Composing certificates builds a `Seq` in the model, which is not how `respond` prints a
  program, so this serves reasoning in the model and not yet the emitted code.
- The two working locals are declared once, before the body: Pancake warns about a
  redeclaration and the gate refuses it. A branch evaluates its condition before either arm
  runs, so every keyword test can reuse the one flag.

## What the theorem does not cover

It is a theorem about the model, and each link from the model to the running code is one of the
[open connections](../assurance.md#open-proof-connections):

- The semantics it is proved against is a transcription of the HOL definitions, compared clause
  by clause and not connected by a proof (item 1).
- The printed source against CakeML's parser (item 2,
  [#4](https://github.com/emberian/dragons-net/issues/4)): the parser folds `a + b + c` into one
  n-ary operation and wraps statements, and agreement is tested, not proven.
- The 32-bit result (item 5): the theorem puts the length below `2^32 - 1`; that the C caller
  receives it whole rests on the ABI adapter.
- The CakeML theorem is stated for `main` only, and the host's buffers lie outside the memory
  domain it admits (items 7 and 8). The theorems here take the memory domain as a premise
  (`memaddrs` covers the buffers), so they hold for whichever domain that decision fixes. If the
  buffers have to be reached through the shared-memory operations instead, the lowering of loads
  and stores changes, and the model of the semantics has to gain those operations first.

## Consequences

- A construct enters the language together with its compile case, its proof case and native
  cases, never before.
- The example matches keywords as exact byte prefixes. NNTP keywords are case-insensitive and
  end at a word boundary; those are the next constructors, followed by bounded loops over the
  input (`while_inv_cond_clk`, where the clock stops being unchanged and becomes a budget),
  session fields in memory and calls to the host.
- Literals are stored a byte at a time: simple to prove, and a candidate for word stores once
  the language is used in anger.
- The reply's length is returned through the 32-bit C result, so `emit` refuses an action
  whose longest reply reaches the refusal value `2^32 - 1`.
- Once the language covers a protocol step, writing that step as an ordinary Lean function and
  finding its `Act` by proof search, as Rupicola does, becomes possible without changing the
  core.

## References

1. J. Gibbons, N. Wu. Folding domain-specific languages: deep and shallow embeddings. ICFP 2014.
   <https://doi.org/10.1145/2628136.2628138>
2. J. Svenningsson, E. Axelsson. Combining deep and shallow embedding of domain-specific
   languages. Computer Languages, Systems & Structures 44, 2015.
   <https://doi.org/10.1016/j.cl.2015.07.003>
3. M. O. Myreen, S. Owens. Proof-producing synthesis of ML from higher-order logic. ICFP 2012.
   <https://doi.org/10.1145/2364527.2364545>
4. J. Protzenko et al. Verified low-level programming embedded in F*. ICFP 2017.
   <https://doi.org/10.1145/3110261>
5. Relational compilation for performance-critical applications: extensible proof-producing
   translation of functional models into low-level code (Rupicola). PLDI 2022.
   <https://doi.org/10.1145/3519939.3523706>
