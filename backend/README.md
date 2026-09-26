# Curated backend work

This directory preserves the useful committed portion of the datacake experiment: primitive dead-code elimination with preservation work, plus counterexamples showing why shared-memory operations cannot be eliminated by the same reasoning. Unfinished Div/Mod changes were excluded.

`lock.json` pins the CakeML and HOL source revisions and the patch digest. `LICENSE.CakeML` retains the upstream BSD license. The rebuild below has been run here: from a clean tree, the chain up to `pan_to_target_compile_semantics` and its tag check took 46 minutes on twelve jobs of a 16-core machine, the prover and its compiler 12 minutes, and the theorem came back carrying no oracle. That is one machine and one run; it is not a claim that the patch is correct, only that its proof goes through.

## Fetch and inspect

From the repository root:

```sh
python3 scripts/backend.py fetch cakeml
python3 scripts/backend.py fetch hol
python3 scripts/backend.py verify cakeml
python3 scripts/backend.py verify hol
```

Fetch refuses to overwrite an existing checkout. Verification compares the tracked source with the exact revision plus the curated patch and rejects unexpected untracked files. For the CakeML tree it also refuses build outputs that upstream Git rules ignore (`*.uo`, `*Theory.sml`, `.HOLMK`, ...), because a stale or substituted theory object would let Holmake treat a target as already built; `scripts/check_backend.sh` removes them (`git clean -fdX`) before it verifies and rebuilds. The prover's own build outputs in the HOL tree are expected and are not certified by this check — what is certified is the source they were built from.

## Rebuild the proof

From the repository root:

```sh
python3 scripts/backend.py fetch hol
python3 scripts/backend.py build hol
bash scripts/check_backend.sh
```

`build hol` builds the prover with the Poly/ML pinned in `tools.lock.json`, which the bootstrap builds from its own pinned source outside the checkout, with GMP and the integer representation decided by the lock rather than by whatever the machine happens to carry. `check_backend.sh` then asks the prover what it was built with: `smart-configure` writes `POLY` and `HOLDIR` into `tools/Holmake/Systeml.sml`, and a prover built by another compiler, or for another directory, is refused. The ML compiler is part of what a rebuilt proof rests on, and a prover picked up from the machine is pinned by nothing.

Both trees are bound to their absolute paths: Poly/ML's prefix is compiled into it and the prover's configuration records where it lives, so a checkout that moves needs `.deps/tools` and `.deps/hol` built again. The refusal above is what says so, instead of a loader error hours into a rebuild.

`check_backend.sh` sets `HOLDIR` and `CAKEMLDIR` to the isolated pinned checkouts, removes the build outputs of any earlier run, verifies the tree, and invokes `Holmake` for `pan_to_targetProofTheory.uo` — the end of the chain the patch can break, and the 46 minutes above. `DN_BACKEND_TARGET=loop_liveProofTheory.uo` runs the narrow smoke target instead (three minutes on two jobs), and the script then says so. `DN_BUILD_JOBS` sets the job count for both the prover build and the proof, and the proof defaults to 2.

For the full target the script then asks the prover itself what the theorem rests on: `tagcheck/` is a one-theory build, outside both pinned trees, that opens the theory Holmake has just produced and fails unless `pan_to_target_compile_semantics` carries nothing but the disk tag — upstream's own criterion (`check_tag` in `misc/preamble.sml`). It is a check on oracles, and `cheat` is one of them: a theorem proved that way comes back tagged `DISK_THM, cheat` and the build fails, which was tried on a theorem proved with `cheat` rather than argued from the sources. Axioms it cannot see, because a theory file keeps a theorem's oracles but not its axiom nonces. The log-reading gate and this check answer different questions: what Holmake reported, and what the theorem says about itself.

`loop_liveProofTheory` alone does not re-establish the Pancake compiler theorem. The patch changes `shrink_def`, and the proofs that use it live further down the chain: `crep_to_loopProof` has `loop_liveProof` as an ancestor, `pan_to_wordProof` unfolds the clauses of `shrink_def`, and the compiler's correctness statement is `pan_to_targetProof`. Building only the narrow target leaves all of them unbuilt, so a break there would not show.

The build must not be given `--fast` (every tactic becomes an oracle) or `--noqof` (a failed proof stops being fatal), and the script refuses a run whose log reports a cheat, an oracle tag or a cache hit: Holmake records those instead of failing. The upstream proof itself ends with `check_thm pan_to_target_compile_semantics`, which rejects a theorem carrying anything but the standard tags.

What the lane fixes is the sources and the configuration of the tools built from them; what it does not fix is the C toolchain of the machine that compiles Poly/ML. Record any change to the recipe here before treating a rebuild as reproducible.

Rebuilding the chain establishes the compiler's correctness theorem for the patched source; it is not a compiler bootstrap, and no executable comes from it. The next section is where one does.

## Bootstrap the compiler

From the repository root, after `build hol` above:

```sh
bash scripts/bootstrap_cake.sh
```

The script verifies both pinned trees, refuses a prover not built by the pinned Poly/ML, removes the CakeML build outputs of any earlier run, and asks Holmake for `cake.S` in `compiler/bootstrap/compilation/x64/64`. That file is the compiler's own machine code, written by the proof of `compiler64_compiled`: the theorem that evaluating the compiler, the patched `shrink_def` among its definitions, on its own source gives that code. The Holmake log goes through the same gate as the proof lane, and a theory built outside both pinned trees (`bootstrap-tagcheck/`) asks the prover for that theorem's tag, as `tagcheck/` does for the proof lane. `scripts/backend.py package-bootstrap` then links `cake.S` with `basis_ffi.c` through the tree's Makefile, with the release compiler's `-z noexecstack` because the generated assembly carries no `.note.GNU-stack`, refuses a result whose stack segment is not `RW` (read from its program headers), and requires the compiler to compile a hello world that prints exactly `Hello!`. It copies `cake` and `cake.S` to `build/bootstrap/`, because the next run of either backend lane removes the tree's build outputs, and writes `report.json` beside them: the revisions, the patch and Poly/ML digests, Poly/ML's runtime options, the job count, the digests of the Holmake log, `cake.S`, `basis_ffi.c` and `cake`, the link flags, the C compiler, the stack permissions, the hello-world output, the platform and the time taken. After a run, `verify cakeml` refuses the tree until its build outputs are removed.

`bootstrap-record.json` is the report of the run the statements below come from. A gate test requires its revisions, patch and Poly/ML to be the ones pinned now, so none of them can move without a new run; its log digest identifies that run's Holmake log.

The script refuses a job count or heap size that is not a plain number, a `CLINE_OPTIONS` in the environment, and a platform other than Linux x86-64: the first two reach the prover's command line and the third reaches Holmake's, where anything else would be read as an option. `DN_BUILD_JOBS` sets the job count (default 2), `DN_POLY_MINHEAP` the heap floor below.

It runs outside CI. On one machine, with 16 hardware threads, 90 GB of memory and four jobs, it took 4 hours 43 minutes, the tag check included; the translation of the compiler is a serial chain of theories that more cores do not shorten, and it took about twice what upstream reports for the same step, for a reason not established. Watching from the host, the heaviest steps (`compiler64Prog` in every run, `cake.S` in one) grew one prover process to Poly/ML's default ceiling of 80 % of physical memory; the report does not measure memory. A hosted runner has 16 GB. How little memory suffices is not measured.

Poly/ML sizes its heap from GC timing. In the first run the limit it chose after a full collection equalled the space already in use, and an object larger than one heap segment then ended `repl_init_types` with "Run out of store" although the heap was 21 % full; this was reproduced under four jobs with Poly/ML's heap log, and the lines that decide it are unchanged in Poly/ML's `master` as of 2026-09-21. The script therefore gives every theory a heap floor, `--minheap 8G` through `POLY_CLINE_OPTIONS`, and Holmake, which runs on Poly/ML too and hit the same limit in a later run, a floor of 2G on its own command line. The floor protects a process while its heap is below it; above it the upstream heuristic applies. It costs memory: a process starts with up to half the floor as allocation space.

Run with `CAKE` set to `build/bootstrap/cake`, `scripts/native_check.py` and `scripts/native_baseline.py` pass with the same case counts as with the release compiler; the reports differ in `compiler_sha256` and in timing and socket-chunking counters, which also differ between two runs of the same compiler. The compiler reports its base revision (`cake --version`), not the patch, and the native lane picks the keyword table for that revision.

No output shows the patch. It drops an add-with-carry whose results are unused at the loop language, and word language's own dead-code pass (`remove_dead` in `word_allocScript.sml`) drops the same instruction later, so a test program with such a dead operation compiled to byte-identical code with the release and the bootstrapped compiler, as the native lanes' programs do. That the binary carries the patch rests on the verified source the prover computed it from.

What this establishes: an executable compiler whose machine code the prover computed from the pinned source with the curated patch, by a theorem that carries no oracle. What it does not establish is a theorem about the binary's behaviour. Upstream's end-to-end theorem for a bootstrapped compiler is a separate target (`compiler/bootstrap/compilation/x64/64/proofs`) that this script does not build; it says the binary computes the compiler function, whose `--pancake` branch reads Pancake text and calls the Pancake compiler, and no upstream theorem connects that branch to `pan_to_target_compile_semantics`. Beyond that, what a compiled program does rests on assumptions outside any proof: the compiler theorem allows a run to stop early when heap or stack is exhausted; the C implementation of the FFI is assumed to behave as the oracle it is modelled by, and foreign code not to touch the compiler's memory; the assembler, linker and loader, the assembly prelude `cake.S` carries around the generated code, and the C compiler that builds `basis_ffi.c` are not verified; the instruction-set model covers user-mode instructions only; and everything rests on the HOL4 kernel and the Poly/ML that runs it. The tree's Makefile builds the compiler with `-DEVAL`, which maps a region that is both writable and executable for in-memory evaluation, as upstream builds it.

`cake --version` prints the time the compiler's version theory was built, which is embedded in `cake.S`, so two builds differ in bytes and a recorded digest names one build, not a reproducible identity. The executable runs on Linux x86-64, and the native lanes here compile for that target only.

## Release compiler lane

`python3 scripts/bootstrap_tool.py cake` instead obtains the digest-pinned Linux x86-64 release in `tools.lock.json`, builds its supplied assembly artifact outside the repository and keeps only the resulting compiler. CI uses it for the native lanes, because the bootstrap above does not fit a hosted runner, and it stays as an independent reference. Its source revision differs from `lock.json`; native tests run with it do not establish that the curated optimization is deployed.
