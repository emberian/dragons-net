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

Rebuilding the chain establishes the compiler's correctness theorem for the patched source; it is not a compiler bootstrap, and no executable was produced from it. A subsequent milestone is to build an executable compiler from this patched source, record the bootstrap chain, and run `scripts/native_check.py --cake /path/to/that/compiler` with the same emitted input.

## Release compiler lane

`python3 scripts/bootstrap_tool.py cake` instead obtains the digest-pinned Linux x86-64 release in `tools.lock.json`, builds its supplied assembly artifact outside the repository and keeps only the resulting compiler. CI uses it to execute the native example today. Its source revision differs from `lock.json`; successful native tests do not establish that the curated optimization is deployed.
