# Curated backend work

This directory preserves the useful committed portion of the datacake experiment: primitive dead-code elimination with preservation work, plus counterexamples showing why shared-memory operations cannot be eliminated by the same reasoning. Unfinished Div/Mod changes were excluded.

`lock.json` pins the CakeML and HOL source revisions and the patch digest. `LICENSE.CakeML` retains the upstream BSD license. The source fetch and patch verification have been exercised; **the pinned HOL proof rebuild below has not yet been validated in this repository**.

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

Install Poly/ML and the native build prerequisites described in the fetched HOL README. Configure and build the pinned HOL checkout:

```sh
cd .deps/hol
poly --script tools/smart-configure.sml
bin/build
cd ../..
bash scripts/check_backend.sh
```

The script sets `HOLDIR` and `CAKEMLDIR` to the isolated pinned checkouts, removes the build outputs of any earlier run, verifies the tree, and invokes `Holmake` for `pan_to_targetProofTheory.uo` — the end of the chain the patch can break. That takes hours; `DN_BACKEND_TARGET=loop_liveProofTheory.uo` runs the narrow smoke target instead, and the script then says so. `DN_BUILD_JOBS` defaults to 2.

`loop_liveProofTheory` alone does not re-establish the Pancake compiler theorem. The patch changes `shrink_def`, and the proofs that use it live further down the chain: `crep_to_loopProof` has `loop_liveProof` as an ancestor, `pan_to_wordProof` unfolds the clauses of `shrink_def`, and the compiler's correctness statement is `pan_to_targetProof`. Building only the narrow target leaves all of them unbuilt, so a break there would not show.

The build must not be given `--fast` (every tactic becomes an oracle) or `--noqof` (a failed proof stops being fatal), and the script refuses a run whose log reports a cheat, an oracle tag or a cache hit: Holmake records those instead of failing. The upstream proof itself ends with `check_thm pan_to_target_compile_semantics`, which rejects a theorem carrying anything but the standard tags.

Configuration may need platform-specific adjustment; record any change before treating this as a reproducible proof lane.

Rebuilding the chain establishes the compiler's correctness theorem for the patched source; it is not a compiler bootstrap, and no executable was produced from it. A subsequent milestone is to build an executable compiler from this patched source, record the bootstrap chain, and run `scripts/native_check.py --cake /path/to/that/compiler` with the same emitted input.

## Release compiler lane

`python3 scripts/bootstrap_tool.py cake` instead obtains the digest-pinned Linux x86-64 release in `tools.lock.json`, builds its supplied assembly artifact outside the repository and keeps only the resulting compiler. CI uses it to execute the native example today. Its source revision differs from `lock.json`; successful native tests do not establish that the curated optimization is deployed.
