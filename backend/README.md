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

Fetch refuses to overwrite an existing checkout. Verification compares the tracked source with the exact revision plus the curated patch and rejects unexpected non-ignored untracked files. Build outputs ignored by upstream Git rules are not certified by this check.

## Rebuild the proof

Install Poly/ML and the native build prerequisites described in the fetched HOL README. Configure and build the pinned HOL checkout:

```sh
cd .deps/hol
poly --script tools/smart-configure.sml
bin/build
cd ../..
bash scripts/check_backend.sh
```

The script sets `HOLDIR` and `CAKEMLDIR` to the isolated pinned checkouts and invokes `Holmake` for `loop_liveProofTheory.uo`. `DN_BUILD_JOBS` defaults to 2. Configuration may need platform-specific adjustment; record any change before treating this as a reproducible proof lane.

That target is an optimization proof rebuild, not a complete compiler bootstrap. A subsequent milestone is to build an executable compiler from this patched source, record the bootstrap chain, and run `scripts/native_check.py --cake /path/to/that/compiler` with the same emitted input.

## Release compiler lane

`python3 scripts/bootstrap_tool.py cake` instead obtains the digest-pinned Linux x86-64 release in `tools.lock.json` and builds its supplied assembly artifact. CI uses it to execute the native example today. Its source revision differs from `lock.json`; successful native tests do not establish that the curated optimization is deployed.
