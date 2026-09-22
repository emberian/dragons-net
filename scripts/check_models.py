#!/usr/bin/env python3
"""Run the concurrency models, refusing a set that has quietly shrunk.

The models are only evidence while they all run. A crate dropped from the
workspace, a `cfg` that stops matching, or a deleted test would otherwise leave
the lane green with less explored, so the discovered tests are compared against
a recorded list instead of a lower bound. Update `models/expected-tests.txt`
when tests are added or renamed, in the same commit.

Loom's preemption bound is left to each test: `loom::model` explores every
interleaving, and the models that would not converge that way set their own
bound explicitly. Setting a bound here would silently weaken the tests that
claim to be exhaustive.
"""

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "models" / "Cargo.toml"
RUNTIME = ROOT / "Cargo.toml"
EXPECTED = ROOT / "models" / "expected-tests.txt"


def members() -> list[tuple[Path, str]]:
    """Every package whose concurrency tests this gate covers."""
    with MANIFEST.open("rb") as handle:
        workspace = tomllib.load(handle)["workspace"]["members"]
    found = []
    for member in workspace:
        with (ROOT / "models" / member / "Cargo.toml").open("rb") as handle:
            found.append((MANIFEST, tomllib.load(handle)["package"]["name"]))
    # The runtime crate itself: its loom tests drive the shipped code, so a
    # `cfg` that stops matching there has to fail this gate too.
    found.append((RUNTIME, "dn-runtime"))
    return sorted(found, key=lambda entry: (str(entry[0]), entry[1]))


def discovered(mode: str, env: dict[str, str]) -> set[str]:
    found = set()
    for manifest, package in members():
        if manifest == RUNTIME and mode != "loom":
            # Its ordinary tests run with the rest of the root workspace.
            continue
        cmd = ["cargo", "test", "--locked", "--release", "--manifest-path", str(manifest),
               "-p", package]
        if manifest == RUNTIME:
            cmd += ["--test", "loom"]
        listing = subprocess.run([*cmd, "--", "--list"], cwd=ROOT, env=env, text=True,
                                 capture_output=True, check=False, timeout=300)
        if listing.returncode != 0:
            print(listing.stdout[-2000:] + listing.stderr[-2000:], file=sys.stderr)
            raise SystemExit(f"models: {package} does not build, so its tests cannot be counted")
        for name in re.findall(r"^(.+): test$", listing.stdout, re.MULTILINE):
            found.add(f"{mode} {package}::{name}")
    return found


def expected(mode: str) -> set[str]:
    lines = EXPECTED.read_text().splitlines()
    return {line for line in lines if line.startswith(f"{mode} ")}


def check(mode: str, env: dict[str, str]) -> None:
    found, want = discovered(mode, env), expected(mode)
    missing, extra = sorted(want - found), sorted(found - want)
    if missing or extra:
        for name in missing:
            print(f"models: expected test not discovered: {name}", file=sys.stderr)
        for name in extra:
            print(f"models: undeclared test discovered: {name}", file=sys.stderr)
        raise SystemExit(f"models: {EXPECTED.relative_to(ROOT)} does not match the {mode} lane")
    print(f"models: {len(found)} {mode} tests, exactly the recorded set", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--loom", action="store_true")
    parser.add_argument("--record", action="store_true",
                        help="rewrite models/expected-tests.txt from what is discovered")
    args = parser.parse_args()
    env = os.environ.copy()
    mode = "plain"
    if args.loom:
        mode = "loom"
        env["RUSTFLAGS"] = (env.get("RUSTFLAGS", "") + " --cfg loom").strip()
        env.pop("LOOM_MAX_PREEMPTIONS", None)
    if args.record:
        keep = {line for line in EXPECTED.read_text().splitlines()
                if line and not line.startswith(f"{mode} ")}
        EXPECTED.write_text("\n".join(sorted(keep | discovered(mode, env))) + "\n")
        print(f"models: recorded the {mode} lane in {EXPECTED.relative_to(ROOT)}")
        raise SystemExit(0)
    check(mode, env)
    cmd = ["cargo", "test", "--locked", "--release", "--manifest-path", str(MANIFEST),
           "--workspace"]
    subprocess.run([*cmd, "--", "--test-threads=1"], cwd=ROOT, env=env, check=True, timeout=1800)
    if args.loom:
        runtime = ["cargo", "test", "--locked", "--release", "--manifest-path", str(RUNTIME),
                   "-p", "dn-runtime", "--test", "loom"]
        subprocess.run([*runtime, "--", "--test-threads=1"], cwd=ROOT, env=env, check=True,
                       timeout=1800)
