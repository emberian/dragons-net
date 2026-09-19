#!/usr/bin/env python3
"""Run concurrency models, refusing a vacuous zero-test Loom invocation."""
import argparse
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--loom", action="store_true")
    args = parser.parse_args()
    env = os.environ.copy()
    cmd = ["cargo", "test", "--locked", "--manifest-path", "models/Cargo.toml", "--workspace"]
    if args.loom:
        env["RUSTFLAGS"] = (env.get("RUSTFLAGS", "") + " --cfg loom").strip()
        env.setdefault("LOOM_MAX_PREEMPTIONS", "2")
        listing = subprocess.run([*cmd, "--", "--list"], cwd=ROOT, env=env,
                                 text=True, capture_output=True, check=True, timeout=180)
        count = len(re.findall(r"^.+: test$", listing.stdout, re.MULTILINE))
        if count < 20:
            raise SystemExit(f"Loom discovery found only {count} tests; cfg/workspace coverage broken")
        print(f"Loom: {count} tests; default preemption bound {env['LOOM_MAX_PREEMPTIONS']} "
              "(individual ring/wake tests set 3)", flush=True)
    subprocess.run([*cmd, "--", "--test-threads=1"], cwd=ROOT, env=env, check=True, timeout=600)
