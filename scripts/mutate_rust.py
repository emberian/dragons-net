#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Check that the concurrency tests can fail.

A green loom lane is only evidence if the tests would go red on a broken
implementation. Each mutation below is a defect the tests are supposed to catch:
the script applies it to a copy of the tree, runs the named tests, and requires
them to fail. A mutation that no longer fails anything means the test lost its
teeth, or the code moved and the mutation stopped applying — both are failures
of this script.

The mutations are deliberately the shape of real mistakes (a publication that is
not ordered against the close, a coalescing condition dropped, a take that is
not atomic, a bound checked after the increment), not line deletions.
"""

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Mutation:
    """One defect, the tests that must catch it, and where they live."""

    name: str
    file: str
    before: str
    after: str
    manifest: str
    package: str
    tests: tuple[str, ...]
    loom: bool = True
    target: str | None = None


MUTATIONS: tuple[Mutation, ...] = (
    Mutation(
        name="ring-publish-without-close-check",
        file="models/ring/src/lib.rs",
        before="""        match self.ring.tail.compare_exchange(
            tail,
            tail.wrapping_add(STEP),
            Ordering::Release,
            Ordering::Acquire,
        ) {
            Ok(_) => {""",
        after="""        match Ok::<usize, usize>({
            self.ring
                .tail
                .fetch_add(STEP, Ordering::Release);
            tail
        }) {
            Ok(_) => {""",
        manifest="models/Cargo.toml",
        package="dn-ring-model",
        tests=(
            "no_push_succeeds_after_recv_reported_drained",
            "accepted_async_sends_are_all_received",
        ),
        target="loom",
    ),
    Mutation(
        name="wake-no-coalescing",
        file="models/wake/src/lib.rs",
        before="        if was_pending {",
        after="        if was_pending && false {",
        manifest="models/Cargo.toml",
        package="dn-wake-model",
        tests=("no_missed_wakeup_single_producer", "no_missed_wakeup_two_producers"),
        target="loom",
    ),
    Mutation(
        name="lease-take-not-atomic",
        file="models/borrow-recycle/src/lib.rs",
        before="""        match self.0.swap(0, Ordering::AcqRel) {
            0 => None,
            bid => Some(bid),
        }""",
        after="""        let bid = self.0.load(Ordering::Acquire);
        self.0.store(0, Ordering::Release);
        if bid == 0 { None } else { Some(bid) }""",
        manifest="models/Cargo.toml",
        package="dn-borrow-recycle-model",
        tests=("borrow_recycle_is_interleaving_safe",),
        target="loom",
    ),
    Mutation(
        name="limit-off-by-one",
        file="crates/dn-runtime/src/limit.rs",
        before="(used < self.maximum).then(|| used + 1)",
        after="(used <= self.maximum).then(|| used + 1)",
        manifest="Cargo.toml",
        package="dn-runtime",
        tests=("limit_of_one_is_never_exceeded",),
        target="loom",
    ),
    Mutation(
        name="limit-relaxed-ordering",
        file="crates/dn-runtime/src/limit.rs",
        before="            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |used| {",
        after="            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |used| {",
        manifest="Cargo.toml",
        package="dn-runtime",
        tests=("a_released_slot_carries_the_previous_holders_writes",),
        target="loom",
    ),
    Mutation(
        name="ring-drop-wrong-slot",
        file="models/ring/src/lib.rs",
        before="            let slot = (i >> 1) & self.mask;",
        after="            let slot = i & self.mask;",
        manifest="models/Cargo.toml",
        package="dn-ring-model",
        tests=("undrained_items_are_destroyed_exactly_once", "destruction_survives_slot_reuse"),
        loom=False,
        target="stress",
    ),
)


def apply(tree: Path, mutation: Mutation) -> None:
    path = tree / mutation.file
    source = path.read_text()
    if source.count(mutation.before) != 1:
        raise SystemExit(
            f"mutation {mutation.name}: its target no longer appears exactly once in "
            f"{mutation.file}; the code moved and the mutation stopped testing anything"
        )
    path.write_text(source.replace(mutation.before, mutation.after))


def run_tests(tree: Path, mutation: Mutation, test: str) -> subprocess.CompletedProcess[str]:
    cmd = [
        "cargo", "test", "--locked", "--release",
        "--manifest-path", str(tree / mutation.manifest),
        "-p", mutation.package,
    ]
    if mutation.target is not None:
        cmd += ["--test", mutation.target]
    flags = os.environ.get("RUSTFLAGS", "")
    env = {"RUSTFLAGS": f"{flags} --cfg loom".strip() if mutation.loom else flags}
    return subprocess.run(
        [*cmd, "--", "--exact", test, "--test-threads=1"],
        cwd=tree, text=True, capture_output=True, timeout=1800,
        env={**os.environ, **env}, check=False,
    )


def verdict(result: subprocess.CompletedProcess[str]) -> str:
    """`killed` only when the test ran and failed.

    A build error, a missing toolchain or a test that was never discovered all
    exit nonzero too, and counting those as kills would make this script report
    success without checking anything.
    """
    output = result.stdout + result.stderr
    if "test result: FAILED" in result.stdout or "process didn't exit successfully" in output:
        # The second case is a test binary that aborted — a double free, say,
        # which never reaches the harness summary.
        return "killed"
    if result.returncode == 0 and re.search(r"test result: ok\. 1 passed", result.stdout):
        return "survived"
    return "inconclusive"


def copy_tree(destination: Path) -> Path:
    tree = destination / "tree"
    ignore = shutil.ignore_patterns("target", ".git", ".lake", ".deps", "build")
    for name in ("models", "crates", "Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        source = ROOT / name
        if source.is_dir():
            shutil.copytree(source, tree / name, ignore=ignore)
        else:
            (tree / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(source, tree / name)
    return tree


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", help="run a single mutation by name")
    args = parser.parse_args()
    selected = [m for m in MUTATIONS if args.only in (None, m.name)]
    if not selected:
        raise SystemExit(f"no mutation named {args.only}")

    failures = []
    for mutation in selected:
        with tempfile.TemporaryDirectory() as temp:
            tree = copy_tree(Path(temp))
            # Control run: the unmutated copy must pass, or the mutation proves
            # nothing about the test and everything about the copy.
            for test in mutation.tests:
                control = run_tests(tree, mutation, test)
                if verdict(control) != "survived":
                    failures.append(f"{mutation.name} -> {test}: control run did not pass")
                    print(f"BROKEN   {mutation.name}: {test} does not pass unmutated", flush=True)
                    print(control.stdout[-2000:] + control.stderr[-2000:], file=sys.stderr)
            apply(tree, mutation)
            for test in mutation.tests:
                result = run_tests(tree, mutation, test)
                state = verdict(result)
                if state == "killed":
                    print(f"killed   {mutation.name}: {test} fails as it must", flush=True)
                    continue
                failures.append(f"{mutation.name} -> {test}: {state}")
                print(f"{state.upper():<8} {mutation.name}: {test}", flush=True)
                if state == "inconclusive":
                    print(result.stdout[-2000:] + result.stderr[-2000:], file=sys.stderr)
    if failures:
        print("mutation checks that proved nothing:", ", ".join(failures), file=sys.stderr)
        return 1
    print(f"all {sum(len(m.tests) for m in selected)} mutation checks killed", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
