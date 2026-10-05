#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The host lane: the host's side of the store (native/store.c), run with a stand-in for the
program (native/host_driver.c) that prints what the host hands it:

- without a spool there is no store: no identity, no group, no random octets, and no client may
  post;
- with one, the program gets the wall clock, 24 random octets drawn anew for each run, the path
  identity and the groups; a client may post from loopback by default, and else from the networks
  `--post-from` names, to the bit, over IPv4 and IPv6;
- a second host on a held spool, and a mark of a failed sync of this boot in the spool or the run
  directory, refuse the start with status 4; a mark of another boot is removed;
- options that cannot be refuse the start with status 2;
- each defect planted in store.c is caught.
"""
from __future__ import annotations

from collections.abc import Callable
import json
from pathlib import Path
import queue
import socket
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/host"
DRIVER = lanes.NATIVE / "host_driver.c"
HOST = lanes.NATIVE / "nntp_host.c"
STORE = lanes.NATIVE / "store.c"
RUNTIME = [lanes.NATIVE / "cake_header.c", lanes.NATIVE / "cake_runtime.c"]
WAIT = 10
IDENTITY = "news.example.org"
GROUPS = ["local.test", "comp.lang.lean"]
MARK = "sync-failed"
OTHER_BOOT = "00000000-0000-0000-0000-000000000000"
NAMED = ["--revision", "0123abc", "--source", "https://example.org/dn"]


def build(binary: Path, store: Path) -> Path:
    return lanes.link(binary, [DRIVER, HOST, store, *RUNTIME], includes=[OUT], check=store == STORE)


def start(binary: Path, options: list[str], address: str) -> tuple[subprocess.Popen[str], lanes.Lines, int]:
    """The host, listening; its standard output, and its port."""
    proc = subprocess.Popen([str(binary), *NAMED, "--address", address, *options], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    lines = lanes.Lines(proc.stdout)
    try:
        first = lines.get(WAIT)
    except queue.Empty:
        proc.kill()
        raise LaneError(f"the host said nothing in {WAIT} s with {options}") from None
    if not first:
        proc.kill()
        said = proc.communicate(timeout=WAIT)[1].strip()
        raise LaneError(f"the host did not start with {options}: status {proc.returncode}, saying {said!r}")
    return proc, lines, int(json.loads(first)["port"])


def stopped(proc: subprocess.Popen[str], lines: lanes.Lines) -> list[str]:
    """Stop the run; what the driver printed before, once the host ended as a stopped run does."""
    if proc.stdin is None:
        raise LaneError("the host has no input")
    proc.stdin.write("stop 7\n")
    proc.stdin.close()
    out = []
    while (line := lines.get(WAIT)) is not None:
        out.append(line.strip())
    status = proc.wait(timeout=WAIT)
    if status != 3:
        raise LaneError(f"the stopped run ended with status {status}")
    return out


def serve(binary: Path, options: list[str], address: str = "127.0.0.1") -> tuple[list[str], list[str]]:
    """One batch with a client connected: the start data and the connections opened, as words."""
    proc, lines, port = start(binary, options, address)
    try:
        with socket.create_connection((address, port), timeout=WAIT):
            if proc.stdin is None:
                raise LaneError("the host has no input")
            proc.stdin.write("next\nemit\n")
            proc.stdin.flush()
            out = stopped(proc, lines)
    finally:
        if proc.poll() is None:
            proc.kill()
            proc.wait()
    begin = [line.split() for line in out if line.startswith("start ")]
    opened = [line.split() for line in out if line.startswith("opened ")]
    if len(begin) != 1 or len(opened) != 1:
        raise LaneError(f"one batch with one connection printed {out}")
    return begin[0], opened[0]


def refused(binary: Path, options: list[str], status: int, said: str) -> None:
    done = subprocess.run([str(binary), *NAMED, *options], stdin=subprocess.DEVNULL, capture_output=True, text=True,
                          timeout=WAIT, check=False)
    if done.returncode != status or said not in done.stderr or done.stdout:
        raise LaneError(f"{options}: status {done.returncode}, saying {done.stderr.strip()!r}, not status {status} "
                        f"saying {said!r}")


class Store:
    """A spool and a run directory of their own."""

    def __init__(self, temp: str) -> None:
        self.spool, self.run = Path(temp) / "spool", Path(temp) / "run"
        self.spool.mkdir()
        self.run.mkdir()

    def options(self, *more: str) -> list[str]:
        named = ["--spool", str(self.spool), "--run-dir", str(self.run), "--path-identity", IDENTITY]
        return [*named, *(o for g in GROUPS for o in ("--group", g)), *more]


def boot_id() -> str:
    return Path("/proc/sys/kernel/random/boot_id").read_text().strip()


def no_store(binary: Path) -> dict[str, object]:
    begin, opened = serve(binary, [])
    if begin[2:] != ["0" * 48, "-"] or opened[3] != "0":
        raise LaneError(f"without a spool the program got {begin[2:]}, a client posting {opened[3]}")
    return {"start": begin[2:], "post": opened[3]}


def handed(binary: Path) -> dict[str, object]:
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        first, opened = serve(binary, store.options())
        second, _ = serve(binary, store.options())
    wall = int(first[1])
    if abs(wall - time.time() * 1000) > 60_000:
        raise LaneError(f"a wall clock of {wall} ms")
    wanted = [IDENTITY.encode().hex(), *(g.encode().hex() for g in GROUPS)]
    if first[3:] != wanted or second[3:] != wanted:
        raise LaneError(f"the program got {first[3:]}, not the identity and the groups {wanted}")
    if len(first[2]) != 48 or first[2] == "0" * 48 or first[2] == second[2]:
        raise LaneError(f"random octets {first[2]} and then {second[2]}")
    if opened[3] != "1":
        raise LaneError("a client on loopback may not post by default")
    return {"wall": wall, "random": [first[2], second[2]], "post": opened[3]}


def posting(binary: Path) -> dict[str, str]:
    """Who may post: the networks named, to the bit; loopback is no longer one once any is named."""
    cases = {"10.0.0.0/8": "0", "127.0.0.1/32": "1", "127.0.0.0/31": "1", "127.0.0.2/31": "0",
             "::1/128": "0"}
    seen = {}
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        for net in cases:
            seen[net] = serve(binary, store.options("--post-from", net))[1][3]
        seen["::1, by default"] = serve(binary, store.options(), "::1")[1][3]
        seen["::/127 from ::1"] = serve(binary, store.options("--post-from", "::/127"), "::1")[1][3]
    wanted_all = {**cases, "::1, by default": "1", "::/127 from ::1": "1"}
    if seen != wanted_all:
        raise LaneError(f"who may post: {seen}, not {wanted_all}")
    return seen


def held(binary: Path) -> str:
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        proc, lines, _ = start(binary, store.options(), "127.0.0.1")
        try:
            refused(binary, store.options(), 4, "another process holds the spool")
            stopped(proc, lines)
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()
    return "refused"


def marks(binary: Path) -> dict[str, str]:
    seen = {}
    for where in ("spool", "run"):
        with tempfile.TemporaryDirectory() as temp:
            store = Store(temp)
            mark = getattr(store, where) / MARK
            for text, said in ((boot_id()[:10], "cannot be read whole"), ("", "cannot be read whole"),
                               (boot_id() + "\n", "a sync failed since the machine started")):
                mark.write_text(text)
                refused(binary, store.options(), 4, said)
                if not mark.exists():
                    raise LaneError(f"a refused start removed the mark in the {where} directory")
            mark.write_text(OTHER_BOOT + "\n")
            serve(binary, store.options())
            if mark.exists():
                raise LaneError(f"a mark of another boot is left in the {where} directory")
            seen[where] = "this boot and a cut one refused, another removed"
    return seen


def options(binary: Path) -> dict[str, str]:
    """Options that cannot be."""
    with tempfile.TemporaryDirectory() as temp:
        store = Store(temp)
        spool, run = ["--spool", str(store.spool)], ["--run-dir", str(store.run)]
        cases = {"a group without a spool": (["--group", "a.b"], "store options without --spool"),
                 "a spool without a run directory": (spool, "--spool needs --run-dir"),
                 "a spool that is not there": (["--spool", str(store.spool / "x"), *run], "No such file"),
                 "an identity too long": ([*spool, *run, "--path-identity", "a" * 201], "--path-identity"),
                 "a group too long": ([*spool, *run, "--group", "a" * 65], "--group"),
                 "an empty group": ([*spool, *run, "--group", ""], "--group"),
                 "65 groups": ([*spool, *run, *(o for k in range(65) for o in ("--group", f"g{k}"))], "--group"),
                 "a network that is none": ([*spool, *run, "--post-from", "10.0.0.0/33"], "not a number"),
                 "an address that is none": ([*spool, *run, "--post-from", "x/8"], "not a network")}
        for options_, said in cases.values():
            refused(binary, options_, 2, said)
    return dict.fromkeys(cases, "refused")


CHECKS: dict[str, Callable[[Path], object]] = {
    "no store": no_store, "handed": handed, "posting": posting, "held": held, "marks": marks, "options": options}

# Defects planted in store.c: (name, the text, what it becomes).
DEFECTS = [
    ("the lock not taken", "if (flock(spool, LOCK_EX | LOCK_NB)) {", "if (0) {"),
    ("a mark of this boot let through", "if (!memcmp(seen, boot, BOOT_ID))", "if (0 && !memcmp(seen, boot, BOOT_ID))"),
    ("a mark cut short taken for another boot's", "if (n != BOOT_ID)\n        refuse(", "if (n < 0)\n        refuse("),
    ("a mark of another boot kept", "if (unlinkat(dir, MARK, 0) && errno != ENOENT)", "if (0)"),
    ("the run directory's mark unread", "    check_mark(run, run_path, boot);\n", ""),
    ("the last bits of a prefix ignored", "if (rest && ", "if (0 && "),
    ("no network by default", '        add_net("127.0.0.0/8");\n        add_net("::1/128");\n', ""),
    ("no random octets", "ssize_t n = getrandom(random_octets + got, sizeof random_octets - got, 0);",
     "ssize_t n = (ssize_t)(sizeof random_octets - got);"),
    ("no groups handed", "dn_put_word(next + DN_SESSION_NEXT_GROUP_COUNT, group_count);",
     "dn_put_word(next + DN_SESSION_NEXT_GROUP_COUNT, 0);"),
]


def check() -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    binary = build(OUT / "host", STORE)
    results = {name: run(binary) for name, run in CHECKS.items()}
    caught = {}
    source = STORE.read_text()
    for index, (name, text, becomes) in enumerate(DEFECTS):
        planted = OUT / f"defect-{index}.c"
        planted.write_text(lanes.plant(source, text, becomes, 1, "store.c, for a planted defect,", exact=True))
        broken = build(OUT / f"defect-{index}", planted)
        for check_name, run in CHECKS.items():
            try:
                run(broken)
            except LaneError as error:
                caught[name] = f"{check_name}: {str(error)[:200]}"
                break
        else:
            raise LaneError(f"the defect {name!r} was not caught")
    return Report("checked", None, [HOST, STORE, lanes.NATIVE / "store.h", DRIVER],
                  {"checks": results, "defects_caught": caught})


def main() -> None:
    lanes.lane_main("HOST", OUT, check)


if __name__ == "__main__":
    main()
