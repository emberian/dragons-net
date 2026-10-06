#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The fiu lane: the points of failure the host's test build is to carry (decision 0005), held to
what its tests will take of libfiu, on a program with one point (native/fault_probe.c):

- built with FIU_ENABLE and libfiu, the program does not fail at a point no one enabled;
- a point enabled as the program starts, through `FIU_ENABLE` and libfiu's preload, fails with the
  information it was given: once when it was enabled once, every time otherwise;
- a point enabled and then disabled while the program runs, through the named pipes of libfiu's
  remote control, fails from then on and stops;
- built without FIU_ENABLE, the same program never fails at the point, whatever is enabled, needs
  no libfiu and carries no symbol of it.
"""
from __future__ import annotations

import errno
import os
from pathlib import Path
import selectors
import subprocess
import sys
import tempfile
import time
from typing import IO, Self

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/fiu"
PROBE = lanes.NATIVE / "fault_probe.c"
POINT = "dn/probe"
# How long the lane waits for the probe or libfiu's remote control at any one step.
WAIT = 10


class Probe:
    """The probe running: a line asks the point once and reads what it answered. Leaving the
    `with` block ends it, whatever happened."""

    def __init__(self, binary: Path, env: dict[str, str]) -> None:
        self.process: subprocess.Popen[str] = subprocess.Popen(
            [str(binary)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, env=env)
        if self.process.stdin is None or self.process.stdout is None:
            raise LaneError("the probe has no pipes")
        self.stdin: IO[str] = self.process.stdin
        self.stdout: IO[str] = self.process.stdout

    def __enter__(self) -> Self:
        return self

    def __exit__(self, *_: object) -> None:
        if self.process.poll() is None:
            self.process.kill()
        self.process.wait()

    def ask(self) -> str:
        self.stdin.write("?\n")
        self.stdin.flush()
        with selectors.DefaultSelector() as ready:
            ready.register(self.stdout, selectors.EVENT_READ)
            if not ready.select(timeout=WAIT):
                raise LaneError("the probe did not answer")
        return self.stdout.readline().strip()

    def close(self) -> None:
        self.stdin.close()
        try:
            status = self.process.wait(timeout=WAIT)
        except subprocess.TimeoutExpired:
            raise LaneError("the probe did not end with its input") from None
        if status:
            raise LaneError(f"the probe ended with status {status}")


def build(fiu: Path, binary: Path, *, enabled: bool) -> Path:
    """The probe with the hardening flags, with its point of failure or without it."""
    with_fiu = ["-DFIU_ENABLE=1", f"-L{fiu}", "-lfiu", f"-Wl,-rpath,{fiu}"] if enabled else []
    lanes.loud([lanes.cc(), *lanes.HARDENING, f"-I{fiu}", str(PROBE), "-o", str(binary), *with_fiu],
               timeout=120, what=f"building {binary.name}")
    lanes.hardened(binary)
    return binary


def environment(fiu: Path, **extra: str) -> dict[str, str]:
    """libfiu's preload, which enables points as the program starts and serves remote control."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("FIU_")}
    return {**env, "LD_PRELOAD": str(fiu / "fiu_run_preload.so"), "LD_LIBRARY_PATH": str(fiu), **extra}


def answers(binary: Path, env: dict[str, str], times: int) -> list[str]:
    with Probe(binary, env) as probe:
        said = [probe.ask() for _ in range(times)]
        probe.close()
    return said


def input_end(path: str, deadline: float) -> int:
    """The writing end of libfiu's input pipe, opened without blocking: the pipe is missing until the
    thread makes it, and has no reader until the thread opens it."""
    while True:
        try:
            return os.open(path, os.O_WRONLY | os.O_NONBLOCK)
        except OSError as error:
            if error.errno not in (errno.ENOENT, errno.ENXIO):
                raise
        if time.monotonic() > deadline:
            raise LaneError("libfiu's remote control did not open its input")
        time.sleep(0.01)


def command(base: str, pid: int, line: str) -> str:
    """One remote control command, as `fiu-ctrl` sends it: a line to the input pipe and the status
    read back from the output pipe. libfiu's thread opens its input, then its output, and answers
    one line; each end is opened here in that order too, without blocking, so that no step waits
    past the deadline for an end the thread has not opened."""
    pipe_in, pipe_out = f"{base}-{pid}.in", f"{base}-{pid}.out"
    deadline = time.monotonic() + WAIT
    sending = input_end(pipe_in, deadline)
    try:
        os.write(sending, (line + "\n").encode())
    finally:
        os.close(sending)
    receiving = os.open(pipe_out, os.O_RDONLY | os.O_NONBLOCK)
    said = b""
    try:
        while not said.endswith(b"\n"):
            if time.monotonic() > deadline:
                raise LaneError(f"libfiu's remote control did not answer {line!r}")
            try:
                said += os.read(receiving, 64)
            except BlockingIOError:
                pass
            time.sleep(0.01)
    finally:
        os.close(receiving)
    return said.decode().strip()


def expect(name: str, said: list[str], wanted: list[str]) -> None:
    if said != wanted:
        raise LaneError(f"{name}: the point answered {said}, not {wanted}")


def check() -> Report:
    fiu = lanes.pinned_tool("libfiu")
    OUT.mkdir(parents=True, exist_ok=True)
    with_point = build(fiu, OUT / "probe-fiu", enabled=True)
    without = build(fiu, OUT / "probe", enabled=False)
    needed = lanes.loud(["readelf", "-d", str(with_point)], timeout=60, what="reading the probe")
    if "libfiu.so" not in needed:
        raise LaneError("the probe built with FIU_ENABLE does not load libfiu")
    seen: dict[str, list[str]] = {}
    seen["not enabled"] = answers(with_point, environment(fiu), 3)
    expect("not enabled", seen["not enabled"], ["0 0"] * 3)
    seen["enabled once at start"] = answers(
        with_point, environment(fiu, FIU_ENABLE=f"enable name={POINT},failinfo=5,onetime"), 3)
    expect("enabled once at start", seen["enabled once at start"], ["1 5", "0 0", "0 0"])
    always = environment(fiu, FIU_ENABLE=f"enable name={POINT},failinfo=28")
    seen["enabled at start"] = answers(with_point, always, 3)
    expect("enabled at start", seen["enabled at start"], ["1 28"] * 3)
    with tempfile.TemporaryDirectory(prefix="dn-fiu-") as temp:
        base = str(Path(temp) / "ctl")
        with Probe(with_point, environment(fiu, FIU_CTRL_FIFO=base)) as probe:
            said = [probe.ask()]
            status = [command(base, probe.process.pid, f"enable name={POINT},failinfo=13")]
            said += [probe.ask(), probe.ask()]
            status.append(command(base, probe.process.pid, f"disable name={POINT}"))
            said.append(probe.ask())
            probe.close()
    if status != ["0", "0"]:
        raise LaneError(f"libfiu's remote control answered {status}, not success")
    seen["enabled and disabled on command"] = said
    expect("enabled and disabled on command", said, ["0 0", "1 13", "1 13", "0 0"])
    seen["compiled out"] = answers(without, always, 3)
    expect("compiled out", seen["compiled out"], ["0 0"] * 3)
    plain = lanes.loud(["readelf", "-d", "--dyn-syms", str(without)], timeout=60, what="reading the probe")
    if "libfiu" in plain or "fiu_" in plain:
        raise LaneError("the probe built without FIU_ENABLE still refers to libfiu")
    return Report("checked", None, [PROBE], {"point": POINT, "answers": seen}, printed_by_dn_compiler=False)


def main() -> None:
    lanes.lane_main("FIU", OUT, check)


if __name__ == "__main__":
    main()
