#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The LazyFS lane: what the crash lanes are to take of LazyFS (decision 0005), seen on files it
serves. The lane mounts it itself, as a user in a user namespace of its own or through
fusermount3, and mounts it again after LazyFS ends itself:

- data synced by fsync or fdatasync is there once the cache of unsynced data is cleared; data
  written since the last sync is not, though it is there while the cache is not cleared;
- creating, renaming and removing a name take effect at once, the directory synced or not: a
  missing sync of the directory is the crash model's to catch, not LazyFS's;
- an append torn by `torn-op` into three parts leaves, once LazyFS has ended itself, the parts it
  was told to keep and zeros where the others were: the first part, a prefix; the last, the end;
  or both, the middle lost;
- an exclusive flock on a file it serves keeps a second one off until it is released.

It needs /dev/fuse and the right to mount it, which it says it lacks when it does.
"""
from __future__ import annotations

import fcntl
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import termios
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes it importable
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/lazyfs"
WAIT = 10
SIZE = 1000
# The parts of an append `torn-op` keeps, each with what the file holds after it: a fixed head,
# synced before, then the parts kept and zeros for the others.
HEAD = b"H" * 10
APPEND = b"a" * SIZE + b"b" * SIZE + b"c" * SIZE
TORN = {"1": HEAD + b"a" * SIZE,
        "3": HEAD + bytes(2 * SIZE) + b"c" * SIZE,
        "1,3": HEAD + b"a" * SIZE + bytes(SIZE) + b"c" * SIZE}


def config(fifo: Path, done: Path, log: Path) -> str:
    """LazyFS's configuration: commands read from `fifo`, a clear of the cache reported on `done`,
    a cache of 64 MiB that never evicts, so that only a command drops what was not synced."""
    return (f'[faults]\nfifo_path="{fifo}"\nfifo_path_completed="{done}"\n'
            '[cache]\napply_eviction=false\n[cache.simple]\ncustom_size="64mb"\nblocks_per_page=1\n'
            f'[filesystem]\nlog_all_operations=false\nlogfile="{log}"\n')


def mounted(point: Path) -> bool:
    """Whether a file system is mounted at `point`, read from this process's mount table."""
    with Path("/proc/self/mountinfo").open() as table:
        return any(line.split()[4] == str(point) for line in table)


# The arguments LazyFS keeps, its own program's name among them, besides `--config-path` and its value.
LAZYFS_ARGS = 10


class LazyFS:
    """LazyFS serving a directory of its own at a mount point, started and stopped by the lane."""

    def __init__(self, binary: Path, work: Path) -> None:
        self.binary, self.root, self.point = binary, work / "root", work / "mnt"
        self.fifo, self.done, self.output = work / "faults.fifo", work / "done.fifo", work / "lazyfs.out"
        self.config = work / "lazyfs.toml"
        self.root.mkdir(exist_ok=True)
        self.point.mkdir(exist_ok=True)
        self.config.write_text(config(self.fifo, self.done, work / "lazyfs.log"))
        self.process: subprocess.Popen[bytes] | None = None
        self.answers: int | None = None
        # How each run of LazyFS ended: killed by itself after a tear, or, unmounted, by an abort
        # of its own, its thread of commands left running.
        self.ends: list[int] = []

    def start(self) -> None:
        """Mount it, in the foreground so that its process is the lane's to watch, and hold the
        reading end of the pipe it answers on: it opens the other end before it reads a command,
        and would wait for a reader until a clear of the cache came. LazyFS takes a configuration
        path holding "-o" anywhere, in any case, for an option and falls back to its default
        silently, so the path is given relative to its working directory; and it keeps only its
        first ten other arguments, dropping the rest silently."""
        command = [str(self.binary), str(self.point), "--config-path", self.config.name, "-f",
                   "-o", "modules=subdir", "-o", f"subdir={self.root}"]
        if len(command) - 2 > LAZYFS_ARGS:
            raise LaneError(f"LazyFS would drop arguments of {command}")
        with self.output.open("ab") as out:
            self.process = subprocess.Popen(command, stdout=out, stderr=subprocess.STDOUT, cwd=self.config.parent)
        deadline = time.monotonic() + WAIT
        while not (mounted(self.point) and self.done.exists()):
            if self.process.poll() is not None or time.monotonic() > deadline:
                self.stop()
                said = self.output.read_text(errors="replace")[-600:]
                raise LaneError("LazyFS could not mount here: it needs /dev/fuse and the right to mount "
                                f"it, in a user namespace or through fusermount3\n{said}")
            time.sleep(0.05)
        self.answers = os.open(self.done, os.O_RDONLY | os.O_NONBLOCK)

    def stop(self) -> None:
        """Unmount, lazily when LazyFS has ended itself, and wait for its process to end, killing it
        if it does not."""
        if mounted(self.point):
            subprocess.run(["fusermount3", "-u", "-z", str(self.point)], capture_output=True, timeout=WAIT,
                           check=False)
        if self.process is not None:
            try:
                self.process.wait(timeout=WAIT)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=WAIT)
            self.ends.append(self.process.returncode)
            self.process = None
        if self.answers is not None:
            os.close(self.answers)
            self.answers = None
        if mounted(self.point):
            raise LaneError(f"{self.point} is still mounted")

    def ended(self) -> int | None:
        """How LazyFS ends by itself, still mounted, within the wait, if it does."""
        if self.process is None:
            return None
        try:
            return self.process.wait(timeout=WAIT)
        except subprocess.TimeoutExpired:
            return None

    def command(self, line: str) -> None:
        """Send one command and wait until LazyFS has read it: two read at once would be one."""
        fd = os.open(self.fifo, os.O_WRONLY)
        try:
            os.write(fd, (line + "\n").encode())
            deadline = time.monotonic() + WAIT
            while int.from_bytes(fcntl.ioctl(fd, termios.FIONREAD, bytes(4)), "little"):
                if time.monotonic() > deadline:
                    raise LaneError(f"LazyFS did not read {line!r}")
                time.sleep(0.01)
        finally:
            os.close(fd)

    def clear_cache(self) -> None:
        """Drop what was not synced, and wait until LazyFS says it has."""
        if self.answers is None:
            raise LaneError("LazyFS is not mounted")
        self.command("lazyfs::clear-cache")
        said, deadline = b"", time.monotonic() + WAIT
        while not said.endswith(b"\n"):
            if time.monotonic() > deadline:
                raise LaneError(f"LazyFS did not say it cleared its cache, only {said!r}")
            try:
                said += os.read(self.answers, 256)
            except BlockingIOError:
                pass
            time.sleep(0.01)
        if said.strip() != b"finished::clear-cache":
            raise LaneError(f"LazyFS answered {said!r} to clearing its cache")


def put(path: Path, data: bytes, sync: str | None) -> None:
    """Write `data` at the end of `path`, then sync it by `sync`, if it names a way."""
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
    try:
        os.write(fd, data)
        if sync == "fsync":
            os.fsync(fd)
        elif sync == "fdatasync":
            os.fdatasync(fd)
    finally:
        os.close(fd)


def contents(fs: LazyFS, names: list[str]) -> dict[str, bytes | None]:
    return {name: (fs.point / name).read_bytes() if (fs.point / name).exists() else None for name in names}


def expect(what: str, seen: object, wanted: object) -> None:
    if seen != wanted:
        raise LaneError(f"{what}: LazyFS left {seen!r}, not {wanted!r}")


def syncs(fs: LazyFS) -> dict[str, object]:
    """Synced data stays when the cache is cleared, data written since the last sync goes."""
    block = b"x" * SIZE
    put(fs.point / "fsync", block, "fsync")
    put(fs.point / "fdatasync", block, "fdatasync")
    put(fs.point / "unsynced", block, None)
    put(fs.point / "appended", block, "fsync")
    put(fs.point / "appended", block, None)
    names = ["fsync", "fdatasync", "unsynced", "appended"]
    before = contents(fs, names)
    expect("before the cache is cleared", before,
           {"fsync": block, "fdatasync": block, "unsynced": block, "appended": block * 2})
    fs.clear_cache()
    after = contents(fs, names)
    expect("after the cache is cleared", after,
           {"fsync": block, "fdatasync": block, "unsynced": b"", "appended": block})
    return {name: [len(before[name] or b""), len(after[name] or b"")] for name in names}


def names(fs: LazyFS) -> dict[str, object]:
    """Names take effect at once, without a sync of the directory."""
    put(fs.point / "made", b"m", "fsync")
    put(fs.point / "moved-from", b"r", "fsync")
    (fs.point / "moved-from").rename(fs.point / "moved")
    put(fs.point / "gone", b"g", "fsync")
    (fs.point / "gone").unlink()
    fs.clear_cache()
    left = contents(fs, ["made", "moved-from", "moved", "gone"])
    expect("names after the cache is cleared", left,
           {"made": b"m", "moved-from": None, "moved": b"r", "gone": None})
    return {name: data is not None for name, data in left.items()}


def torn(fs: LazyFS, persist: str) -> int:
    """An append torn into three parts, `persist` of them kept, read once LazyFS has ended itself
    and been mounted again; the length the file was left with."""
    put(fs.point / "torn", HEAD, "fsync")
    fs.command(f"lazyfs::torn-op::file={fs.root / 'torn'}::persist={persist}::parts=3::occurrence=1")
    # LazyFS takes its commands one at a time, in order, and says only when it has cleared its
    # cache: once it says so, the tear is set. Nothing is lost by it, the head being synced.
    fs.clear_cache()
    try:
        put(fs.point / "torn", APPEND, None)
    except OSError:
        pass  # LazyFS ends itself in the middle of the append
    # A tear ends with LazyFS killing itself; any other end is something else gone wrong.
    ended = fs.ended()
    if ended != -signal.SIGKILL:
        raise LaneError(f"LazyFS did not kill itself after an append torn, parts {persist} kept: it "
                        f"{'went on' if ended is None else f'ended with status {ended}'}")
    fs.stop()
    fs.start()
    left = (fs.point / "torn").read_bytes()
    expect(f"an append torn, parts {persist} kept", left, TORN[persist])
    (fs.point / "torn").unlink()
    return len(left)


def locks(fs: LazyFS) -> list[str]:
    """A second exclusive flock is refused while the first is held, and taken once it is not."""
    put(fs.point / "lock", b"", "fsync")
    first = os.open(fs.point / "lock", os.O_RDONLY)
    second = os.open(fs.point / "lock", os.O_RDONLY)
    seen = []
    try:
        fcntl.flock(first, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            fcntl.flock(second, fcntl.LOCK_EX | fcntl.LOCK_NB)
            seen.append("taken while held")
        except BlockingIOError:
            seen.append("refused while held")
        fcntl.flock(first, fcntl.LOCK_UN)
        try:
            fcntl.flock(second, fcntl.LOCK_EX | fcntl.LOCK_NB)
            seen.append("taken once released")
        except BlockingIOError:
            seen.append("refused once released")
    finally:
        os.close(first)
        os.close(second)
    expect("flock", seen, ["refused while held", "taken once released"])
    return seen


def check() -> Report:
    binary = lanes.pinned_tool("lazyfs")
    # "-o" in the name, which LazyFS would take for an option were its configuration's path given whole.
    with tempfile.TemporaryDirectory(prefix="dn-lazyfs-o-") as temp:
        fs = LazyFS(binary, Path(temp))
        fs.start()
        try:
            body = {"syncs": syncs(fs), "names": names(fs),
                    "torn": {persist: torn(fs, persist) for persist in TORN}, "flock": locks(fs)}
        finally:
            fs.stop()
        body["ends"] = fs.ends
    return Report("checked", None, [], body, printed_by_dn_compiler=False)


def main() -> None:
    lanes.lane_main("LAZYFS", OUT, check)


if __name__ == "__main__":
    main()
