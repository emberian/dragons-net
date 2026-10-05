# SPDX-License-Identifier: AGPL-3.0-or-later
"""The fault lanes' own tools: what the LazyFS lane takes of LazyFS is refused of a file system
that keeps what was not synced or writes an append whole, its configuration is what it says, and
the fiu lane runs its probe with libfiu's preload and nothing left over from the caller."""
from __future__ import annotations

import os
from pathlib import Path
import signal
import tempfile
import tomllib
import unittest
from unittest import mock

from gatekit import script

L = script("lazyfs_check")
F = script("fiu_check")


class Durable:
    """A plain directory standing for LazyFS: nothing is lost and no append is torn."""

    def __init__(self, work: Path) -> None:
        self.point = self.root = work

    def command(self, line: str) -> None:
        pass

    def clear_cache(self) -> None:
        pass

    def ended(self) -> int:
        return -signal.SIGKILL

    def start(self) -> None:
        pass

    def stop(self) -> None:
        pass


class LazyFSLane(unittest.TestCase):
    def test_a_file_system_keeping_unsynced_data_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as temp, self.assertRaisesRegex(L.LaneError, "cache is cleared"):
            L.syncs(Durable(Path(temp)))

    def test_an_append_written_whole_is_refused(self) -> None:
        for persist in L.TORN:
            with self.subTest(persist=persist), tempfile.TemporaryDirectory() as temp, \
                    self.assertRaisesRegex(L.LaneError, "LazyFS left"):
                L.torn(Durable(Path(temp)), persist)

    def test_names_and_locks_hold_of_a_plain_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            self.assertEqual(L.names(Durable(Path(temp))), {"made": True, "moved-from": False, "moved": True,
                                                            "gone": False})
            self.assertEqual(L.locks(Durable(Path(temp))), ["refused while held", "taken once released"])

    def test_the_torn_appends_keep_the_parts_they_name(self) -> None:
        parts = [L.APPEND[k * L.SIZE:(k + 1) * L.SIZE] for k in range(3)]
        for persist, left in L.TORN.items():
            kept = {int(p) for p in persist.split(",")}
            end = max(kept) * L.SIZE
            wanted = b"".join(part if k + 1 in kept else bytes(L.SIZE) for k, part in enumerate(parts))[:end]
            with self.subTest(persist=persist):
                self.assertEqual(left, L.HEAD + wanted)

    def test_the_configuration_reads_as_lazyfs_reads_it(self) -> None:
        text = L.config(Path("/w/faults.fifo"), Path("/w/done.fifo"), Path("/w/lazyfs.log"))
        read = tomllib.loads(text)
        self.assertEqual(read["faults"], {"fifo_path": "/w/faults.fifo", "fifo_path_completed": "/w/done.fifo"})
        self.assertEqual(read["cache"]["apply_eviction"], False)
        self.assertEqual(read["filesystem"]["logfile"], "/w/lazyfs.log")

    def test_mounts_are_read_off_the_mount_table(self) -> None:
        self.assertTrue(L.mounted(Path("/")))
        self.assertFalse(L.mounted(Path("/no/such/mount")))


class FiuLane(unittest.TestCase):
    def test_the_probe_runs_with_the_preload_and_none_of_the_callers_points(self) -> None:
        with mock.patch.dict("os.environ", {"FIU_ENABLE": "enable name=dn/probe", "FIU_CTRL_FIFO": "/x"}):
            env = F.environment(Path("/fiu"), FIU_ENABLE="enable name=x")
        self.assertEqual(env["LD_PRELOAD"], "/fiu/fiu_run_preload.so")
        self.assertEqual(env["LD_LIBRARY_PATH"], "/fiu")
        self.assertEqual(env["FIU_ENABLE"], "enable name=x")
        self.assertNotIn("FIU_CTRL_FIFO", env)

    def test_a_remote_control_no_thread_serves_is_refused_in_time(self) -> None:
        with tempfile.TemporaryDirectory() as temp, mock.patch.object(F, "WAIT", 0.2):
            base = str(Path(temp) / "ctl")
            with self.assertRaisesRegex(F.LaneError, "did not open its input"):
                F.command(base, 1, "enable name=x")
            os.mkfifo(f"{base}-1.in")
            os.mkfifo(f"{base}-1.out")
            with self.assertRaisesRegex(F.LaneError, "did not open its input"):
                F.command(base, 1, "enable name=x")

    def test_a_probe_that_does_not_answer_is_refused_in_time(self) -> None:
        # tail writes nothing before its input ends.
        with mock.patch.object(F, "WAIT", 0.2), F.Probe(Path("/usr/bin/tail"), {}) as probe, \
                self.assertRaisesRegex(F.LaneError, "did not answer"):
            probe.ask()
        self.assertIsNotNone(probe.process.returncode)

    def test_an_answer_other_than_wanted_is_refused(self) -> None:
        F.expect("same", ["1 5"], ["1 5"])
        with self.assertRaisesRegex(F.LaneError, "not"):
            F.expect("other", ["0 0"], ["1 5"])


if __name__ == "__main__":
    unittest.main()
