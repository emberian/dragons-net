# SPDX-License-Identifier: AGPL-3.0-or-later
"""The measurement's own reasoning (scripts/bench.py) on records made here. Kept rates, the sweep, the load's CPUs, a
reply's share, the table, NNTP replies, a server's time with its children's."""
from __future__ import annotations

import io
import os
import subprocess
import sys
import time
from typing import Any
import unittest

from gatekit import script

B = script("bench")


def run(**given: Any) -> dict[str, Any]:
    """A load's record: 1,000 a second kept, every count as given."""
    base: dict[str, Any] = {
        "rate": 1000, "achieved": 1000.0, "served": 10_000, "answered": 13_000, "owed": 0, "wrong": 0, "lost": 0,
        "seconds": 10, "warmup": 2, "threads": 4, "cpu_user_us": 1_000_000, "cpu_system_us": 1_000_000,
        "latency_ns": {"p50": 100_000, "p99": 1_000_000, "p999": 2_000_000, "max": 3_000_000},
        "send_late_ns": {"p99": 5_000},
        "server": {"cpu_ns": 1_000_000_000, "cpu_user_ms": 600, "cpu_system_ms": 400, "voluntary_switches": 20_000,
                   "involuntary_switches": 0, "allocations": 0, "high_water_kb": 4096}}
    for key, value in given.items():
        if key in base["server"]:
            base["server"][key] = value
        elif key == "p99":
            base["latency_ns"][key] = value
        else:
            base[key] = value
    return base


class Kept(unittest.TestCase):
    def test_a_rate_is_kept_only_whole(self) -> None:
        self.assertFalse(B.saturated(run()))
        for broken in ({"achieved": 960.0}, {"owed": 1}, {"wrong": 1}, {"lost": 1}, {"p99": 20_000_001}):
            with self.subTest(broken):
                self.assertTrue(B.saturated(run(**broken)))
        self.assertFalse(B.saturated(run(achieved=970.0, p99=20_000_000)))

    def test_the_sweep_finds_the_highest_rate_kept(self) -> None:
        for capacity, highest, tried in (
                (10_000, 10_000, [2000, 4000, 8000, 16_000, 10_000, 12_000]),
                (500, 500, [2000, 1000, 500, 625]),
                (100, 0, [2000, 1000, 500, 250]),
                (10**9, 2_048_000, [2000 * 2**k for k in range(11)])):
            with self.subTest(capacity):
                self.assertEqual(B.sweep(lambda rate, c=capacity: rate > c), (highest, tried))


class Machine(unittest.TestCase):
    def test_the_load_takes_cores_the_server_does_not_share(self) -> None:
        # Sixteen CPUs, eight cores of two threads: CPU n and n + 8 share core n.
        topology = {cpu: ("0", str(cpu % 8)) for cpu in range(16)}
        self.assertEqual(B.load_cpus({2, 3, 4, 5}, topology, 4), [1, 6, 7, 9])
        self.assertEqual(B.load_cpus({0, 1, 2, 3, 4, 5}, topology, 4), [6, 7, 14, 15])
        with self.assertRaises(B.LaneError):
            B.load_cpus(set(range(8)), topology, 1)
        self.assertEqual(B.server_cpus("2,3-5"), {2, 3, 4, 5})

    def test_a_servers_time_counts_its_childrens(self) -> None:
        spin = "import time\nend = time.process_time() + 0.4\nwhile time.process_time() < end: pass\ntime.sleep(5)"
        before = B.usage(os.getpid())
        self.assertGreater(before["cpu_ns"], 0)
        with subprocess.Popen([sys.executable, "-c", spin]) as child:
            try:
                deadline, spent = time.monotonic() + 10, 0
                while spent < 300 and time.monotonic() < deadline:
                    time.sleep(0.05)
                    spent = B.usage(os.getpid())["cpu_user_ms"] - before["cpu_user_ms"]
                self.assertGreaterEqual(spent, 300)
            finally:
                child.kill()


class Records(unittest.TestCase):
    def test_a_reply_shares_the_window_alone(self) -> None:
        got = B.summary(run())
        self.assertEqual(got["server_cpu_us_a_reply"], 100.0)
        self.assertEqual(got["switches_a_reply"], 2.0)
        self.assertEqual(got["server_system_share"], 0.4)
        self.assertEqual(got["load_cpu_share"], 0.05)
        self.assertNotIn("load", got)
        self.assertIs(B.summary(run(), raw=True)["load"]["served"], 10_000)

    def test_the_table_takes_medians_and_their_spread(self) -> None:
        rounds = [B.summary(run(cpu_ns=ms * 1_000_000 + 400_000_000, cpu_user_ms=ms)) for ms in (500, 600, 900)]
        host = {"kept": 2000, "at_kept": B.summary(run()), "sweep": [{"load_cpu_share": 0.1}], "steady": rounds,
                "overload": rounds,
                "limits": {}, "allocations_a_reply": 0.0, "system_calls": {"total_a_reply": 36.0},
                "commands": {"STAT": {"cpu_us_a_reply": 40.0, "p50_us": 120.0, "octets": 24, "kept": True},
                             "OVER": {"cpu_us_a_reply": 1500.0, "p50_us": 9e6, "octets": 2907, "kept": False}}}
        rows = B.table({"hosts": {"nntp-uring": host}}).splitlines()
        self.assertEqual(rows[2], "| `nntp-uring` | 2,000 | 100.0 | 100 (100 to 100) | 1,000 (1,000 to 1,000) | 5 | "
                                  "100.0 (90.0 to 130.0) | 40% | 2.00 | 0.00 | 4.0 | 1,000 | 36.0 |")
        self.assertEqual(rows[-2:], ["| STAT | 24 | 40, 120 |", "| OVER | 2,907 | 1,500, not kept |"])


class Nntp(unittest.TestCase):
    def test_replies_are_read_whole(self) -> None:
        stream = io.BytesIO(b"211 3 1 3 g\r\n220 1 <a@b>\r\nX: y\r\n\r\n..dot\r\n.\r\n223 1 <a@b>\r\n")
        self.assertEqual(B.reply_of(stream), b"211 3 1 3 g\r\n")
        self.assertEqual(B.reply_of(stream), b"220 1 <a@b>\r\nX: y\r\n\r\n..dot\r\n.\r\n")
        self.assertEqual(B.reply_of(stream), b"223 1 <a@b>\r\n")
        with self.assertRaises(B.LaneError):
            B.reply_of(io.BytesIO(b"220 1 <a@b>\r\nX: y\r\n"))

    def test_exchanges_read_back(self) -> None:
        pairs = [(b"", b"200 hi\r\n"), (b"STAT 1\r\n", b"223 1 <a@b>\r\n")]
        self.assertEqual(B.exchanges(b"".join(B.exchange(*p) for p in pairs)), pairs)

    def test_each_command_alone_reads_the_same_articles(self) -> None:
        numbers = B.five()
        for name, commands in B.alone().items():
            with self.subTest(name):
                if name in ("OVER", "GROUP"):
                    self.assertEqual(len(commands), 1)
                    continue
                named = [c.decode().split()[1] for c in commands]
                self.assertEqual(named, [f"<b{n - 1}@x.example>" if "<" in name else str(n) for n in numbers])

    def test_the_mix_reads_the_same_articles_its_ways(self) -> None:
        mix = [line.decode().split() for line in B.nntp_commands()]
        numbers = [int(c[1]) for c in mix if c[0] == "ARTICLE" and not c[1].startswith("<")]
        self.assertEqual(len(numbers), 5)
        self.assertTrue({int(c[1]) for c in mix if c[0] in ("HEAD", "STAT")} <= set(numbers))
        self.assertEqual({c[1] for c in mix if c[1].startswith("<")}, {f"<b{n - 1}@x.example>" for n in numbers[:2]})


if __name__ == "__main__":
    unittest.main()
