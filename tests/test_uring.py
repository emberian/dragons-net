# SPDX-License-Identifier: AGPL-3.0-or-later
"""The io_uring lane's own tables: each planted defect finds its one place. The lane builds the Cake copies the host
declares, and enables every failure point the sources carry."""
from __future__ import annotations

from pathlib import Path
import re
import unittest

from gatekit import script

U = script("uring_check")


class Tables(unittest.TestCase):
    def test_each_defect_finds_its_place(self) -> None:
        for defect in U.DEFECTS:
            with self.subTest(defect.what):
                self.assertEqual(defect.file.read_text().count(defect.pattern), defect.times)

    def test_each_defect_names_a_check_the_lane_has(self) -> None:
        source = Path(U.__file__).read_text()
        for defect in U.DEFECTS:
            with self.subTest(defect.what):
                self.assertTrue(defect.caught_by == "layer" or f'"{defect.caught_by}": lambda' in source)

    def test_the_copies_built_are_those_declared(self) -> None:
        text = U.ECHO.read_text()
        declared = re.findall(r"COPY\((\d+)\)", text)
        self.assertEqual(sorted(set(declared), key=int), [str(k) for k in range(U.COPIES)])
        self.assertEqual(len(declared), 2 * U.COPIES)

    def test_every_point_of_failure_is_enabled(self) -> None:
        points = {name for source in (U.ECHO, U.LAYER)
                  for name in re.findall(r'DN_FAULT(?:_INFO)?\("([^"]+)"', source.read_text())}
        lane = Path(U.__file__).read_text()
        self.assertTrue(points)
        for point in sorted(points):
            with self.subTest(point):
                self.assertTrue(any(f"{left}{point}{right}" in lane for left in ("name=", '"')
                                    for right in (",", '"')), point)


if __name__ == "__main__":
    unittest.main()
