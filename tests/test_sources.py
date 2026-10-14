# SPDX-License-Identifier: AGPL-3.0-or-later
"""The source check's account of headers, on directories made to test it: an include in any form C
allows is seen, one neither present nor printed is refused, and so is a printed one no file
includes; the real native/ is accounted for."""
from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from gatekit import ROOT, script

S = script("compile_sources")


class Headers(unittest.TestCase):
    def tree(self, files: dict[str, str]) -> Path:
        temp = tempfile.TemporaryDirectory(prefix="dn-sources-test-")
        self.addCleanup(temp.cleanup)
        for name, text in files.items():
            (Path(temp.name) / name).write_text(text)
        return Path(temp.name)

    def test_native_is_accounted_for(self) -> None:
        self.assertEqual(S.unaccounted(ROOT / "native", S.GENERATED), [])

    def test_every_form_of_include_is_seen(self) -> None:
        for line in ('#include "p.h"', '  #  include "p.h"', '#\tinclude\t"p.h"', '#include"p.h"'):
            with self.subTest(line=line):
                root = self.tree({"a.c": f"{line}\n"})
                self.assertEqual(S.unaccounted(root, {"p.h": "emit-p"}), [])

    def test_a_header_neither_present_nor_printed_is_refused(self) -> None:
        root = self.tree({"a.c": '#include "here.h"\n#include "gone.h"\n', "here.h": "", "b.h": '#include "lost.h"\n'})
        self.assertEqual(S.unaccounted(root, {}), ["included, but neither in native/ nor printed: gone.h",
                                                   "included, but neither in native/ nor printed: lost.h"])

    def test_a_printed_header_no_file_includes_is_refused(self) -> None:
        root = self.tree({"a.c": '#include "p.h"\n#include <q.h>\n'})
        self.assertEqual(S.unaccounted(root, {"p.h": "emit-p", "q.h": "emit-q"}),
                         ["printed, but included by no source: q.h"])


if __name__ == "__main__":
    unittest.main()
