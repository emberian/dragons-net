"""Exercise gate failures on disposable copies; never mutate the working tree."""
import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("structure", ROOT / "scripts/check_structure.py")
structure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(structure)


class Gates(unittest.TestCase):
    def test_new_proof_cannot_escape_audit(self):
        with tempfile.TemporaryDirectory() as temp:
            copy = Path(temp)
            for directory in ("lean", "rfcs", "backend"):
                shutil.copytree(ROOT / directory, copy / directory)
            (copy / "lean/DN/Unlisted.lean").write_text("namespace DN\ntheorem extra : 1 = 1 := rfl\nend DN\n")
            self.assertTrue(any("missing" in e for e in structure.check(copy)))

    def test_transitive_axiom_dependency_fails(self):
        for declaration in ["theorem unsound : False := Foreign.bad",
                            "noncomputable def unchecked : Nat := False.elim Foreign.bad"]:
            with self.subTest(declaration=declaration), tempfile.TemporaryDirectory() as temp:
                source = Path(temp) / "Bad.lean"
                source.write_text("import DN.Audit\nnamespace Foreign\naxiom bad : False\nend Foreign\n"
                                  f"namespace DN.Bad\n{declaration}\nend DN.Bad\n#audit_dn\n")
                result = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT,
                                        text=True, capture_output=True, timeout=60)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("unapproved axioms", result.stdout + result.stderr)

    def test_emitter_has_no_build_side_effects(self):
        binary = ROOT / ".lake/build/bin/dn-compiler"
        with tempfile.TemporaryDirectory() as temp:
            first = subprocess.run([str(binary), "emit-region"], cwd=temp, check=True,
                                   text=True, capture_output=True).stdout
            second = subprocess.run([str(binary), "emit-region"], cwd=temp, check=True,
                                    text=True, capture_output=True).stdout
            self.assertEqual(first, second)
            self.assertEqual(list(Path(temp).iterdir()), [])
            self.assertTrue(first.startswith("export fun dn_region("))
            result = subprocess.run([str(binary), "unknown"], capture_output=True)
            self.assertEqual(result.returncode, 2)
