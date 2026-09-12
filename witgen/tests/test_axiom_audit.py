import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class AxiomAuditTests(unittest.TestCase):
    def test_requires_every_expected_declaration_and_only_two_axioms(self):
        path = ROOT / "tools/axiom_audit.py"
        self.assertTrue(path.is_file(), "non-vacuous axiom gate missing")
        spec = importlib.util.spec_from_file_location("axiom_audit", path)
        assert spec is not None and spec.loader is not None
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        expected = ["Example.one", "Example.two"]
        with self.assertRaises(ValueError):
            module.check_axioms("", expected)
        good = "'Example.one' depends on axioms: [propext, Quot.sound]\n'Example.two' does not depend on any axioms\n"
        self.assertEqual(module.check_axioms(good, expected), ["Quot.sound", "propext"])
        with self.assertRaises(ValueError):
            module.check_axioms(
                good.replace("Quot.sound", "Classical.choice"), expected
            )
        with self.assertRaises(ValueError):
            module.check_axioms(good + good, expected)


if __name__ == "__main__":
    unittest.main()
