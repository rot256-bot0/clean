import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class AxiomAuditTests(unittest.TestCase):
    def test_explicit_whitelist_does_not_change_core_default(self):
        import inspect
        spec = importlib.util.spec_from_file_location("axiom_audit", ROOT / "tools/axiom_audit.py")
        assert spec is not None and spec.loader is not None
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        self.assertIn("allowed_axioms", inspect.signature(module.check_axioms).parameters,
                      "Caliper needs an explicit per-call whitelist, not global mutation")
        expected = ["Example.one"]
        text = "'Example.one' depends on axioms: [propext, Classical.choice, Quot.sound]"
        allowed = module.ALLOWED_AXIOMS | {"Classical.choice"}
        with self.assertRaises(ValueError):
            module.check_axioms(text, expected)
        self.assertEqual(module.check_axioms(text, expected, allowed_axioms=allowed),
                         ["Classical.choice", "Quot.sound", "propext"])
        self.assertEqual(module.ALLOWED_AXIOMS, {"propext", "Quot.sound"})
        with self.assertRaises(ValueError):
            module.check_axioms(text, expected)
        for bad in ("", text + text, text.replace("Example.one", "Example.two"),
                    text.replace("Classical.choice", "sorryAx"),
                    text.replace("Classical.choice", "Lean.ofNativeBool"),
                    text.replace("Classical.choice", "trustCompiler")):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                module.check_axioms(bad, expected, allowed_axioms=allowed)
        for bad_expected in ([], expected + expected):
            with self.assertRaises(ValueError):
                module.check_axioms(text, bad_expected, allowed_axioms=allowed)
        with self.assertRaises(ValueError):
            module.check_axioms(text, expected, allowed_axioms=set())

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
