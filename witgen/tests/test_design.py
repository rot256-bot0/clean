"""Keep code-first publication excerpts tied to the checked sources."""
import hashlib
import json
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class DesignTests(unittest.TestCase):
    def test_caliper_runtime_section_and_exact_excerpts(self):
        result = subprocess.run(["python3", "tools/update_design.py"], cwd=ROOT,
                                text=True, capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        text = (ROOT.parent / "doc/witgen-dsl-design.md").read_text()
        self.assertIn("## 7. Caliper Integration and Runtime Proofs", text)
        self.assertIn("field.Square", text)
        self.assertIn("field.Mul", text)
        self.assertIn("field.Add", text)
        self.assertIn("def fieldModel", text)
        self.assertIn("def ofNat", text)
        self.assertIn("n % p", text)
        self.assertIn("Residue.square a", text)
        self.assertIn("curve.Scale", text)
        self.assertIn("curve.ToAffine", text)
        self.assertIn("curve.FromAffine", text)
        self.assertIn("struct.Set", text)
        self.assertIn("struct.Named", text)
        self.assertIn("Caliper consumes only the U64-level program", text)
        self.assertIn("Field → U64", text)
        self.assertIn("fn method_1", text)
        self.assertIn("0..256usize", text)
        self.assertIn("not a Rust runtime", text)
        self.assertNotIn("Errors Are Values", text)
        self.assertNotIn("pub enum Error", text)
        self.assertNotIn("DataOp", text)
        self.assertNotRegex(text, r"(?m)^## 8\.")
        self.assertNotIn("Checks and Boundaries", text)
        self.assertNotIn("[Verification and Scope]", text)
        receipts = json.loads((ROOT / "artifacts/design-snippets.json").read_text())
        self.assertGreater(len(receipts), 0)
        for receipt in receipts:
            path = ROOT.parent / receipt["path"]
            lines = path.read_text().splitlines()
            excerpt = "\n".join(lines[receipt["start"] - 1:receipt["end"]])
            self.assertEqual(hashlib.sha256(excerpt.encode()).hexdigest(), receipt["sha256"])
            self.assertIn(excerpt, text)


if __name__ == "__main__":
    unittest.main()
