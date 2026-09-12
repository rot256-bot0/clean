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
        self.assertIn("theorem quadratic_runtime", text)
        self.assertIn("theorem quadratic_exact_cost", text)
        self.assertIn("not a Rust runtime", text)
        self.assertIn("mem.alloci b0, 4", text)
        self.assertIn("### Observed Runs and Proved Profiles", text)
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
