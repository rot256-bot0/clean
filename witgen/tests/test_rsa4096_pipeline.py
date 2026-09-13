from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class Rsa4096PipelineTests(unittest.TestCase):
    def test_actual_finite_hybrid_witnesses_and_full_source_relation(self):
        with tempfile.TemporaryDirectory(prefix="witgen-rsa4096-") as output:
            result = subprocess.run(
                [sys.executable, "-B", "tools/run_rsa4096.py", "--output", output],
                cwd=ROOT, capture_output=True, text=True, timeout=900,
            )
            self.assertEqual(result.returncode, 0, (result.stdout + result.stderr)[-16000:])
            receipt = json.loads((Path(output) / "verification.json").read_text())
            self.assertEqual(receipt["status"], "PASS")
            self.assertEqual(receipt["cases"], 3)
            self.assertEqual(receipt["witness_cells"], 160527)
            self.assertEqual(receipt["constraint_rows"], 161242)
            self.assertEqual(len(receipt["results"]), 3)
            self.assertTrue(receipt["source_manifest_unchanged"])
            self.assertTrue(receipt["negative_control"]["failed_rows"])
            self.assertTrue({"bignum.divmod", "field.mul", "field.sub", "field.from_nat",
                             "field.to_nat", "vector.fold"}.issubset(receipt["opcodes"]))
            for case in receipt["results"]:
                self.assertTrue(case["full_cell_match"])
                self.assertTrue(case["allocation_schedule_match"])
                self.assertEqual(case["failed_rows"], [])
                self.assertTrue(case["rsa_check"])


if __name__ == "__main__":
    unittest.main()
