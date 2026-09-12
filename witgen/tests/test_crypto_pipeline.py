"""The cryptographic main examples must execute from actual proved Lean ASTs."""
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CryptoPipelineTests(unittest.TestCase):
    def test_real_lean_to_crypto_native_pipeline(self):
        script = ROOT / "tools/run_crypto.py"
        self.assertTrue(script.is_file(), "cryptographic pipeline runner is missing")
        source = (ROOT / "Witgen/Crypto/Program.lean").read_text()
        self.assertIn("makeNamedStruct schemaDesc .quad", source)
        self.assertIn("fields![square := square, output := output]", source)
        result = subprocess.run(["python3", str(script)], cwd=ROOT, text=True,
                                capture_output=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads((ROOT / "artifacts/crypto/verification.json").read_text())
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(report["native_cases"], 48)
        self.assertEqual(report["input_pairs"], 12)
        self.assertEqual(report["wide_input_pairs"], 10)
        self.assertEqual(len(report["programs"]), 4)
        self.assertGreaterEqual(report["maximum_unreduced_product_bits"], 500)
        self.assertTrue(report["full_cells_match_lean_and_integer_oracle"])
        self.assertTrue(report["typed_error_controls"])
        self.assertEqual(len(report["axiom_declarations"]), 16)


if __name__ == "__main__":
    unittest.main()
