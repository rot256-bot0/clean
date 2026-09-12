import json
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class FullDemoTests(unittest.TestCase):
    def test_exhaustive_native_vs_lean_demo(self):
        script = ROOT / "tools/run_demo.py"
        self.assertTrue(script.is_file(), "end-to-end verification runner is missing")
        result = subprocess.run(
            ["python3", str(script)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout[-3000:])
        report = json.loads((ROOT / "artifacts/verification.json").read_text())
        self.assertEqual(report["status"], "PASS")
        self.assertGreater(report["native_cases"], 1000)
        self.assertTrue(report["direct_vs_lowered_code_differs"])
        self.assertTrue(report["wrong_slot_control_rejected"])
        self.assertTrue(report["gmp_large_integer_case"])
        self.assertEqual(report.get("caliper", {}).get("status"), "PASS",
                         "full runner must verify Caliper, not only native Rust")
        self.assertEqual(report["caliper"]["runtime_receipt"],
                         "artifacts/caliper/runtime.json")
        for name in ("quadratic.caliper", "modMul.caliper", "fixedGated.caliper", "runtime.json"):
            self.assertEqual((ROOT / "examples/caliper" / name).read_bytes(),
                             (ROOT / "artifacts/caliper" / name).read_bytes(),
                             "published Caliper snapshot differs from actual export: " + name)


if __name__ == "__main__":
    unittest.main()
