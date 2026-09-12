"""The published runtime walkthrough is backed by executable Lean."""
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class RuntimeGuideTests(unittest.TestCase):
    def test_runtime_guide_is_kernel_checked(self):
        source = ROOT / "Witgen/Backends/CaliperRuntimeGuide.lean"
        self.assertTrue(source.is_file(), "published runtime proof module is missing")
        result = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=true", str(source)],
            cwd=ROOT, text=True, capture_output=True, timeout=120,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("sorryAx", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
