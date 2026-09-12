import json
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class NativeDispatcherTests(unittest.TestCase):
    def test_all_exported_modes_use_the_real_native_backend(self):
        script = ROOT / "tools/build_native.py"
        self.assertTrue(script.is_file(), "native crate generator is not implemented")
        with tempfile.TemporaryDirectory() as tmp:
            export = subprocess.run(
                ["lake", "exe", "witgen", "export", tmp],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(export.returncode, 0, export.stderr)
            build = subprocess.run(
                ["python3", str(script), tmp],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(build.returncode, 0, build.stderr)
        compile_result = subprocess.run(
            [
                "cargo",
                "build",
                "--quiet",
                "--locked",
                "--manifest-path",
                str(ROOT / "backend/Cargo.toml"),
                "--bin",
                "witgen-native",
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(compile_result.returncode, 0, compile_result.stderr)
        requests = [
            {"program": name, "inputs": ["3", "4"]}
            for name in ["quadratic_field", "quadratic_nat", "quadratic_word"]
        ]
        requests += [
            {"program": name, "inputs": ["15", "15", "16"]}
            for name in ["modmul_nat", "modmul_word"]
        ]
        requests += [
            {
                "program": "conditional_fold_word",
                "inputs": [True, ["3", "1", "4"], "2"],
            },
            {"program": "conditional_word", "inputs": [False, ["3", "1", "4"], "2"]},
            {"program": "conditional_word", "inputs": [True, ["17"], "2"]},
        ]
        requests += [
            {"program": "batch_field", "inputs": [True, ["3", "4", "16"], "4"]},
            {"program": "batch_fold_word", "inputs": [False, ["3", "4", "16"], "4"]},
            {"program": "batch_nat", "inputs": [True, ["3", "4"], "4"]},
        ]
        native = subprocess.run(
            [str(ROOT / "backend/target/debug/witgen-native")],
            input="\n".join(map(json.dumps, requests)) + "\n",
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(native.returncode, 0, native.stderr)
        results = [json.loads(line) for line in native.stdout.splitlines()]
        self.assertEqual(len(results), len(requests))
        for result in results[:3]:
            self.assertEqual(result["cells"], [3, 4, 9, 13])
        for result in results[3:5]:
            self.assertEqual(result["cells"], [15, 15, 16, 225, 14, 1])
        expected = [
            {"square": str(x * x % 17), "output": str((x * x % 17 + 2) % 17)}
            for x in [3, 1, 4]
        ]
        self.assertEqual(results[5]["value"], expected)
        self.assertEqual(results[6]["value"], [])
        self.assertIn("error", results[7])
        self.assertEqual(results[8]["cells"], [1, 3, 4, 16, 4, 9, 13, 16, 3, 1, 5])
        self.assertEqual(results[9]["cells"], [0, 3, 4, 16, 4, 0, 0, 0, 0, 0, 0])
        self.assertIn("error", results[10])


if __name__ == "__main__":
    unittest.main()
