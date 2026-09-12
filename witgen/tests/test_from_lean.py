import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class LeanExportIntegrationTests(unittest.TestCase):
    def test_proved_lean_program_to_native_buffer(self):
        self.assertTrue(
            (ROOT / "Main.lean").is_file(), "Lean export CLI is not implemented"
        )
        with tempfile.TemporaryDirectory() as tmp:
            exported = subprocess.run(
                ["lake", "exe", "witgen", "export", tmp],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(exported.returncode, 0, exported.stderr)
            module = json.loads((Path(tmp) / "quadratic_field.json").read_text())
        self.assertEqual(module["body"]["op"], "field.mul")
        self.assertEqual(module["wire_layout"]["input_slots"], [0, 1])
        spec = importlib.util.spec_from_file_location(
            "emit_rust", ROOT / "tools/emit_rust.py"
        )
        assert spec is not None and spec.loader is not None
        emitter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(emitter)
        code = emitter.emit_module(module)
        path = ROOT / "backend/src/bin/from_lean_quadratic.rs"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            code
            + '\nfn main() { let mut cells = [3u64,4,0,0].map(witgen_native::F17::from); populate(&mut cells).unwrap(); println!("{}", serde_json::json!(cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>())); }\n'
        )
        native = subprocess.run(
            [
                "cargo",
                "run",
                "--quiet",
                "--locked",
                "--manifest-path",
                str(ROOT / "backend/Cargo.toml"),
                "--bin",
                "from_lean_quadratic",
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(native.returncode, 0, native.stderr)
        self.assertEqual(json.loads(native.stdout), [3, 4, 9, 13])

    def test_export_contains_lowered_and_control_programs(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = subprocess.run(
                ["lake", "exe", "witgen", "export", tmp],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            expected = {
                "quadratic_field": "field.mul",
                "quadratic_nat": "nat.mul",
                "quadratic_word": "word.mul",
                "modmul_nat": "nat.mul",
                "modmul_word": "word.mul",
                "conditional_field": "control.branch",
                "conditional_fold_word": "control.branch",
                "batch_field": "control.map",
                "batch_fold_word": "list.empty",
            }
            for name, op in expected.items():
                path = Path(tmp) / (name + ".json")
                self.assertTrue(path.is_file(), f"missing typed-program export: {name}")
                module = json.loads(path.read_text())
                self.assertEqual(module["body"]["op"], op)
            folded = (Path(tmp) / "conditional_fold_word.json").read_text()
            self.assertNotIn('"control.map"', folded)
            self.assertIn('"control.fold"', folded)

    def test_lean_reference_fixture_generation(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "reference.json"
            result = subprocess.run(
                ["lake", "exe", "witgen", "fixtures", str(path)],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                result.returncode,
                0,
                "reference fixture command missing: " + result.stderr,
            )
            fixtures = json.loads(path.read_text())
        self.assertGreater(len(fixtures), 1000)
        example = next(
            r
            for r in fixtures
            if r["program"] == "quadratic_word" and r["inputs"] == ["3", "4"]
        )
        self.assertEqual(example["expected"]["cells"], [3, 4, 9, 13])
        self.assertTrue(any(r["program"] == "modmul_nat_raw" for r in fixtures))
        batch = next(
            (
                r
                for r in fixtures
                if r["program"] == "batch_fold_word" and r["inputs"][0] is False
            ),
            None,
        )
        self.assertIsNotNone(batch, "fixed-shape batch fixtures are missing")
        assert batch is not None
        self.assertEqual(batch["expected"]["cells"][5:], [0, 0, 0, 0, 0, 0])


if __name__ == "__main__":
    unittest.main()
