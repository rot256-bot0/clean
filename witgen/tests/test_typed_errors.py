"""Generated native APIs preserve typed failures through to the JSON boundary."""
import json
from pathlib import Path
import subprocess
import sys
import unittest

from test_native_emitter import quad_fixture, lowered_quad_fixture
from test_batch_writer import batch_module

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from emit_rust import emit_module
from build_native import build


class TypedErrorTests(unittest.TestCase):
    def test_codegen_uses_native_result_and_structured_writer_errors(self):
        for module in (quad_fixture(), lowered_quad_fixture("word"), batch_module()):
            code = emit_module(module)
            self.assertNotIn(", String>", code)
            self.assertIn("witgen_native::Result<", code)
        code = emit_module(batch_module())
        self.assertIn("Error::WitnessLength", code)
        self.assertIn("Error::NonBooleanCell", code)

    def test_runtime_providers_return_typed_errors(self):
        code = r'''
fn main() {
    use witgen_native::*;
    assert!(matches!(f17_from_u64(17), Err(Error::NonCanonicalField { field: "field17" })));
    assert!(matches!(f257_from_u64(257), Err(Error::NonCanonicalField { field: "field257" })));
    assert!(matches!(nat_from_str("-1"), Err(Error::NegativeNatural)));
    assert!(matches!(nat_from_str("no"), Err(Error::ParseInteger(_))));
    assert!(matches!(word_from_nat(&(rug::Integer::from(1) << 65)), Err(Error::WordOverflow)));
    for result in [word_div(1,0), word_mod(1,0)] {
        assert!(matches!(result, Err(Error::DivisionByZero)));
    }
    for result in [nat_div(&1.into(), &0.into()), nat_mod(&1.into(), &0.into())] {
        assert!(matches!(result, Err(Error::DivisionByZero)));
    }
    assert!(matches!(nat_div(&(-1).into(), &1.into()), Err(Error::NegativeNatural)));
    assert!(matches!(nat_mod(&1.into(), &(-1).into()), Err(Error::NegativeNatural)));
}
'''
        path = ROOT / "backend/src/bin/emitter_typed_errors.rs"
        path.parent.mkdir(exist_ok=True)
        path.write_text(code)
        result = subprocess.run(["cargo", "run", "--quiet", "--locked", "--manifest-path",
                                 "backend/Cargo.toml", "--bin", "emitter_typed_errors"],
                                cwd=ROOT, text=True, capture_output=True, timeout=90)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_cli_keeps_diagnostics_and_exposes_error_codes(self):
        # Rebuild from existing real exports; this test does not manufacture witness results.
        self.assertTrue((ROOT / "artifacts/export/manifest.json").is_file())
        build(ROOT / "artifacts/export")
        subprocess.run(["cargo", "build", "--quiet", "--locked", "--manifest-path",
                        "backend/Cargo.toml", "--bin", "witgen-native"], cwd=ROOT, check=True)
        requests = ["{", "{}", json.dumps({"program": "unknown", "inputs": []}),
                    json.dumps({"program": "quadratic_field", "inputs": ["17", "0"]}),
                    json.dumps({"program": "quadratic_field", "inputs": ["0"]}),
                    json.dumps({"program": 23, "inputs": []}),
                    json.dumps({"program": "quadratic_field", "inputs": {}})]
        result = subprocess.run([str(ROOT / "backend/target/debug/witgen-native")],
                                input="\n".join(requests)+"\n", text=True,
                                capture_output=True, check=True)
        errors = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(errors), len(requests))
        self.assertEqual([error.get("error_code") for error in errors],
                         ["invalid_json", "missing_field", "unknown_program",
                          "noncanonical_field", "input_arity", "invalid_input_type", "invalid_input_type"])
        self.assertTrue(all(isinstance(e["error"], str) and e["error"] for e in errors))


if __name__ == "__main__":
    unittest.main()
