"""Full-width field codegen tests; published examples come from Lean separately."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from test_native_emitter import quad_fixture, lowered_quad_fixture

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from emit_rust import emit_module, EmitError
from build_native import build

P = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def crypto_module(domain):
    module = quad_fixture() if domain == "bn254" else lowered_quad_fixture(domain)
    module["domain"] = domain
    module["input_semantics"] = "bn254"
    module["field_modulus"] = str(P)
    term = module["body"]
    while term["tag"] == "let":
        if term["op"].endswith(".const"):
            term["static"]["value"] = str(P)
        term = term["next"]
    module["wire_layout"] = {"field": "bn254", "cells": 4, "input_slots": [0, 1],
        "outputs": [{"path": ["square"], "slot": 2}, {"path": ["output"], "slot": 3}]}
    return module


class CryptoNativeTests(unittest.TestCase):
    def test_crypto_field_and_gmp_codegen_preserve_full_width(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            names = ["crypto_test_field", "crypto_test_nat"]
            modules = [crypto_module("bn254"), crypto_module("nat")]
            for name, module in zip(names, modules):
                code = emit_module(module)
                self.assertNotIn("F17", code)
                self.assertNotIn(", String>", code)
                self.assertIn("Bn254Scalar", code)
                (directory / (name + ".json")).write_text(json.dumps(module))
            (directory / "manifest.json").write_text(json.dumps({"programs": names}))
            # Use an isolated generated-source destination; no rewrite of main examples.
            build(directory, generated_subdir="crypto_test_generated", binary="emitter_crypto_dispatch")
            subprocess.run(["cargo", "build", "--quiet", "--locked", "--manifest-path",
                            "backend/Cargo.toml", "--bin", "emitter_crypto_dispatch"], cwd=ROOT, check=True)
            pairs = [(P-1, P-1), (P-2, 2**200+17), (2**200+123, 2**190+7), (0, 0)]
            requests = [{"program": name, "inputs": [str(x),str(y)]}
                        for name in names for x,y in pairs]
            requests += [{"program": name, "inputs": [str(P), "0"]} for name in names]
            result = subprocess.run([str(ROOT / "backend/target/debug/emitter_crypto_dispatch")],
                                    input="\n".join(map(json.dumps, requests))+"\n", text=True,
                                    capture_output=True, check=True)
            rows = [json.loads(line) for line in result.stdout.splitlines()]
            self.assertEqual(len(rows), len(requests))
            for request, row in zip(requests, rows):
                x,y = map(int, request["inputs"])
                if x == P:
                    self.assertEqual(row["error_code"], "noncanonical_field")
                else:
                    self.assertEqual(row["cells"], list(map(str,[x,y,x*x%P,(x*x%P+y)%P])))

    def test_crypto_schema_rejects_wrong_modulus_and_single_word_claim(self):
        good = crypto_module("bn254")
        emit_module(good)
        for bad_modulus in [str(P+1), str(P)+" ", P]:
            bad = copy.deepcopy(good)
            bad["field_modulus"] = bad_modulus
            with self.assertRaises(EmitError): emit_module(bad)
        with self.assertRaises(EmitError): emit_module(crypto_module("word"))
        storage_only = crypto_module("nat")
        storage_only.pop("input_semantics")
        storage_only["field_modulus"] = "17"
        with self.assertRaises(EmitError): emit_module(storage_only)


if __name__ == "__main__":
    unittest.main()
