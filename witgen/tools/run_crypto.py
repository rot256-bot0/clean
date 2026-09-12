#!/usr/bin/env python3
"""Reproduce the actual BN254 feature→StructOp/field→Nat→native examples."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

from axiom_audit import check_axioms
from build_native import build
from emit_rust import BN254_MODULUS

ROOT = Path(__file__).resolve().parents[1]
ART = ROOT / "artifacts/crypto"
PROGRAMS = ("quad_bn254", "quad_nat", "envelope_bn254", "envelope_nat")
AUDIT_DECLARATIONS = (
    "Witgen.Crypto.bn254Positive",
    "Witgen.Crypto.Residue.mul_val",
    "Witgen.Crypto.fieldToNat_law",
    "Witgen.Crypto.fieldToNat_correct",
    "Witgen.Crypto.quadToField_correct",
    "Witgen.Crypto.QuadCircuit.sound",
    "Witgen.Crypto.QuadCircuit.constraints_iff",
    "Witgen.Crypto.QuadCircuit.Slots.noAliases",
    "Witgen.Crypto.QuadCircuit.Slots.covers",
    "Witgen.Crypto.quadNatWitgen",
    "Witgen.Crypto.quad_full_buffer_agrees",
    "Witgen.Crypto.quad_nat_raw_buffer",
    "Witgen.Crypto.quad_nat_buffer_correct",
    "Witgen.Crypto.envelopeNat_raw_buffer",
    "Witgen.Crypto.envelope_nat_buffer_correct",
    "Witgen.Crypto.envelopeOutputPaths_exact",
)


def source_hashes():
    paths = set((ROOT / "Witgen").rglob("*.lean"))
    paths.update(ROOT / name for name in (
        "MainCrypto.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "tools/run_crypto.py", "tools/axiom_audit.py", "tools/build_native.py", "tools/emit_rust.py",
        "backend/Cargo.toml", "backend/Cargo.lock", "backend/src/lib.rs",
        "backend/src/error.rs", "backend/src/crypto.rs"))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def expected_inputs():
    p = BN254_MODULUS
    return [(0, 0), (1, p-1), (p-1, p-2), (p-2, p-3),
            (2**64, 2**64+1), (2**128+123, p-1), (2**200+7, 2**192+9),
            (p//2, p//3), (p-123456789, p-987654321), (2**253, 2**250),
            (p-5, 2**128), (2**65+99, 2**129+101)]


def validate_cases(cases, results):
    expected = Counter((name, str(x), str(y)) for name in PROGRAMS for x, y in expected_inputs())
    actual = Counter((c["program"], *c["inputs"]) for c in cases)
    if actual != expected or len(results) != len(cases):
        raise ValueError("crypto fixture/native result coverage mismatch")
    p = BN254_MODULUS
    for case, result in zip(cases, results):
        x, y = map(int, case["inputs"])
        oracle = list(map(str, [x, y, x*x % p, (x*x % p + y) % p]))
        if case["expected"] != {"cells": oracle}:
            raise ValueError("Lean full witness differs from independent integer arithmetic")
        if result.get("program") != case["program"] or result.get("cells") != oracle or "error" in result:
            raise ValueError("native full witness differs from Lean/integer arithmetic")


def run_all():
    ART.mkdir(parents=True, exist_ok=True)
    (ART / "verification.json").unlink(missing_ok=True)
    before = source_hashes()
    commands = []

    def run(command, log, input_text=None):
        result = subprocess.run(command, cwd=ROOT, text=True, input=input_text,
                                capture_output=True, timeout=180)
        (ART / log).write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(f"{command!r} failed: {(result.stdout + result.stderr)[-3500:]}")
        commands.append({"argv": command, "log": log, "returncode": result.returncode})
        return result.stdout

    run(["lake", "build", "Witgen.Crypto.Tests"], "lean-build.log")
    run(["lake", "env", "lean", "-DwarningAsError=true", "Witgen/Crypto/ExportTests.lean"], "export-tests.log")
    axioms = run(["lake", "env", "lean", "-DwarningAsError=true", "Witgen/Crypto/Audit.lean"], "axioms.log")
    dependencies = check_axioms(axioms, AUDIT_DECLARATIONS)
    export = ART / "export"
    run(["lake", "env", "lean", "--run", "MainCrypto.lean", "export", "artifacts/crypto/export"], "export.log")
    run(["lake", "env", "lean", "--run", "MainCrypto.lean", "fixtures", "artifacts/crypto/reference.json"], "fixtures.log")
    manifest = json.loads((export / "manifest.json").read_text())
    if Counter(manifest["programs"]) != Counter(PROGRAMS):
        raise ValueError("crypto export manifest mismatch")
    build(export, generated_subdir="generated_crypto", binary="witgen-crypto")
    run(["cargo", "build", "--locked", "--manifest-path", "backend/Cargo.toml", "--bin", "witgen-crypto"], "rust-build.log")
    binary = ROOT / "backend/target/debug/witgen-crypto"
    cases = json.loads((ART / "reference.json").read_text())
    requests = [{"program": c["program"], "inputs": c["inputs"]} for c in cases]
    output = run([str(binary)], "native-results.jsonl", "\n".join(map(json.dumps, requests)) + "\n")
    results = [json.loads(line) for line in output.splitlines()]
    validate_cases(cases, results)
    invalid = []
    expected_codes = []
    for name in PROGRAMS:
        for inputs, code in [([str(BN254_MODULUS), "0"], "noncanonical_field"),
                             ([str(BN254_MODULUS+1), "0"], "noncanonical_field"),
                             (["-1", "0"], "negative_natural"),
                             (["not-a-number", "0"], "invalid_integer"),
                             ([str(2**200)], "input_arity")]:
            invalid.append({"program": name, "inputs": inputs})
            expected_codes.append(code)
    invalid_rows = [json.loads(line) for line in run([str(binary)], "negative-results.jsonl",
                    "\n".join(map(json.dumps, invalid)) + "\n").splitlines()]
    if [row.get("error_code") for row in invalid_rows] != expected_codes:
        raise ValueError("crypto typed-error control failed")
    if any("cells" in row or not isinstance(row.get("error"), str) for row in invalid_rows):
        raise ValueError("invalid input produced a witness or lost diagnostics")
    after = source_hashes()
    if before != after:
        raise ValueError("source changed during crypto verification")
    artifact_paths = list(export.glob("*.json")) + [ART / "reference.json", ART / "native-results.jsonl"]
    artifact_paths += list((ROOT / "backend/src/generated_crypto").glob("*"))
    artifact_paths += [ROOT / "backend/src/bin/witgen-crypto.rs"]
    report = {"status": "PASS", "programs": list(PROGRAMS), "native_cases": len(cases),
              "input_pairs": len(expected_inputs()),
              "wide_input_pairs": sum(x >= 2**64 for x, _ in expected_inputs()),
              "maximum_unreduced_product_bits": max((x*x).bit_length() for x, _ in expected_inputs()),
              "full_cells_match_lean_and_integer_oracle": True, "typed_error_controls": True,
              "typed_error_control_count": len(invalid_rows),
              "field": "BN254 scalar Fr", "field_modulus": str(BN254_MODULUS),
              "axioms": dependencies, "axiom_declarations": list(AUDIT_DECLARATIONS),
              "commands": commands, "source_hashes": after,
              "artifact_hashes": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in sorted(artifact_paths)},
              "scope": {"full_width_field_and_gmp": True, "one_word_field_lowering": False,
                        "formal_primality_certificate": False,
                        "native_serialization_compiler_libraries": "tested, not kernel-verified"}}
    (ART / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


if __name__ == "__main__":
    report = run_all()
    print(json.dumps({key: value for key, value in report.items()
                     if key not in {"source_hashes", "artifact_hashes", "commands"}}, indent=2))
