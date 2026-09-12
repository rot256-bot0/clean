#!/usr/bin/env python3
"""Reproduce kernel builds, code generation, native execution and controls."""

import copy
import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

from axiom_audit import check_axioms
from build_native import build
from emit_rust import EmitError, emit_module
from run_caliper import run_all as run_caliper

ROOT = Path(__file__).resolve().parents[1]
ART = ROOT / "artifacts"


def run(command, log, input_text=None):
    result = subprocess.run(
        command, cwd=ROOT, input=input_text, text=True, capture_output=True, check=False
    )
    (ART / log).write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(
            f"command failed: {command!r}\n{result.stdout[-3000:]}\n{result.stderr[-3000:]}"
        )
    return result.stdout


def satisfies(program, inputs, result):
    if program.startswith("quadratic_"):
        x, y = map(int, inputs)
        w = result["cells"]
        return (
            len(w) == 4
            and w[:2] == [x, y]
            and all(0 <= z < 17 for z in w)
            and w[2] == x * x % 17
            and w[3] == (w[2] + y) % 17
        )
    if program in {"modmul_nat", "modmul_word"}:
        a, b, n = map(int, inputs)
        w = result["cells"]
        return (
            len(w) == 6
            and w[:3] == [a, b, n]
            and all(0 <= z < 257 for z in w)
            and 0 < n <= 16
            and a < n
            and b < n
            and w[3] == a * b
            and w[3] == w[4] * n + w[5]
            and w[4] < n
            and w[5] < n
        )
    if program == "modmul_nat_raw":
        a, b, n = map(int, inputs)
        w = {k: int(v) for k, v in result["value"].items()}
        return (
            w["product"] == a * b
            and w["product"] == w["quotient"] * n + w["remainder"]
            and 0 <= w["remainder"] < n
        )
    if program.startswith("conditional_"):
        enabled, xs, offset = inputs
        xs, offset = list(map(int, xs)), int(offset)
        expected = (
            [
                {"square": str(x * x % 17), "output": str((x * x % 17 + offset) % 17)}
                for x in xs
            ]
            if enabled
            else []
        )
        return result["value"] == expected
    if program.startswith("batch_"):
        enabled, xs, offset = inputs
        xs, offset = list(map(int, xs)), int(offset)
        w = result["cells"]
        expected = [int(enabled), *xs, offset]
        for x in xs:
            square = x * x % 17 if enabled else 0
            expected += [square, (square + offset) % 17 if enabled else 0]
        return (
            len(xs) == 3
            and len(w) == 11
            and w == expected
            and all(0 <= x < 17 for x in w)
        )
    raise AssertionError("independent checker missing for " + program)


def main():
    ART.mkdir(exist_ok=True)
    (ART / "verification.json").unlink(missing_ok=True)
    targets = [
        "Witgen.CoreTests",
        "Witgen.ArithmeticTests",
        "Witgen.DemoTests",
        "Witgen.CircuitTests",
        "Witgen.IntegrationTests",
        "Witgen.ExportTests",
        "Witgen.BatchTests",
        "witgen",
    ]
    run(["lake", "build", *targets], "lean-build.log")
    proofs = (ART / "lean-build.log").read_text()
    if "sorryAx" in proofs or "Lean.ofNativeBool" in proofs:
        raise AssertionError("forbidden proof trust in build output")
    audit_source = ROOT / "Witgen/Audit.lean"
    expected_declarations = re.findall(
        r"^#print axioms (\S+)$", audit_source.read_text(), re.MULTILINE
    )
    run(
        ["lake", "env", "lean", "-DwarningAsError=true", "Witgen/Audit.lean"],
        "axiom-audit.log",
    )
    dependencies = check_axioms(
        (ART / "axiom-audit.log").read_text(), expected_declarations
    )
    export = ART / "export"
    export.mkdir(exist_ok=True)
    run(["lake", "exe", "witgen", "export", str(export)], "export.log")
    reference = ART / "reference.json"
    run(["lake", "exe", "witgen", "fixtures", str(reference)], "reference.log")
    build(export)
    run(
        [
            "cargo",
            "build",
            "--locked",
            "--manifest-path",
            "backend/Cargo.toml",
            "--bin",
            "witgen-native",
        ],
        "rust-build.log",
    )
    cases = json.loads(reference.read_text())
    requests = [{"program": x["program"], "inputs": x["inputs"]} for x in cases]
    output = run(
        [str(ROOT / "backend/target/debug/witgen-native")],
        "native-results.jsonl",
        "\n".join(map(json.dumps, requests)) + "\n",
    )
    results = [json.loads(line) for line in output.splitlines()]
    assert len(results) == len(cases), (len(results), len(cases))
    for index, (case, result) in enumerate(zip(cases, results)):
        if "error" in result or any(
            result.get(k) != v for k, v in case["expected"].items()
        ):
            raise AssertionError(
                f"native/reference mismatch at {index}, {case['program']}: {str(result)[:1200]}"
            )
        assert satisfies(case["program"], case["inputs"], result), (
            index,
            case["program"],
        )
    generated = ROOT / "backend/src/generated"
    field = (generated / "quadratic_field.rs").read_text()
    natural = (generated / "quadratic_nat.rs").read_text()
    word = (generated / "quadratic_word.rs").read_text()
    assert (
        "witgen_native::f17_mul" in field
        and "witgen_native::nat_mul" in natural
        and "witgen_native::word_mul" in word
    )
    assert "rug::Integer" in natural and "rug::Integer" not in word
    assert field != natural != word
    folded = (export / "conditional_fold_word.json").read_text()
    assert '"control.map"' not in folded and '"control.fold"' in folded
    wrong = copy.deepcopy(json.loads((export / "quadratic_word.json").read_text()))
    (
        wrong["wire_layout"]["outputs"][0]["slot"],
        wrong["wire_layout"]["outputs"][1]["slot"],
    ) = 3, 2
    bad_code = emit_module(wrong)
    path = ROOT / "backend/src/bin/wrong_slots.rs"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        bad_code
        + '\nfn main() { let mut cells=[3u64,4,0,0].map(witgen_native::F17::from); populate(&mut cells).unwrap(); println!("{}",serde_json::json!(cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>())); }\n'
    )
    bad_output = run(
        [
            "cargo",
            "run",
            "--quiet",
            "--locked",
            "--manifest-path",
            "backend/Cargo.toml",
            "--bin",
            "wrong_slots",
        ],
        "wrong-slot.log",
    )
    bad_cells = json.loads(bad_output)
    assert not satisfies("quadratic_word", ["3", "4"], {"cells": bad_cells})
    missing = copy.deepcopy(wrong)
    missing["wire_layout"]["outputs"].pop()
    try:
        emit_module(missing)
    except EmitError:
        pass
    else:
        raise AssertionError("missing-cell layout accepted")
    counts = Counter(x["program"] for x in cases)
    large = [x for x in cases if x["program"] == "modmul_nat_raw"]
    assert large and int(large[0]["inputs"][0]).bit_length() == 4096
    caliper = run_caliper()
    if caliper.get("status") != "PASS":
        raise AssertionError("Caliper verification did not pass")
    hashes = {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted((ROOT / "Witgen").rglob("*.lean"))
    }
    report = {
        "status": "PASS",
        "native_cases": len(cases),
        "per_program": dict(sorted(counts.items())),
        "lean_targets": targets,
        "axioms": sorted(set(dependencies)),
        "axiom_declarations": expected_declarations,
        "direct_vs_lowered_code_differs": True,
        "map_to_fold_observed": True,
        "wrong_slot_control_rejected": True,
        "wrong_slot_cells": bad_cells,
        "missing_cell_layout_rejected": True,
        "gmp_large_integer_case": True,
        "caliper": {
            "status": caliper["status"],
            "verification_receipt": "artifacts/caliper/verification.json",
            "runtime_receipt": "artifacts/caliper/runtime.json",
        },
        "source_hashes": hashes,
        "trust_boundary": [
            "Lean kernel and its standard foundations for proofs",
            "Lean JSON serialization, Python Rust emission, rustc, arkworks and GMP/rug tested, not kernel-verified",
            "Caliper Exec/Triple costs concern emitted analysis programs, not Rust or hardware runtime; buffer capacity excludes registers",
        ],
    }
    (ART / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps({k: v for k, v in report.items() if k != "source_hashes"}, indent=2)
    )


if __name__ == "__main__":
    main()
