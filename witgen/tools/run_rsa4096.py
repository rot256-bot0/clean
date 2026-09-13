"""Execute the finite Lean hybrid AST, compare every cell, and check the pinned source relation.

The independent Python reference is source-reviewed, not extracted from Lean.
An original-Lean oracle, when separately available, is an additional assurance layer.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_manifest():
    paths = {ROOT / name for name in ["MainRSA.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]}
    for directory in ["Witgen", "tools", "tests"]:
        paths.update(p for p in (ROOT / directory).rglob("*")
                     if p.is_file() and p.suffix in {".lean", ".py", ".json", ".gz"}
                     and "__pycache__" not in p.parts)
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(paths)}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(command, output, name, commands, timeout=300):
    start = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    (output / (name + ".log")).write_text(result.stdout + result.stderr)
    commands.append({"name": name, "argv": command, "exit_code": result.returncode,
                     "seconds": round(time.monotonic() - start, 3)})
    (output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
    require(result.returncode == 0, f"{name} failed; see {name}.log\n{(result.stdout + result.stderr)[-12000:]}")
    return result.stdout


def opcodes(value):
    found = set()
    stack = [value]
    while stack:
        node = stack.pop()
        if isinstance(node, dict):
            if "op" in node:
                found.add(node["op"])
            stack.extend(node.values())
        elif isinstance(node, list):
            stack.extend(node)
    return found


def verify(output):
    # Imports with data dependencies occur only after stale PASS removal in main.
    from rsa4096.io import CONSTRAINT_ROWS, FIELD_PRIME, WITNESS_CELLS, decode_public_inputs, decode_witness
    from rsa4096.reference import Runner
    from rsa4096.audit import RSA_AUDIT
    from axiom_audit import check_axioms

    before = source_manifest()
    pin = json.loads((ROOT / "tools/rsa4096/source-pin.json").read_text())
    require(pin["allocations"] == WITNESS_CELLS and pin["constraints"] == CONSTRAINT_ROWS, "source count pin drift")
    with gzip.open(ROOT / "tools/rsa4096/allocation-manifest.json.gz", "rt") as stream:
        manifest = json.load(stream)
    require(manifest["field_modulus"] == FIELD_PRIME, "field parameter drift")
    require(manifest["submission_id"] == pin["submission_id"], "allocation layout source drift")
    events = []
    for event in manifest["events"]:
        if event["kind"] == "witness":
            events.append(("witness", event["count"]))
        elif event["kind"] == "assert":
            events.extend([("assert", 1)] * event["count"])
        else:
            raise RuntimeError("unexpected allocation-manifest event")
    require(sum(n for kind, n in events if kind == "witness") == WITNESS_CELLS, "incomplete witness schedule")
    require(sum(n for kind, n in events if kind == "assert") == CONSTRAINT_ROWS, "incomplete constraint schedule")
    fixture_paths = sorted((ROOT / "tests/data/rsa4096").glob("case-*.json"))
    require(len(fixture_paths) == 3, "expected exactly three maintained RSA fixtures")
    fixtures = [json.loads(path.read_text()) for path in fixture_paths]
    identities = {(r["modulus"], r["signature"], r["digest"]) for r in fixtures}
    require(len(identities) == len(fixtures), "duplicate RSA fixture")
    commands = []
    version = run(["lake", "env", "lean", "--version"], output, "lean-version", commands)
    require("version 4.32.2" in version, "wrong WitGen Lean toolchain")
    run(["lake", "build", "Witgen.Examples.RSA4096.ProgramTests", "Witgen.Examples.RSA4096.CodecTests",
         "Witgen.Examples.RSA4096.IOTests", "Witgen.Typed.BigNumAudit"], output, "lean-build", commands)
    audit_text = run(["lake", "env", "lean", "-DwarningAsError=true", "Witgen/RsaAudit.lean"],
                     output, "model-axioms", commands, timeout=60)
    model_axioms = check_axioms(audit_text, RSA_AUDIT)
    ir_path = output / "rsa4096_hybrid.json"
    run(["lake", "env", "lean", "--run", "MainRSA.lean", "export", str(ir_path)], output, "typed-export", commands)
    operations = opcodes(json.loads(ir_path.read_text()))
    require({"bignum.divmod", "field.mul", "field.sub", "field.from_nat", "field.to_nat", "vector.fold"} <= operations,
            "actual exported program is missing the hybrid arithmetic path")
    results = []
    negative = None
    for index, (fixture_path, fixture) in enumerate(zip(fixture_paths, fixtures)):
        stem = fixture_path.stem
        request = decode_public_inputs(fixture)
        input_path = output / (stem + ".inputs.json")
        output_path = output / (stem + ".witness.json")
        input_path.write_text(json.dumps(request, indent=2) + "\n")
        run(["lake", "env", "lean", "--run", "MainRSA.lean", "run", str(input_path), str(output_path)],
            output, stem + "-lean", commands)
        cells = decode_witness(json.loads(output_path.read_text()))
        inputs = [bytes.fromhex(fixture[k]) for k in ["modulus", "digest", "signature"]]
        generator = Runner()
        generated = generator.run(*inputs)
        checker = Runner(cells)
        checked = checker.run(*inputs)
        full_match = cells == generator.witness
        schedule_match = checker.events == generator.events == events
        require(full_match, f"{stem}: complete Lean/source-oracle witness mismatch")
        require(schedule_match, f"{stem}: interleaved allocation/assertion schedule mismatch")
        require(not checked["failed_rows"] and not generated["failed_rows"], f"{stem}: source relation rejected witness")
        require(checked["rsa_check"] and generated["rsa_check"], f"{stem}: independent RSA equation rejected fixture")
        row = {"case": stem, "fixture_sha256": digest(fixture_path), "witness_sha256": digest(output_path),
               "full_cell_match": full_match, "allocation_schedule_match": schedule_match,
               "failed_rows": checked["failed_rows"], "rsa_check": checked["rsa_check"],
               "witness_cells": len(cells), "constraint_rows": checked["constraints"]}
        (output / (stem + ".verification.json")).write_text(json.dumps(row, indent=2) + "\n")
        results.append(row)
        if index == 0:
            altered = cells.copy()
            require(altered[-1] in (0, 1), "last allocated carry bit is not Boolean")
            altered[-1] = 1 - altered[-1]
            rejected = Runner(altered).run(*inputs)
            require(bool(rejected["failed_rows"]), "last-carry-bit negative control was accepted")
            negative = {"mutation": "flip the last allocated carry bit", "failed_rows": rejected["failed_rows"]}
        print(json.dumps({"case": stem, "cells": len(cells), "rows": checked["constraints"], "full_cell_match": full_match}), flush=True)
    saved = [json.loads((output / (path.stem + ".verification.json")).read_text()) for path in fixture_paths]
    require(saved == results and len(saved) == 3, "incomplete saved case coverage")
    after = source_manifest()
    unchanged = before == after
    require(unchanged, "sources changed during verification")
    artifacts = {p.relative_to(output).as_posix(): digest(p) for p in sorted(output.iterdir())
                 if p.is_file() and p.name not in {"verification.json", "verification.tmp.json", "failure.json"}}
    receipt = {"status": "PASS", "evidence": "SOURCE_REVIEWED_NOT_LEAN_BOUND",
               "submission_id": pin["submission_id"], "source_archive_sha256": pin["archive_sha256"],
               "cases": len(saved), "witness_cells": WITNESS_CELLS, "constraint_rows": CONSTRAINT_ROWS,
               "opcodes": sorted(operations), "results": saved, "negative_control": negative,
               "model_axioms": model_axioms, "model_audit_count": len(RSA_AUDIT),
               "source_manifest_unchanged": unchanged, "sources": after, "artifacts": artifacts,
               "lean_version": version.strip(), "commands": commands}
    pending = output / "verification.tmp.json"
    pending.write_text(json.dumps(receipt, indent=2) + "\n")
    pending.replace(output / "verification.json")
    print(json.dumps({"status": receipt["status"], "cases": len(saved), "evidence": receipt["evidence"]}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/rsa4096")
    args = parser.parse_args()
    output = args.output.resolve()
    for name in ["Witgen", "tools", "tests"]:
        protected = ROOT / name
        if output == protected or protected in output.parents:
            parser.error("output may not overwrite source directories")
    output.mkdir(parents=True, exist_ok=True)
    for name in ["verification.json", "verification.tmp.json", "failure.json"]:
        (output / name).unlink(missing_ok=True)
    try:
        verify(output)
    except Exception as error:
        (output / "failure.json").write_text(json.dumps({"status": "FAIL", "error": str(error)}, indent=2) + "\n")
        print(str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
