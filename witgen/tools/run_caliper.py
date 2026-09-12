#!/usr/bin/env python3
"""Fresh Caliper verification (analysis backend, not the Rust engine).

Parent integration: ``from run_caliper import run_all; report = run_all()``.
No arguments; cwd-independent. Returns the JSON-serializable report and writes
artifacts/caliper/verification.json. Raises on any failed command or check.
CLI: ``python3 tools/run_caliper.py``. Does not call run_demo or touch Rust.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tomllib

from axiom_audit import ALLOWED_AXIOMS, check_axioms

ROOT = Path(__file__).resolve().parents[1]
ART = ROOT / "artifacts/caliper"

CALIPER_ALLOWED_AXIOMS = ALLOWED_AXIOMS | {"Classical.choice"}

# Independent inventory: deleting an audit directive must fail, not shrink coverage.
AUDIT_DECLARATIONS = (
    "Witgen.Backends.Caliper.compile_inputs_fresh",
    "Witgen.Backends.Caliper.decode_add",
    "Witgen.Backends.Caliper.decode_mul",
    "Witgen.Backends.Caliper.decode_div",
    "Witgen.Backends.Caliper.decode_mod",
    "Witgen.Backends.Caliper.compileWord_correct",
    "Witgen.Backends.Caliper.compileData_correct",
    "Witgen.Backends.Caliper.quadratic_compiles",
    "Witgen.Backends.Caliper.modMul_compiles",
    "Witgen.Backends.Caliper.quadratic_code",
    "Witgen.Backends.Caliper.modMul_code",
    "Witgen.Backends.Caliper.quadratic_result",
    "Witgen.Backends.Caliper.modMul_result",
    "Witgen.Backends.Caliper.quadraticWord_eval_u64",
    "Witgen.Backends.Caliper.quadratic_run",
    "Witgen.Backends.Caliper.modMul_run",
    "Witgen.Backends.Caliper.fixedGated_compiles",
    "Witgen.Backends.Caliper.fixedGated_result",
    "Witgen.Backends.Caliper.fixedGatedWord_eval",
    "Witgen.Backends.Caliper.fixedGated_run",
    "Witgen.Backends.Caliper.exec_of_observed_run",
    "Witgen.Backends.Caliper.compileWord_frame",
    "Witgen.Backends.Caliper.quadratic_frame",
    "Witgen.Backends.Caliper.modMul_frame",
    "Witgen.Backends.Caliper.fixedGated_frame",
    "Witgen.Backends.Caliper.quadratic_exec",
    "Witgen.Backends.Caliper.modMul_exec",
    "Witgen.Backends.Caliper.fixedGated_exec",
    "Witgen.Backends.CaliperWitness.pushState_regs",
    "Witgen.Backends.CaliperWitness.pushState_caps",
    "Witgen.Backends.CaliperWitness.pushState_tapePos",
    "Witgen.Backends.CaliperWitness.pushState_other",
    "Witgen.Backends.CaliperWitness.pushState_contents",
    "Witgen.Backends.CaliperWitness.pushRegs_exec",
    "Witgen.Backends.CaliperWitness.writeRegs_exec",
    "Witgen.Backends.CaliperWitness.writerState_regs",
    "Witgen.Backends.CaliperWitness.writerState_tapePos",
    "Witgen.Backends.CaliperWitness.writerState_contents",
    "Witgen.Backends.CaliperWitness.writerState_capacity",
    "Witgen.Backends.CaliperWitness.writerState_other",
    "Witgen.Backends.CaliperWitness.writerState_post",
    "Witgen.Backends.CaliperWitness.writeRegs_triple",
    "Witgen.Backends.CaliperWitness.writerTime_unit",
    "Witgen.Backends.CaliperWitness.writerTime_cycles",
    "Witgen.Backends.CaliperWitness.writeRegs_unique",
    "Witgen.Backends.CaliperWitness.pushRegs_noWrites",
    "Witgen.Backends.CaliperWitness.writeRegs_noWrites",
    "Witgen.Backends.CaliperWitness.pushRegs_touches",
    "Witgen.Backends.CaliperWitness.writeRegs_touches",
    "Witgen.Backends.CaliperWitness.writeRegs_liveMem",
    "Witgen.Backends.CaliperWitness.writeRegs_reaches_bound",
    "Witgen.Backends.CaliperWitness.produce_write_exec",
    "Witgen.Backends.CaliperWitness.reserved_load_noExec",
    "Witgen.Backends.CaliperWitness.full_push_noExec",
    "Witgen.Backends.CaliperExamples.quadratic_producer_exec",
    "Witgen.Backends.CaliperExamples.modMul_producer_exec",
    "Witgen.Backends.CaliperExamples.withWitness_exec",
    "Witgen.Backends.CaliperExamples.quadratic_witness_exec",
    "Witgen.Backends.CaliperExamples.modMul_witness_exec",
    "Witgen.Backends.CaliperExamples.quadratic_triple",
    "Witgen.Backends.CaliperExamples.modMul_triple",
    "Witgen.Backends.CaliperExamples.quadratic_unit_cost",
    "Witgen.Backends.CaliperExamples.quadratic_cycles_cost",
    "Witgen.Backends.CaliperExamples.modMul_unit_cost",
    "Witgen.Backends.CaliperExamples.modMul_cycles_cost",
    "Witgen.Backends.CaliperExamples.quadratic_unit_resources",
    "Witgen.Backends.CaliperExamples.modMul_unit_resources",
    "Witgen.Backends.CaliperExamples.quadratic_cells_circuit",
    "Witgen.Backends.CaliperExamples.modMul_cells_circuit",
    "Witgen.Backends.CaliperExamples.quadratic_circuit_exec",
    "Witgen.Backends.CaliperExamples.modMul_circuit_exec",
    "Witgen.Backends.CaliperExamples.quadList_regs_read",
    "Witgen.Backends.CaliperExamples.fixedGated_witness_exec",
    "Witgen.Backends.CaliperExamples.fixedGated_unit_triple",
    "Witgen.Backends.CaliperExamples.fixedGated_unit_cost",
    "Witgen.Backends.CaliperExamples.fixedGated_cycles_cost",
    "Witgen.Backends.CaliperExamples.fixedGated_cycles_triple",
    "Witgen.Backends.CaliperExamples.compiled_register_endpoints",
    "Witgen.Backends.CaliperExamples.quadratic_intermediate_memory",
    "Witgen.Backends.CaliperExamples.modMul_intermediate_memory",
    "Witgen.Backends.CaliperRuntimeGuide.quadratic_runtime",
    "Witgen.Backends.CaliperRuntimeGuide.quadratic_exact_cost",
)


LAYOUTS = {
    "quadratic": ([0, 1], [4, 7], 8),
    "modMul": ([0, 1, 2], [3, 4, 5], 6),
    "fixedGated": ([0, 1, 2, 3], [18, 19, 20, 21], 22),
}
SAMPLES = {
    "quadratic": [("quadratic", (3, 5))],
    "modMul": [("modMul", (7, 9, 11))],
    "fixedGated": [("fixedGated/on", (1, 3, 4, 5)), ("fixedGated/off", (0, 3, 4, 5))],
}


def validate_runtime(runtime, validation):
    """Independently check full arrays, profiles and exact nonempty domain coverage.

    This is a tested Python arithmetic checker, not a replacement interpreter or
    a proof. It only checks observations emitted by the real Lean Caliper.run.
    """
    if (runtime.get("schema_version"), runtime.get("interpreter"), runtime.get("renderer"),
        runtime.get("word_bits"), runtime.get("fuel")) != (
            1, "Caliper.run", "Caliper.Stmt.renderString", 64, 100):
        raise ValueError("unexpected Caliper runtime receipt header")
    programs = runtime.get("programs", [])
    if Counter(p["name"] for p in programs) != Counter(LAYOUTS.keys()):
        raise ValueError("Caliper program coverage mismatch")
    validation_programs = validation.get("programs", [])
    if (validation.get("interpreter") != "Caliper.run" or
        Counter(p["name"] for p in validation_programs) != Counter(LAYOUTS.keys())):
        raise ValueError("finite-domain program coverage mismatch")
    validation_rows = {p["name"]: p["runs"] for p in validation_programs}
    domains = {
        "quadratic": [(x, y) for x in range(17) for y in range(17)],
        "modMul": [(a, b, n) for n in range(1, 17) for a in range(n) for b in range(n)],
        "fixedGated": [],
    }
    counts = {}
    for program in programs:
        name = program["name"]
        inputs, outputs, end = LAYOUTS[name]
        if (program["input_registers"], program["output_registers"], program["next_register"],
            program["first_fresh_register"], program["buffer"]) != (
                inputs, outputs, end, len(inputs), 0):
            raise ValueError(f"{name}: register/buffer metadata mismatch")
        assembly = program["assembly"]
        pushes = [int(r) for r in re.findall(r"^mem\.push\s+b0, r(\d+)$", assembly, re.M)]
        if pushes != inputs + outputs or f"mem.alloci b0, {len(pushes)}" not in assembly:
            raise ValueError(f"{name}: incomplete assembly writer layout")
        if name == "fixedGated" and ("ifnz r0 {" not in assembly or "} else {" not in assembly):
            raise ValueError("missing gated assembly branch")
        for field, cases in (
            ("runs", SAMPLES[name]),
            ("validation_runs", [(name + "/finite", values) for values in domains[name]]),
        ):
            rows = program.get("runs", []) if field == "runs" else validation_rows[name]
            actual = Counter((r["case"], tuple(r["input_values"]), r["cost_model"]) for r in rows)
            expected = Counter((label, values, cost) for label, values in cases for cost in ("unit", "cycles"))
            if actual != expected:
                raise ValueError(f"{name}/{field}: exact case coverage mismatch")
            for row in rows:
                values = row["input_values"]
                if any(type(v) is not int or not 0 <= v < 2 ** 64 for v in values):
                    raise ValueError(f"{name}: non-word input")
                if name == "quadratic":
                    x, y = values
                    square = (x * x % (2 ** 64)) % 17
                    cells = [x, y, square, ((square + y) % (2 ** 64)) % 17]
                    costs = {"unit": 14, "cycles": 90}
                elif name == "modMul":
                    a, b, n = values
                    product = a * b % (2 ** 64)
                    cells = [a, b, n, product, product // n if n else 0, product % n if n else product]
                    costs = {"unit": 15, "cycles": 99}
                else:
                    flag, x0, x1, c = values
                    cells = list(values)
                    for x in (x0, x1):
                        square = (x * x % (2 ** 64)) % 17 if flag else 0
                        cells += [square, ((square + c) % (2 ** 64)) % 17 if flag else 0]
                    costs = {"unit": 33 if flag else 23, "cycles": 186 if flag else 56}
                if row["cells"] != cells:
                    raise ValueError(f"{name}: independent full-cell arithmetic mismatch")
                if (row["time"], row["net_words"], row["peak_words"], row["capacity"]) != (
                    costs[row["cost_model"]], len(cells), len(cells), len(cells)):
                    raise ValueError(f"{name}: resource profile mismatch")
                regs = row["final_registers"]
                if (len(regs) != end or row["tape_position"] != 0 or
                    row["final_input_values"] != values or [regs[r] for r in inputs] != values or
                    row["output_values"] != cells[len(inputs):] or
                    [regs[r] for r in outputs] != cells[len(inputs):]):
                    raise ValueError(f"{name}: output/register/tape frame mismatch")
        if domains[name]:
            counts[name] = {"inputs": len(domains[name]), "runs": len(validation_rows[name])}
    return counts


def source_hashes():
    """Bind local Lean sources, the harness, manifests and pinned Caliper sources."""
    paths = set((ROOT / "Witgen").rglob("*.lean"))
    paths.update((ROOT / ".lake/packages/caliper/Caliper").rglob("*.lean"))
    paths.update(ROOT / path for path in (
        "MainCaliper.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "tools/run_caliper.py", "tools/axiom_audit.py",
        "tests/test_caliper_runner.py", "tests/test_axiom_audit.py",
        ".lake/packages/caliper/Caliper.lean", ".lake/packages/caliper/lakefile.lean",
        ".lake/packages/caliper/lake-manifest.json", ".lake/packages/caliper/lean-toolchain",
    ))
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def proof_scope():
    programs = {}
    for name in LAYOUTS:
        prefix = "Witgen.Backends.CaliperExamples."
        circuit = None if name == "fixedGated" else prefix + name + "_circuit_exec"
        programs[name] = {
            "source_program": ("Witgen.Backends.Caliper." if name == "fixedGated" else "Witgen.Demo.") + name + "Word",
            "code": prefix + name + "Code",
            "word_scope": "Universal execution/full output for this exact checked compiler layout, every word state, tape and cost model; fresh output buffer.",
            "circuit_endpoint": circuit,
            "circuit_assumptions": ({
                "quadratic": "Input registers decode to canonical Field17 inputs (0..16); WellFormed state and zero output-buffer capacity.",
                "modMul": "Input registers decode to a,b,n with 0 < n <= 16, a < n, b < n; WellFormed state and zero output-buffer capacity.",
                "fixedGated": "No circuit claim: two-row fixedGatedWord is not the separate three-row Batch.gatedBatchWord circuit.",
            })[name],
            "endpoints": [endpoint for endpoint in AUDIT_DECLARATIONS
                          if endpoint.startswith(("Witgen.Backends.Caliper." + name + "_", prefix + name + "_"))],
        }
    programs["fixedGated"]["rows"] = 2
    return {
        "generic_compiler_preservation": False,
        "compiler_scope": "Generic word-primitive semantics/frame, data-layout preservation and checked input freshness; whole-program certificates only for the named layouts.",
        "compiler_endpoints": [name for name in AUDIT_DECLARATIONS if name.startswith("Witgen.Backends.Caliper.compile")],
        "writer_scope": "Generic writeRegs initializes the full register list, with exact cost and frame; fresh capacity, plus WellFormed for physical-memory triples.",
        "writer_endpoints": [name for name in AUDIT_DECLARATIONS if name.startswith("Witgen.Backends.CaliperWitness.")],
        "runtime_guide_endpoints": [name for name in AUDIT_DECLARATIONS if name.startswith("Witgen.Backends.CaliperRuntimeGuide.")],
        "memory_metric": "reserved_buffer_words",
        "register_metric": "static_ssa_exclusive_endpoint",
        "register_endpoint_proof": "Witgen.Backends.CaliperExamples.compiled_register_endpoints",
        "cost_models": "unit and cycles are abstract Caliper tables, not measured CPU cycles; costs include witness allocation and every push.",
        "rust_runtime_bound": False,
        "programs": programs,
        "trust_boundary": [
            "Lean kernel proofs with the explicit axiom whitelist; existing dependency olean caches are trusted build inputs.",
            "Caliper.run observations, Lean assembly/JSON serialization and Python arithmetic checks are executable validation, not extra universal theorems.",
            "Hashes bind local Lean/harness and Caliper sources; other dependencies are pinned by lake-manifest.json, not individually source-hashed here.",
            "No minimal-register allocation, combined register-plus-buffer footprint, or Rust/hardware runtime guarantee.",
        ],
    }


def run_all():
    """Build and execute Caliper, writing fresh evidence or raising on failure."""
    ART.mkdir(parents=True, exist_ok=True)
    # Never leave an earlier PASS receipt behind when this invocation fails.
    (ART / "verification.json").unlink(missing_ok=True)
    before_hashes = source_hashes()
    commands = []
    for command, log in [
        (["git", "-C", ".lake/packages/caliper", "rev-parse", "HEAD"], "caliper-revision.log"),
        (["git", "-C", ".lake/packages/caliper", "diff", "--exit-code", "HEAD", "--", "Caliper", "Caliper.lean", "lakefile.lean", "lean-toolchain"], "caliper-source-check.log"),
        (["lake", "env", "lean", "--version"], "lean-version.log"),
        (["lake", "build", "Witgen.Backends.CaliperRuntimeGuide"], "build.log"),
        (["lake", "env", "lean", "-DwarningAsError=true", "Witgen/Backends/CaliperCompilerTests.lean"], "compiler-tests.log"),
        (["lake", "env", "lean", "-DwarningAsError=true", "Witgen/Backends/CaliperTests.lean"], "interpreter-tests.log"),
        (["lake", "env", "lean", "-DwarningAsError=true", "Witgen/Backends/CaliperAudit.lean"], "axiom-audit.log"),
        (["lake", "env", "lean", "-DwarningAsError=true", "--run", "MainCaliper.lean", "export", "artifacts/caliper"], "export.log"),
    ]:
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=240)
        (ART / log).write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(f"{command!r} failed; see {ART / log}\n{result.stdout[-3000:]}\n{result.stderr[-3000:]}")
        commands.append({"argv": command, "log": log, "returncode": result.returncode})
    revision = (ART / "caliper-revision.log").read_text().strip()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    package = next(p for p in manifest["packages"] if p["name"] == "caliper")
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    requirement = next(p for p in config["require"] if p["name"] == "caliper")
    if not re.fullmatch(r"[0-9a-f]{40}", revision) or revision != package["rev"] or revision != requirement["rev"]:
        raise ValueError("Caliper checkout does not match the manifest/config pin")
    dependencies = check_axioms(
        (ART / "axiom-audit.log").read_text(), AUDIT_DECLARATIONS,
        allowed_axioms=CALIPER_ALLOWED_AXIOMS,
    )
    runtime = json.loads((ART / "runtime.json").read_text())
    validation = json.loads((ART / "validation.json").read_text())
    counts = validate_runtime(runtime, validation)
    for program in runtime["programs"]:
        if (ART / (program["name"] + ".caliper")).read_text() != program["assembly"] + "\n":
            raise ValueError("assembly file differs from runtime program export")
    hashes = source_hashes()
    if hashes != before_hashes:
        raise ValueError("source files changed during Caliper verification; rerun on a stable tree")
    artifact_names = [p["name"] + ".caliper" for p in runtime["programs"]]
    artifact_names += ["runtime.json", "validation.json"] + [c["log"] for c in commands]
    artifact_hashes = {name: hashlib.sha256((ART / name).read_bytes()).hexdigest()
                       for name in sorted(artifact_names)}
    report = {"status": "PASS", "finite_domain_cases": counts,
              "caliper_revision": revision, "lean_version": (ART / "lean-version.log").read_text().strip(),
              "source_hashes": hashes, "artifact_hashes": artifact_hashes, "scope": proof_scope(),
              "axiom_declaration_count": len(AUDIT_DECLARATIONS),
              "execution_mode": "lake env lean --run (no native Mathlib C compilation)",
              "validation_receipt": "validation.json", "commands": commands, "runtime_receipt": "runtime.json",
              "programs": [program["name"] for program in runtime["programs"]],
              "axiom_declarations": list(AUDIT_DECLARATIONS), "axioms": dependencies,
              "allowed_axioms": sorted(CALIPER_ALLOWED_AXIOMS)}
    (ART / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main():
    print(json.dumps(run_all(), indent=2))


if __name__ == "__main__":
    main()
