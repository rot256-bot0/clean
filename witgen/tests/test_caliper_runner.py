"""Caliper harness contract; run_all() is the parent run_demo integration seam."""

import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
ART = ROOT / "artifacts/caliper"
sys.path.insert(0, str(ROOT / "tools"))


class CaliperIntegrationTests(unittest.TestCase):
    def test_receipt_binds_source_artifacts_and_precise_proof_scope(self):
        import hashlib
        import run_caliper
        report = run_caliper.run_all()
        self.assertIn("source_hashes", report, "Python-generated source hashes are missing")
        for path in ("MainCaliper.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
                     "tools/run_caliper.py", "tools/axiom_audit.py",
                     "Witgen/Backends/Caliper.lean", "Witgen/Backends/CaliperWitness.lean",
                     "Witgen/Backends/CaliperExamples.lean", "Witgen/Backends/CaliperAudit.lean",
                     "Witgen/Backends/CaliperRuntimeGuide.lean",
                     ".lake/packages/caliper/Caliper/Render.lean"):
            self.assertIn(path, report["source_hashes"])
        for path, digest in report["source_hashes"].items():
            self.assertFalse(Path(path).is_absolute())
            self.assertEqual(digest, hashlib.sha256((ROOT / path).read_bytes()).hexdigest())
        for name in ("quadratic.caliper", "modMul.caliper", "fixedGated.caliper", "runtime.json",
                     "validation.json", "axiom-audit.log", "interpreter-tests.log", "compiler-tests.log"):
            self.assertEqual(report["artifact_hashes"][name],
                             hashlib.sha256((ART / name).read_bytes()).hexdigest())
        self.assertEqual(report["caliper_revision"], "b62f7c8be35df0aa728e5a6aac7bae85eef67449")
        self.assertEqual(report["axiom_declaration_count"], len(report["axiom_declarations"]))
        scope = report["scope"]
        self.assertFalse(scope["generic_compiler_preservation"])
        self.assertFalse(scope["rust_runtime_bound"])
        self.assertEqual(scope["memory_metric"], "reserved_buffer_words")
        self.assertEqual(scope["register_metric"], "static_ssa_exclusive_endpoint")
        self.assertEqual(scope["programs"]["fixedGated"]["circuit_endpoint"], None)
        self.assertEqual(scope["programs"]["fixedGated"]["rows"], 2)
        for name in ("quadratic", "modMul"):
            self.assertEqual(scope["programs"][name]["circuit_endpoint"],
                             "Witgen.Backends.CaliperExamples." + name + "_circuit_exec")
            self.assertTrue(scope["programs"][name]["circuit_assumptions"])
        for program in scope["programs"].values():
            for endpoint in program["endpoints"]:
                self.assertIn(endpoint, report["axiom_declarations"])

    def test_full_finite_domains_are_executed_and_checked_fail_closed(self):
        import copy
        import run_caliper
        report = run_caliper.run_all()
        self.assertIn("finite_domain_cases", report,
                      "full-domain Caliper.run observations and validation are missing")
        self.assertEqual(report["finite_domain_cases"], {
            "quadratic": {"inputs": 17 ** 2, "runs": 2 * 17 ** 2},
            "modMul": {"inputs": sum(n * n for n in range(1, 17)),
                       "runs": 2 * sum(n * n for n in range(1, 17))},
        })
        argv = [command["argv"] for command in report["commands"]]
        for path in ("Witgen/Backends/CaliperTests.lean", "Witgen/Backends/CaliperCompilerTests.lean"):
            self.assertIn(["lake", "env", "lean", "-DwarningAsError=true", path], argv)
        runtime = json.loads((ART / "runtime.json").read_text())
        validation = json.loads((ART / "validation.json").read_text())
        self.assertEqual(run_caliper.validate_runtime(runtime, validation), report["finite_domain_cases"])
        for mutation in ("no_programs", "missing_domain", "duplicate_case", "wrong_cell", "wrong_cost",
                         "wrong_register", "missing_sample", "wrong_output", "wrong_capacity"):
            bad = copy.deepcopy(runtime)
            bad_validation = copy.deepcopy(validation)
            program = bad["programs"][0]
            domain = bad_validation["programs"][0]
            if mutation == "no_programs":
                bad["programs"] = []
            elif mutation == "missing_domain":
                domain["runs"] = []
            elif mutation == "duplicate_case":
                domain["runs"].append(domain["runs"][0])
            elif mutation == "wrong_cell":
                domain["runs"][0]["cells"][2] += 1
            elif mutation == "wrong_cost":
                program["runs"][0]["time"] += 1
            elif mutation == "wrong_register":
                program["next_register"] += 1
            elif mutation == "missing_sample":
                program["runs"].pop()
            elif mutation == "wrong_output":
                program["runs"][0]["output_values"][0] += 1
            elif mutation == "wrong_capacity":
                program["runs"][0]["capacity"] += 1
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                run_caliper.validate_runtime(bad, bad_validation)

    def test_dedicated_audit_exact_coverage_with_explicit_choice(self):
        from axiom_audit import ALLOWED_AXIOMS, check_axioms
        import run_caliper
        self.assertTrue((ROOT / "Witgen/Backends/CaliperAudit.lean").is_file(),
                        "dedicated fully-qualified Caliper audit is missing")
        report = run_caliper.run_all()
        declarations = report["axiom_declarations"]
        self.assertEqual(declarations, list(run_caliper.AUDIT_DECLARATIONS))
        for name in [
            "Witgen.Backends.Caliper.compileWord_correct",
            "Witgen.Backends.Caliper.compileData_correct",
            "Witgen.Backends.Caliper.fixedGated_exec",
            "Witgen.Backends.CaliperWitness.writeRegs_exec",
            "Witgen.Backends.CaliperWitness.writeRegs_triple",
            "Witgen.Backends.CaliperExamples.quadratic_circuit_exec",
            "Witgen.Backends.CaliperExamples.modMul_circuit_exec",
            "Witgen.Backends.CaliperExamples.fixedGated_cycles_triple",
            "Witgen.Backends.CaliperRuntimeGuide.quadratic_runtime",
            "Witgen.Backends.CaliperRuntimeGuide.quadratic_exact_cost",
        ]:
            self.assertIn(name, declarations)
        self.assertTrue(all(name.startswith("Witgen.Backends.") for name in declarations))
        log = (ART / "axiom-audit.log").read_text()
        allowed = ALLOWED_AXIOMS | {"Classical.choice"}
        self.assertEqual(check_axioms(log, declarations, allowed_axioms=allowed), report["axioms"])
        self.assertIn("Classical.choice", report["axioms"])
        self.assertEqual(report["allowed_axioms"], sorted(allowed))
        for bad in ("", log + log, log.replace(declarations[0], "Unexpected.theorem"),
                    log.replace("Classical.choice", "sorryAx")):
            with self.subTest(bad=bad[:50]), self.assertRaises(ValueError):
                check_axioms(bad, declarations, allowed_axioms=allowed)
        with self.assertRaises(ValueError):
            check_axioms(log, declarations)
        self.assertEqual(ALLOWED_AXIOMS, {"propext", "Quot.sound"})

    def test_export_actual_assembly_and_run_receipts(self):
        result = subprocess.run(
            [sys.executable, "tools/run_caliper.py"], cwd=ROOT,
            text=True, capture_output=True, timeout=300,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads((ART / "verification.json").read_text())
        self.assertEqual(report["status"], "PASS")
        runtime = json.loads((ART / "runtime.json").read_text())
        self.assertEqual(runtime["interpreter"], "Caliper.run")
        self.assertEqual(runtime["renderer"], "Caliper.Stmt.renderString")
        programs = {p["name"]: p for p in runtime["programs"]}
        self.assertEqual(set(programs), {"quadratic", "modMul", "fixedGated"})
        layouts = {
            "quadratic": ([0, 1], [4, 7], 8),
            "modMul": ([0, 1, 2], [3, 4, 5], 6),
            "fixedGated": ([0, 1, 2, 3], [18, 19, 20, 21], 22),
        }
        for name, (inputs, outputs, end) in layouts.items():
            program = programs[name]
            self.assertEqual(program["input_registers"], inputs)
            self.assertEqual(program["output_registers"], outputs)
            self.assertEqual(program["next_register"], end)
            assembly = (ART / f"{name}.caliper").read_text()
            self.assertEqual(assembly, program["assembly"] + "\n")
            self.assertIn("mem.alloci b0,", assembly)
            self.assertEqual(assembly.count("mem.push"), len(inputs + outputs))
        self.assertIn("ifnz r0 {", programs["fixedGated"]["assembly"])
        self.assertIn("} else {", programs["fixedGated"]["assembly"])
        expected = {
            "quadratic": ([3, 5, 9, 14], {"unit": 14, "cycles": 90}),
            "modMul": ([7, 9, 11, 63, 5, 8], {"unit": 15, "cycles": 99}),
            "fixedGated/on": ([1, 3, 4, 5, 9, 14, 16, 4], {"unit": 33, "cycles": 186}),
            "fixedGated/off": ([0, 3, 4, 5, 0, 0, 0, 0], {"unit": 23, "cycles": 56}),
        }
        observed = [r for p in programs.values() for r in p["runs"]]
        self.assertEqual(len(observed), 8)
        self.assertEqual({(r["case"], r["cost_model"]) for r in observed},
                         {(case, cost) for case in expected for cost in ("unit", "cycles")})
        for row in observed:
            cells, costs = expected[row["case"]]
            self.assertEqual(row["cells"], cells)
            self.assertEqual(row["time"], costs[row["cost_model"]])
            self.assertEqual((row["net_words"], row["peak_words"], row["capacity"]),
                             (len(cells), len(cells), len(cells)))
            self.assertEqual(row["tape_position"], 0)
            self.assertEqual(row["input_values"], row["final_input_values"])


if __name__ == "__main__":
    unittest.main()
