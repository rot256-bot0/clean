import importlib.util
import json
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
QUAD = {
    "record": "QuadWitness",
    "fields": [
        {"name": "square", "type": "scalar"},
        {"name": "output", "type": "scalar"},
    ],
}


def quad_fixture():
    return {
        "version": 1,
        "name": "generate",
        "domain": "field17",
        "inputs": [{"name": "x", "type": "scalar"}, {"name": "y", "type": "scalar"}],
        "output": QUAD,
        "body": {
            "tag": "let",
            "op": "field.mul",
            "args": [0, 0],
            "regions": [],
            "result": "scalar",
            "next": {
                "tag": "let",
                "op": "field.add",
                "args": [0, 2],
                "regions": [],
                "result": "scalar",
                "next": {
                    "tag": "let",
                    "op": "record.make",
                    "args": [1, 0],
                    "regions": [],
                    "result": QUAD,
                    "next": {"tag": "ret", "ref": 0},
                },
            },
        },
    }


def lowered_quad_fixture(domain):
    prefix = {"nat": "nat", "word": "word"}[domain]
    body = {"tag": "ret", "ref": 0}
    for op, args, result, static in reversed(
        [
            ("mul", [0, 0], "scalar", {}),
            ("const", [], "scalar", {"value": "17"}),
            ("mod", [1, 0], "scalar", {}),
            ("add", [0, 4], "scalar", {}),
            ("mod", [0, 2], "scalar", {}),
            ("record.make", [2, 0], QUAD, {}),
        ]
    ):
        body = {
            "tag": "let",
            "op": op if "." in op else prefix + "." + op,
            "args": args,
            "regions": [],
            "result": result,
            "static": static,
            "next": body,
        }
    return {
        "version": 1,
        "name": "generate",
        "domain": domain,
        "inputs": [{"name": "x", "type": "scalar"}, {"name": "y", "type": "scalar"}],
        "output": QUAD,
        "body": body,
    }


class NativeEmitterTests(unittest.TestCase):
    def emitter(self):
        path = ROOT / "tools" / "emit_rust.py"
        self.assertTrue(path.is_file(), "Rust emitter is not implemented")
        spec = importlib.util.spec_from_file_location("emit_rust", path)
        assert spec is not None and spec.loader is not None
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module

    def test_record_quadratic_emits_and_executes(self):
        code = self.emitter().emit_module(quad_fixture())
        self.assertIn("struct QuadWitness", code)
        self.assertIn("witgen_native::f17_mul", code)
        self.assertIn("witgen_native::f17_add", code)
        path = ROOT / "backend" / "src" / "bin" / "emitter_smoke.rs"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            code
            + """\nfn main() {\n let r = generate(witgen_native::f17_from_u64(3).unwrap(), witgen_native::f17_from_u64(4).unwrap()).unwrap();\n println!("[{},{}]", witgen_native::f17_to_u64(r.square), witgen_native::f17_to_u64(r.output));\n}\n"""
        )
        result = subprocess.run(
            [
                "cargo",
                "run",
                "--quiet",
                "--locked",
                "--manifest-path",
                str(ROOT / "backend/Cargo.toml"),
                "--bin",
                "emitter_smoke",
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), [9, 13])

    def test_lowered_gmp_and_word_execute_the_same_quadratic(self):
        emitter = self.emitter()
        for domain in ["nat", "word"]:
            with self.subTest(domain=domain):
                try:
                    code = emitter.emit_module(lowered_quad_fixture(domain))
                except ValueError as error:
                    self.fail(f"required backend domain {domain} was rejected: {error}")
                self.assertNotIn("witgen_native::f17_mul", code)
                self.assertIn(
                    "witgen_native::" + ("nat_mul" if domain == "nat" else "word_mul"),
                    code,
                )
                args = (
                    "rug::Integer::from(3), rug::Integer::from(4)"
                    if domain == "nat"
                    else "3, 4"
                )
                path = ROOT / "backend/src/bin" / ("emitter_" + domain + ".rs")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(
                    code
                    + f'\nfn main() {{ let r = generate({args}).unwrap(); println!("[{{}},{{}}]", r.square, r.output); }}\n'
                )
                result = subprocess.run(
                    [
                        "cargo",
                        "run",
                        "--quiet",
                        "--locked",
                        "--manifest-path",
                        str(ROOT / "backend/Cargo.toml"),
                        "--bin",
                        "emitter_" + domain,
                    ],
                    cwd=ROOT,
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(json.loads(result.stdout), [9, 13])

    def test_branch_does_not_execute_untaken_division(self):
        emitter = self.emitter()
        bad = {
            "tag": "let",
            "op": "word.const",
            "args": [],
            "regions": [],
            "static": {"value": "0"},
            "result": "scalar",
            "next": {
                "tag": "let",
                "op": "word.div",
                "args": [1, 0],
                "regions": [],
                "result": "scalar",
                "next": {"tag": "ret", "ref": 0},
            },
        }
        module = {
            "version": 1,
            "name": "generate",
            "domain": "word",
            "inputs": [
                {"name": "flag", "type": "bool"},
                {"name": "x", "type": "scalar"},
            ],
            "output": "scalar",
            "body": {
                "tag": "let",
                "op": "control.branch",
                "args": [0, 1],
                "result": "scalar",
                "regions": [
                    {"inputs": ["scalar"], "output": "scalar", "body": bad},
                    {
                        "inputs": ["scalar"],
                        "output": "scalar",
                        "body": {"tag": "ret", "ref": 0},
                    },
                ],
                "next": {"tag": "ret", "ref": 0},
            },
        }
        try:
            code = emitter.emit_module(module)
        except ValueError as error:
            self.fail(f"branch support missing: {error}")
        self.assertIn("if flag", code)
        path = ROOT / "backend/src/bin/emitter_branch.rs"
        path.write_text(
            code
            + '\nfn main() { assert_eq!(generate(false, 7).unwrap(), 7); assert!(generate(true, 7).is_err()); println!("branch-ok"); }\n'
        )
        result = subprocess.run(
            [
                "cargo",
                "run",
                "--quiet",
                "--locked",
                "--manifest-path",
                str(ROOT / "backend/Cargo.toml"),
                "--bin",
                "emitter_branch",
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "branch-ok")

    def test_map_with_explicit_capture_executes(self):
        emitter = self.emitter()
        scalar_list = {"list": "scalar"}
        body = {
            "tag": "let",
            "op": "nat.mul",
            "args": [0, 1],
            "regions": [],
            "result": "scalar",
            "next": {"tag": "ret", "ref": 0},
        }
        module = {
            "version": 1,
            "name": "generate",
            "domain": "nat",
            "inputs": [
                {"name": "xs", "type": scalar_list},
                {"name": "factor", "type": "scalar"},
            ],
            "output": scalar_list,
            "body": {
                "tag": "let",
                "op": "control.map",
                "args": [0, 1],
                "result": scalar_list,
                "regions": [
                    {"inputs": ["scalar", "scalar"], "output": "scalar", "body": body}
                ],
                "next": {"tag": "ret", "ref": 0},
            },
        }
        try:
            code = emitter.emit_module(module)
        except ValueError as error:
            self.fail(f"map support missing: {error}")
        self.assertIn("for ", code)
        path = ROOT / "backend/src/bin/emitter_map.rs"
        path.write_text(
            code
            + '\nfn main() { let xs = vec![2,5,9].into_iter().map(rug::Integer::from).collect(); let r = generate(xs, rug::Integer::from(3)).unwrap(); println!("{}", serde_json::json!(r.iter().map(ToString::to_string).collect::<Vec<_>>())); }\n'
        )
        result = subprocess.run(
            [
                "cargo",
                "run",
                "--quiet",
                "--locked",
                "--manifest-path",
                str(ROOT / "backend/Cargo.toml"),
                "--bin",
                "emitter_map",
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), ["6", "15", "27"])

    def test_fold_builder_matches_map_including_empty(self):
        emitter = self.emitter()
        seq = {"list": "scalar"}
        body = {
            "tag": "let",
            "op": "nat.mul",
            "args": [0, 2],
            "regions": [],
            "result": "scalar",
            "next": {
                "tag": "let",
                "op": "list.push",
                "args": [2, 0],
                "regions": [],
                "result": seq,
                "next": {"tag": "ret", "ref": 0},
            },
        }
        module = {
            "version": 1,
            "name": "generate",
            "domain": "nat",
            "inputs": [
                {"name": "xs", "type": seq},
                {"name": "factor", "type": "scalar"},
            ],
            "output": seq,
            "body": {
                "tag": "let",
                "op": "list.empty",
                "args": [],
                "regions": [],
                "result": seq,
                "next": {
                    "tag": "let",
                    "op": "control.fold",
                    "args": [1, 0, 2],
                    "result": seq,
                    "regions": [
                        {
                            "inputs": ["scalar", seq, "scalar"],
                            "output": seq,
                            "body": body,
                        }
                    ],
                    "next": {"tag": "ret", "ref": 0},
                },
            },
        }
        try:
            code = emitter.emit_module(module)
        except ValueError as error:
            self.fail(f"fold/builder support missing: {error}")
        self.assertIn("for ", code)
        path = ROOT / "backend/src/bin/emitter_fold.rs"
        path.write_text(
            code
            + '\nfn main() { let xs = vec![2,5,9].into_iter().map(rug::Integer::from).collect(); let r = generate(xs, rug::Integer::from(3)).unwrap(); assert!(generate(vec![], rug::Integer::from(3)).unwrap().is_empty()); println!("{}", serde_json::json!(r.iter().map(ToString::to_string).collect::<Vec<_>>())); }\n'
        )
        result = subprocess.run(
            [
                "cargo",
                "run",
                "--quiet",
                "--locked",
                "--manifest-path",
                str(ROOT / "backend/Cargo.toml"),
                "--bin",
                "emitter_fold",
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), ["6", "15", "27"])

    def test_record_projection_and_scalar_equality(self):
        emitter = self.emitter()
        for domain, prefix in [("field17", "field"), ("nat", "nat"), ("word", "word")]:
            with self.subTest(domain=domain):
                term = {"tag": "ret", "ref": 0}
                for op, args, out, static in reversed(
                    [
                        (prefix + ".const", [], "scalar", {"value": "3"}),
                        ("record.make", [0, 0], QUAD, {}),
                        ("record.get", [0], "scalar", {"index": 1}),
                        (prefix + ".eq", [0, 2], "bool", {}),
                    ]
                ):
                    term = {
                        "tag": "let",
                        "op": op,
                        "args": args,
                        "regions": [],
                        "result": out,
                        "static": static,
                        "next": term,
                    }
                module = {
                    "version": 1,
                    "name": "generate",
                    "domain": domain,
                    "inputs": [],
                    "output": "bool",
                    "body": term,
                }
                try:
                    code = emitter.emit_module(module)
                except ValueError as error:
                    self.fail(f"projection/equality support missing: {error}")
                name = "emitter_projection_" + domain
                path = ROOT / "backend/src/bin" / (name + ".rs")
                path.write_text(
                    code
                    + '\nfn main() { assert!(generate().unwrap()); println!("projection-ok"); }\n'
                )
                result = subprocess.run(
                    [
                        "cargo",
                        "run",
                        "--quiet",
                        "--locked",
                        "--manifest-path",
                        str(ROOT / "backend/Cargo.toml"),
                        "--bin",
                        name,
                    ],
                    cwd=ROOT,
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), "projection-ok")

    def test_generated_writer_populates_reserved_cells_in_all_domains(self):
        emitter = self.emitter()
        for domain in ["field17", "nat", "word"]:
            with self.subTest(domain=domain):
                module = (
                    quad_fixture()
                    if domain == "field17"
                    else lowered_quad_fixture(domain)
                )
                module["wire_layout"] = {
                    "field": 17,
                    "cells": 4,
                    "input_slots": [0, 1],
                    "outputs": [
                        {"path": ["square"], "slot": 2},
                        {"path": ["output"], "slot": 3},
                    ],
                }
                code = emitter.emit_module(module)
                self.assertIn("pub fn populate", code, "writer not implemented")
                name = "emitter_writer_" + domain
                path = ROOT / "backend/src/bin" / (name + ".rs")
                path.write_text(
                    code
                    + '\nfn main() { let mut cells = [witgen_native::F17::from(3u64), witgen_native::F17::from(4u64), witgen_native::F17::from(0u64), witgen_native::F17::from(0u64)]; populate(&mut cells).unwrap(); println!("{}", serde_json::json!(cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>())); }\n'
                )
                result = subprocess.run(
                    [
                        "cargo",
                        "run",
                        "--quiet",
                        "--locked",
                        "--manifest-path",
                        str(ROOT / "backend/Cargo.toml"),
                        "--bin",
                        name,
                    ],
                    cwd=ROOT,
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(json.loads(result.stdout), [3, 4, 9, 13])

    def test_modmul_writer_uses_field257_and_checks_assumptions(self):
        emitter = self.emitter()
        rec = {
            "record": "ModMulWitness",
            "fields": [
                {"name": name, "type": "scalar"}
                for name in ["product", "quotient", "remainder"]
            ],
        }
        for domain in ["nat", "word"]:
            with self.subTest(domain=domain):
                term = {"tag": "ret", "ref": 0}
                for op, args, out in reversed(
                    [
                        (domain + ".mul", [0, 1], "scalar"),
                        (domain + ".div", [0, 3], "scalar"),
                        (domain + ".mod", [1, 4], "scalar"),
                        ("record.make", [2, 1, 0], rec),
                    ]
                ):
                    term = {
                        "tag": "let",
                        "op": op,
                        "args": args,
                        "regions": [],
                        "result": out,
                        "next": term,
                    }
                module = {
                    "version": 1,
                    "name": "generate",
                    "domain": domain,
                    "inputs": [
                        {"name": n, "type": "scalar"} for n in ["a", "b", "modulus"]
                    ],
                    "output": rec,
                    "body": term,
                    "wire_layout": {
                        "field": 257,
                        "cells": 6,
                        "input_slots": [0, 1, 2],
                        "policy": "modmul_small",
                        "outputs": [
                            {"path": [name], "slot": slot}
                            for name, slot in zip(
                                ["product", "quotient", "remainder"], [3, 4, 5]
                            )
                        ],
                    },
                }
                try:
                    code = emitter.emit_module(module)
                except ValueError as error:
                    self.fail(f"modmul witness writer support missing: {error}")
                name = "emitter_modmul_" + domain
                path = ROOT / "backend/src/bin" / (name + ".rs")
                path.write_text(
                    code
                    + '\nfn main() { let mut cells = [15u64,15,16,0,0,0].map(witgen_native::F257::from); populate(&mut cells).unwrap(); println!("{}", serde_json::json!(cells.into_iter().map(witgen_native::f257_to_u64).collect::<Vec<_>>())); let mut bad = [1u64,1,17,0,0,0].map(witgen_native::F257::from); let old=bad; assert!(populate(&mut bad).is_err()); assert_eq!(bad,old); }\n'
                )
                result = subprocess.run(
                    [
                        "cargo",
                        "run",
                        "--quiet",
                        "--locked",
                        "--manifest-path",
                        str(ROOT / "backend/Cargo.toml"),
                        "--bin",
                        name,
                    ],
                    cwd=ROOT,
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(json.loads(result.stdout), [15, 15, 16, 225, 14, 1])

    def test_static_literals_follow_field_and_word_semantics(self):
        emitter = self.emitter()
        for domain, prefix, literal, expected in [
            ("field17", "field", 34, 0),
            ("word", "word", 2**64 + 1, 1),
        ]:
            with self.subTest(domain=domain):
                module = {
                    "version": 1,
                    "name": "generate",
                    "domain": domain,
                    "inputs": [],
                    "output": "scalar",
                    "body": {
                        "tag": "let",
                        "op": prefix + ".const",
                        "args": [],
                        "regions": [],
                        "static": {"value": str(literal)},
                        "result": "scalar",
                        "next": {"tag": "ret", "ref": 0},
                    },
                }
                try:
                    code = emitter.emit_module(module)
                except ValueError as error:
                    self.fail(f"valid static literal was rejected: {error}")
                expression = (
                    "witgen_native::f17_to_u64(generate().unwrap())"
                    if domain == "field17"
                    else "generate().unwrap()"
                )
                name = "emitter_literal_" + domain
                (ROOT / "backend/src/bin" / (name + ".rs")).write_text(
                    code + f'\nfn main() {{ println!("{{}}", {expression}); }}\n'
                )
                result = subprocess.run(
                    [
                        "cargo",
                        "run",
                        "--quiet",
                        "--locked",
                        "--manifest-path",
                        str(ROOT / "backend/Cargo.toml"),
                        "--bin",
                        name,
                    ],
                    cwd=ROOT,
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(int(result.stdout), expected)

    def test_malformed_ir_is_rejected_before_rust_generation(self):
        import copy

        emitter = self.emitter()
        cases = []
        module = quad_fixture()
        module["version"] = True
        cases.append(module)
        module = quad_fixture()
        module["inputs"][0]["name"] = "_"
        cases.append(module)
        module = quad_fixture()
        module["body"]["arg_types"] = ["bool", "bool"]
        cases.append(module)
        module = quad_fixture()
        module["body"]["static"] = {"modulus": 19}
        cases.append(module)
        module = quad_fixture()
        module["body"]["args"] = [0, 999]
        cases.append(module)
        for module in cases:
            with self.subTest(module=module), self.assertRaises(ValueError):
                emitter.emit_module(copy.deepcopy(module))


if __name__ == "__main__":
    unittest.main()
