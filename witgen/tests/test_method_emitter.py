"""Tests of actual Lean v2 exports and the tested (not proved) Rust emitter.

Run: python3 -B -m unittest discover -s tests -p test_method_emitter.py -v
Fixtures must be real MainTyped/MainU64 exports under artifacts/methods.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXPORTS = ROOT / "artifacts" / "methods"
EMITTER = ROOT / "tools" / "emit_methods.py"
sys.dont_write_bytecode = True


def load_emitter():
    spec = importlib.util.spec_from_file_location("emit_methods", EMITTER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def exported(name):
    return json.loads((EXPORTS / (name + ".json")).read_text())


class MethodEmitterTests(unittest.TestCase):
    def test_00_missing_emitter_control_and_actual_nat_graph(self):
        self.assertTrue(EMITTER.is_file(), "v2 method emitter is missing")
        emitter = load_emitter()
        module = exported("nat")
        source = emitter.emit_module(module, "nat")
        self.assertEqual(len(re.findall(r"^fn method_\d+\(", source, re.M)), 3)
        for ordinal, method in enumerate(module["methods"]):
            self.assertIn("// method " + str(ordinal) + ": " + json.dumps(method["name"]), source)
            self.assertEqual(source.count(f"fn method_{ordinal}("), 1)
        square = source.split("fn method_2(", 1)[1].split("pub fn run(", 1)[0]
        self.assertIn("method_1(", square)
        self.assertNotIn(" % ", square)
        caller = source.split("pub fn run(", 1)[1].split("fn decode_", 1)[0]
        self.assertEqual(len(re.findall(r"method_\d+\(", caller)), 3)
        self.assertLess(len(caller.splitlines()), 12)
        self.assertIn("rug::Integer", source)
        self.assertIn(" % ", source)
        self.assertIn("typed::NatField::<2>(", source)
        self.assertNotIn("nat_mod(", source)

    def test_registry_and_field_negative_controls(self):
        self.assertTrue(EMITTER.is_file(), "v2 method emitter is missing")
        emitter = load_emitter()
        import copy
        def remove(m): m["methods"].pop()
        def duplicate(m): m["methods"].append(copy.deepcopy(m["methods"][0]))
        def forward(m): m["methods"][0]["body"] = copy.deepcopy(m["methods"][2]["body"])
        def wrong_name(m): m["body"]["static"]["name"] = m["methods"][0]["name"]
        def wrong_index(m): m["body"]["static"]["index"] = 1
        def missing(m): m["body"]["static"]["index"] = 3
        def signature(m): m["methods"][2]["args"].append(copy.deepcopy(m["methods"][2]["args"][0]))
        def bad_modulus(m): m["body"]["result"]["modulus"] = "17"
        def scalar_as_base(m): m["inputs"][0]["type"] = exported("mixed")["inputs"][2]["type"]
        for mutate in (remove, duplicate, forward, wrong_name, wrong_index, missing,
                       signature, bad_modulus, scalar_as_base):
            with self.subTest(control=mutate.__name__):
                m = exported("nat")
                mutate(m)
                with self.assertRaises(emitter.EmitError):
                    emitter.emit_module(m, "nat")
    def test_u64_shared_methods_loop_and_mode_admission(self):
        emitter = load_emitter()
        module = exported("u64")
        source = emitter.emit_module(module, "u64")
        self.assertEqual(len(re.findall(r"^fn method_\d+\(", source, re.M)), 12)
        self.assertEqual(source.count(".rev()"), 1)
        self.assertIn("0..256usize", source)
        self.assertIn("typed::adc(", source)
        self.assertIn("typed::sbb(", source)
        self.assertIn("typed::bit_at(", source)
        self.assertLess(len(source.splitlines()), 320)
        caller = source.split("pub fn run(", 1)[1].split("fn decode_", 1)[0]
        self.assertEqual(len(re.findall(r"method_\d+\(", caller)), 3)
        self.assertLess(len(caller.splitlines()), 12)
        arithmetic = source.split("fn method_0(", 1)[1].split("// method 3:", 1)[0]
        for forbidden in ("Integer", "nat_", "bn254_", "secp_", "field_modulus", " % "):
            self.assertNotIn(forbidden, arithmetic)
        square = source.split("fn method_2(", 1)[1].split("// method 3:", 1)[0]
        self.assertEqual(square.count("method_1("), 1)
        multiply = source.split("fn method_1(", 1)[1].split("// method 2:", 1)[0]
        self.assertEqual(multiply.count("method_0("), 2)
        for mode, fixture in (("nat", "u64"), ("u64", "nat"), ("u64", "mixed"),
                              ("nat", "affine"), ("native", "u64")):
            with self.subTest(mode=mode, fixture=fixture):
                with self.assertRaises(emitter.EmitError):
                    emitter.emit_module(exported(fixture), mode)
        for typ in ("nat", {"option": "nat"}, {"pair": ["bool", "nat"]}):
            m = {"version": 2, "name": "unbounded", "inputs": [{"name": "n", "type": typ}],
                 "output": typ, "methods": [], "body": {"tag": "ret", "ref": 0}}
            with self.assertRaises(emitter.EmitError):
                emitter.emit_module(m, "u64")

    def test_every_u64_node_and_region_metadata_is_checked(self):
        emitter = load_emitter()
        def nodes(value):
            if isinstance(value, dict):
                yield value
                for v in value.values(): yield from nodes(v)
            elif isinstance(value, list):
                for v in value: yield from nodes(v)
        original = exported("u64")
        self.assertIn("pub fn run(", emitter.emit_module(original, "u64"))
        import copy
        control_count = 0
        for index, node in enumerate(nodes(original)):
            mutations = []
            if node.get("tag") == "ret":
                mutations = [("ref", -1), ("ref", True), ("ref", 9999)]
            elif node.get("tag") == "let":
                mutations = [("arg_types", [] if node["arg_types"] else ["bool"]),
                             ("result", "bool" if node["result"] != "bool" else "word4"),
                             ("regions", [node] if not node["regions"] else [])]
                if node["args"]: mutations.append(("args", [9999] + node["args"][1:]))
            elif set(node) == {"inputs", "output", "body"}:
                mutations = [("inputs", ["word4"] * 5), ("output", "bool")]
            for key, bad in mutations:
                m = copy.deepcopy(original)
                list(nodes(m))[index][key] = bad
                with self.subTest(node=index, key=key):
                    with self.assertRaises(emitter.EmitError):
                        emitter.emit_module(m, "u64")
                control_count += 1
        self.assertGreater(control_count, 300)
    def test_symbols_preserve_names_without_lossy_collisions_or_injection(self):
        emitter = load_emitter()
        m = exported("nat")
        new_names = ["a-b", "a.b", 'quote"\\\n} fn injected() {} // ☃']
        mapping = {method["name"]: new_names[i] for i, method in enumerate(m["methods"])}
        def rename(value):
            if isinstance(value, dict):
                if value.get("name") in mapping: value["name"] = mapping[value["name"]]
                for v in value.values(): rename(v)
            elif isinstance(value, list):
                for v in value: rename(v)
        rename(m)
        source = emitter.emit_module(m, "nat")
        self.assertEqual(re.findall(r"^fn (method_\d+)\(", source, re.M), ["method_0", "method_1", "method_2"])
        self.assertNotIn("\n} fn injected", source)
        for i, original in enumerate(new_names):
            self.assertIn(f"// method {i}: {json.dumps(original)}\n", source)
        self.assertEqual(source, emitter.emit_module(m, "nat"))

    def test_caller_growth_does_not_duplicate_or_expand_methods(self):
        emitter = load_emitter()
        import copy
        for count in (1, 40):
            m = exported("u64")
            call = copy.deepcopy(m["body"])
            body = {"tag": "ret", "ref": 0}
            for _ in range(count):
                body = {**call, "next": body}
            m["body"] = body
            source = emitter.emit_module(m, "u64")
            self.assertEqual(len(re.findall(r"^fn method_\d+\(", source, re.M)), 12)
            caller = source.split("pub fn run(", 1)[1].split("fn decode_", 1)[0]
            self.assertEqual(len(re.findall(r"method_\d+\(", caller)), count)
            self.assertEqual(source.count(".rev()"), 1)
            self.assertLess(len(caller.splitlines()), count + 7)

    def test_static_metadata_and_schema_negative_controls(self):
        emitter = load_emitter()
        self.assertIn("pub fn run(", emitter.emit_module(exported("mixed"), "native"))
        m = exported("mixed")
        import copy
        mutations = [("version", True), ("version", 1), ("methods", None), ("inputs", {}),
                     ("output", {"field": True, "modulus": emitter.FIELD_MODULI[1]}),
                     ("output", {"field": 1, "modulus": "0" + emitter.FIELD_MODULI[1]}),
                     ("output", {"field": 1, "modulus": int(emitter.FIELD_MODULI[1])}),
                     ("output", {"point": "other"}), ("output", {"pair": ["bool"]})]
        for key, value in mutations:
            bad = copy.deepcopy(m)
            bad[key] = value
            with self.subTest(key=key, value=value):
                with self.assertRaises(emitter.EmitError): emitter.emit_module(bad, "native")
        for bad_static in ({"field": 1, "modulus": emitter.FIELD_MODULI[2]},
                           {"field": 2, "modulus": emitter.FIELD_MODULI[1]},
                           {"field": 2}, {"field": 2, "modulus": emitter.FIELD_MODULI[2], "extra": 0}):
            bad = copy.deepcopy(m)
            bad["body"]["static"] = bad_static
            with self.assertRaises(emitter.EmitError): emitter.emit_module(bad, "native")
        for op, static, result in (("u64.word", {"value": str(2**64)}, "u64"),
                                    ("u64.word", {"value": "01"}, "u64"),
                                    ("u64.flag", {"value": 1}, "bool"),
                                    ("u64.literal", {"limbs": ["0"] * 3}, "word4")):
            with self.assertRaises(emitter.EmitError):
                emitter.emit_module(primitive_module(op, [], result, static), "u64")

    def test_unbounded_nat_static_literal_is_not_a_python_machine_integer(self):
        emitter = load_emitter()
        m = exported("nat")
        m["body"]["next"]["next"]["static"]["value"] = "1" + "0" * 5000
        self.assertIn('"1' + "0" * 5000 + '"', emitter.emit_module(m, "nat"))

    def test_actual_bundle_keeps_one_registry_for_all_nine_callers(self):
        emitter = load_emitter()
        module = exported("u64-shared")
        source = emitter.emit_module(module, "u64")
        self.assertEqual(len(re.findall(r"^fn method_\d+\(", source, re.M)), 12)
        self.assertEqual(len(re.findall(r"^pub fn program_\d+\(", source, re.M)), 9)
        self.assertEqual(source.count(".rev()"), 1)
        for ordinal in range(9):
            caller = source.split(f"pub fn program_{ordinal}(", 1)[1].split("fn program_", 1)[0]
            self.assertEqual(len(re.findall(r"method_\d+\(", caller)), 1)
        with self.assertRaises(emitter.EmitError): emitter.emit_module(module, "native")

    def test_native_exports_affine_bind_and_json_seam(self):
        emitter = load_emitter()
        for fixture in ("mixed", "affine", "from-affine"):
            with self.subTest(fixture=fixture):
                source = emitter.emit_module(exported(fixture), "native")
                self.assertIn("pub fn run_json(", source)
                self.assertIn("witgen_native::Result<", source)
                self.assertNotIn("NatField", source)
                self.assertNotIn("WordField", source)
        mixed = emitter.emit_module(exported("mixed"), "native")
        for helper in ("secp_scalar_square", "secp_scalar_mul", "secp_scalar_add",
                       "secp_base_square", "secp_base_mul", "secp_base_add",
                       "point_generator", "point_scale", "point_inv", "point_add", "point_x"):
            self.assertIn("typed::" + helper + "(", mixed)
        affine = emitter.emit_module(exported("affine"), "native")
        self.assertIn("typed::to_affine(", affine)
        self.assertIn("typed::from_affine(", affine)
        self.assertIn("match ", affine)
        self.assertIn("None => None", affine)
        self.assertIn("Option<typed::SecpPoint>", affine)
        for mode in ("nat", "u64"):
            source = emitter.emit_module(exported(mode), mode)
            self.assertIn(f"typed::parse_{mode if mode == 'nat' else 'word'}_field::<2>", source)
            self.assertIn("pub fn run_json(", source)

    def test_structural_types_are_generic_and_closed(self):
        emitter = load_emitter()
        for mode in ("native", "nat", "u64"):
            typ = {"pair": ["bool", {"option": "word4"}]}
            m = {"version": 2, "name": "structural", "inputs": [{"name": "x", "type": typ}],
                 "methods": [], "output": typ, "body": {"tag": "ret", "ref": 0}}
            self.assertIn("(bool, Option<typed::Word4>)", emitter.emit_module(m, mode))
            bad = {"pair": ["bool", {"option": {"point": "secp256k1"}}]}
            m["inputs"][0]["type"] = m["output"] = bad
            if mode != "native":
                with self.assertRaises(emitter.EmitError): emitter.emit_module(m, mode)
        m = exported("affine")
        # A bind region's single formal pair is not allowed to capture its parent.
        region = m["body"]["next"]["next"]["regions"][0]
        region["body"]["args"] = [1]
        with self.assertRaises(emitter.EmitError): emitter.emit_module(m, "native")

def primitive_module(op, arg_types, result, static=None, regions=None):
    """Supplemental primitive probes, never substitutes for exported libraries."""
    return {"version": 2, "name": op, "methods": [],
            "inputs": [{"name": f"input{i}", "type": t} for i, t in enumerate(arg_types)],
            "output": result, "body": {
                "tag": "let", "op": op, "args": list(range(len(arg_types))),
                "arg_types": arg_types, "result": result, "static": {} if static is None else static,
                "regions": [] if regions is None else regions, "next": {"tag": "ret", "ref": 0}}}


def supplemental_modules():
    fields = [{"field": i, "modulus": p} for i, p in enumerate(load_emitter().FIELD_MODULI)]
    point = {"point": "secp256k1"}
    word_option = {"option": "word4"}
    pair = {"pair": ["bool", "u64"]}
    some = primitive_module("option.some", ["word4"], word_option)["body"]
    result = {
        "raw-nat-pack": (primitive_module("nat.field.pack", ["nat"], fields[0], {"field": 0}), "nat"),
        "raw-u64-pack": (primitive_module("u64.fromWord", ["word4"], fields[0], {"field": 0}), "u64"),
        "raw-u64-unpack": (primitive_module("u64.toWord", [fields[0]], "word4", {"field": 0}), "u64"),
        "nat-mod-zero": (primitive_module("nat.mod", ["nat"], "nat", {"modulus": "0"}), "nat"),
        "word-max": (primitive_module("u64.word", [], "u64", {"value": str(2**64 - 1)}), "u64"),
        "bool-true": (primitive_module("u64.flag", [], "bool", {"value": True}), "u64"),
        "pair": (primitive_module("value.pair", ["bool", "u64"], pair), "native"),
        "fst": (primitive_module("value.fst", [pair], "bool"), "native"),
        "snd": (primitive_module("value.snd", [pair], "u64"), "native"),
        "some": (primitive_module("option.some", ["word4"], word_option), "native"),
        "none": (primitive_module("option.none", [], word_option), "native"),
        "bind": (primitive_module("option.bind", [word_option], word_option, regions=[{
            "inputs": ["word4"], "output": word_option, "body": some}]), "native"),
        "to-affine": (primitive_module("curve.toAffine", [point], {"option": {"pair": [fields[1], fields[1]]}}, {"curve": "secp256k1"}), "native"),
        "point-identity": (primitive_module("secp.identity", [], point, {"curve": "secp256k1"}), "native"),
        "point-x": (primitive_module("secp.x", [point], fields[1], {"curve": "secp256k1"}), "native"),
        "bn254-square": (primitive_module("field.square", [fields[0]], fields[0], fields[0]), "native"),
    }
    for i, field in enumerate(fields):
        result[f"native-const-{i}"] = (primitive_module("field.const", [], field,
            {**field, "value": str(int(field["modulus"]) + 17)}), "native")
    return result


def nested_option_modules():
    """Accepted structural IR: constructors and identity across the JSON seam."""
    opt = {"option": "bool"}
    nested = {"option": opt}
    pair = {"pair": ["bool", nested]}
    def identity(ty):
        return {"version": 2, "name": "identity", "methods": [],
                "inputs": [{"name": "x", "type": ty}], "output": ty,
                "body": {"tag": "ret", "ref": 0}}
    result = {}
    for mode in ("native", "nat", "u64"):
        probes = {
            "none": primitive_module("option.none", [], nested),
            "some": primitive_module("option.some", [opt], nested),
            "identity": identity(nested),
            "pair": identity(pair),
            "option-pair": identity({"option": pair}),
            "triple": identity({"option": nested}),
        }
        result.update({f"nested-{mode}-{name}": (module, mode) for name, module in probes.items()})
    return result


def compile_modules(named_modules, checks=""):
    """Test-only binary; all generated source/build files stay in ignored paths."""
    import os
    import subprocess
    emitter = load_emitter()
    directory = EXPORTS / "emitter-test-src"
    directory.mkdir(parents=True, exist_ok=True)
    bin_name = f"emitter_methods_test_{os.getpid()}"
    bin_path = ROOT / "backend" / "src" / "bin" / (bin_name + ".rs")
    ignored = subprocess.run(["git", "check-ignore", "--quiet", str(bin_path)], cwd=ROOT)
    if ignored.returncode != 0:
        raise AssertionError("temporary emitter_methods_*.rs binary must be ignored before testing")
    declarations, cases = [], []
    for i, (label, (module, mode)) in enumerate(named_modules.items()):
        path = directory / f"module_{i}.rs"
        path.write_text(emitter.emit_module(module, mode))
        declarations.append(f'#[allow(dead_code)]\nmod module_{i} {{ include!({json.dumps(str(path))}); }}')
        if module.get("kind") == "u64-shared-library":
            for j, program in enumerate(module["programs"]):
                cases.append(f'{json.dumps(program["name"])} => module_{i}::run_json({j}, inputs),')
        else:
            cases.append(f'{json.dumps(label)} => module_{i}::run_json(inputs),')
    runner = '''
use std::io::{self, BufRead};
fn execute(value: &serde_json::Value) -> witgen_native::Result<serde_json::Value> {
    let program = value["program"].as_str().ok_or(witgen_native::Error::InvalidInputType { expected: "program string" })?;
    let inputs = value["inputs"].as_array().ok_or(witgen_native::Error::InvalidInputType { expected: "input array" })?;
    match program {
''' + "\n".join(cases) + '''
        _ => Err(witgen_native::Error::UnknownProgram(program.to_owned())),
    }
}
fn main() {
    for line in io::stdin().lock().lines() {
        let result = line.map_err(witgen_native::Error::from)
            .and_then(|text| serde_json::from_str(&text).map_err(witgen_native::Error::from))
            .and_then(|value| execute(&value));
        let output = match result {
            Ok(value) => serde_json::json!({"ok": value}),
            Err(error) => serde_json::json!({"error": error.code(), "message": error.to_string()}),
        };
        println!("{}", output);
    }
}
'''
    runner = runner.replace("fn main() {", "fn main() {\n" + checks, 1)
    bin_path.write_text("\n".join(declarations) + runner)
    target = EXPORTS / "cargo-target"
    env = dict(os.environ, CARGO_TARGET_DIR=str(target))
    try:
        built = subprocess.run(["cargo", "build", "--offline", "--locked", "--bin", bin_name],
                               cwd=ROOT / "backend", env=env, capture_output=True, text=True, timeout=180)
        (directory / "build.log").write_text(built.stdout + built.stderr)
        if built.returncode:
            raise AssertionError("actual Rust compilation failed:\n" + built.stdout + built.stderr)
    finally:
        bin_path.unlink(missing_ok=True)
    return target / "debug" / bin_name


def fresh_lean_bit_controls():
    """Compile the real local import closure; never trust stale project oleans."""
    import os
    import subprocess
    import tempfile
    order, seen = [], set()
    def visit(module):
        if module in seen:
            return
        seen.add(module)
        source = ROOT / (module.replace(".", "/") + ".lean")
        for line in source.read_text().splitlines():
            if line.startswith("import "):
                for dep in line.removeprefix("import ").split():
                    if dep.startswith("Witgen."):
                        visit(dep)
                    elif dep.split(".")[0] not in {"Std", "Lean", "Init"}:
                        raise AssertionError(f"unexpected external dependency: {dep}")
        order.append((module, source))
    visit("Witgen.U64.BitAtTests")
    with tempfile.TemporaryDirectory(prefix="witgen-bit-domain-") as build:
        env = dict(os.environ, LEAN_PATH=build)
        for module, source in order:
            target = Path(build) / (module.replace(".", "/") + ".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            result = subprocess.run(["lean", "-DwarningAsError=true", "-o", str(target), str(source)],
                                    cwd=ROOT, env=env, capture_output=True, text=True, timeout=90)
            if result.returncode:
                raise AssertionError(f"{module}:\n{result.stdout}{result.stderr}")
        result = subprocess.run(["lean", "--run", "Witgen/U64/BitAtTests.lean"],
                                cwd=ROOT, env=env, capture_output=True, text=True, timeout=90)
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)
    report = json.loads(result.stdout)
    EXPORTS.mkdir(parents=True, exist_ok=True)
    (EXPORTS / "bit-at-controls.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


class BitAtExecutionTests(unittest.TestCase):
    def test_actual_lean_repeat257_and_indices256_257_match_rust(self):
        import subprocess
        report = fresh_lean_bit_controls()
        modules = {m["name"]: (m, "u64") for m in report["programs"]}
        self.assertEqual(set(modules), {"bit-domain-257", "bit-domain-258"})
        for count, module in zip((257, 258), report["programs"]):
            self.assertEqual(module["body"]["next"]["static"]["count"], count)
            self.assertIn(f"0..{count}usize", load_emitter().emit_module(module, "u64"))
        # Direct real runtime primitive controls supplement, not replace, the IR runs.
        checks = []
        for row in report["bit_cases"]:
            i = int(row["index"])
            expected = bool((sum(int(w) << (64*j) for j, w in enumerate(row["word"])) >> i) & 1)
            self.assertEqual(row["expected"], expected)
            if i < 2**64:
                word = "[" + ",".join(w + "u64" for w in row["word"]) + "]"
                checks.append(f"assert_eq!(witgen_native::typed::bit_at({word}, {i}usize), {str(expected).lower()});")
        binary = compile_modules(modules, "\n".join(checks))
        rows = [{"program": r["program"], "inputs": r["inputs"]} for r in report["cases"]]
        result = subprocess.run([str(binary)], input="\n".join(map(json.dumps, rows)) + "\n",
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        outputs = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(outputs), len(rows))
        self.assertEqual(len(rows), 6)
        for row, output in zip(report["cases"], outputs):
            with self.subTest(program=row["program"], inputs=row["inputs"]):
                self.assertEqual(output, {"ok": row["expected"]})
                self.assertEqual(output, {"ok": row["actual"]})
        for row in report["bit_cases"]:
            with self.subTest(index=row["index"], word=row["word"]):
                self.assertEqual(row["actual"], row["expected"])


class RustExecutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not (ROOT / "backend" / "src" / "typed.rs").is_file():
            raise unittest.SkipTest("parent typed runtime not installed")
        modules = {name: (exported(name), mode) for name, mode in
                   (("nat", "nat"), ("u64", "u64"), ("mixed", "native"),
                    ("affine", "native"), ("from-affine", "native"), ("u64-shared", "u64"))}
        modules.update(supplemental_modules())
        modules.update(nested_option_modules())
        cls.binary = compile_modules(modules)

    def cases(self, rows):
        import subprocess
        result = subprocess.run([str(self.binary)], input="\n".join(json.dumps(row) for row in rows) + "\n",
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        outputs = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(outputs), len(rows))
        return outputs

    def test_real_nat_u64_caller_arithmetic_is_raw(self):
        p = int(load_emitter().FIELD_MODULI[2])
        pairs = [(0, 0), (3, 4), (p - 1, p - 1), (2**192 + 7, 2**193 + 11), (2**255, 2**255)]
        rows = [{"program": mode, "inputs": [str(a), str(b)]} for mode in ("nat", "u64") for a, b in pairs]
        outputs = self.cases(rows)
        expected = [{"ok": str((a*a*b + 5) % p)} for mode in ("nat", "u64") for a, b in pairs]
        self.assertEqual(outputs, expected)

    def test_generated_imports_are_warning_clean(self):
        log = (EXPORTS / "emitter-test-src" / "build.log").read_text()
        self.assertNotIn("warning:", log)

    def test_all_exported_u64_fixtures_against_python_raw_integers(self):
        report = exported("u64-tests")
        fixtures = report["fixtures"]
        self.assertEqual(len(fixtures), report["field_caller_checks"])
        outputs = self.cases([{"program": f["program"], "inputs": f["inputs"]} for f in fixtures])
        receipt = []
        for fixture, output in zip(fixtures, outputs):
            p = int(fixture["modulus"])
            a, *rest = map(int, fixture["inputs"])
            op = fixture["program"].split(".")[-1]
            raw = (a + rest[0]) if op == "add" else (a * rest[0]) if op == "mul" else a * a
            expected = str(raw % p)
            self.assertEqual(output, {"ok": expected}, fixture)
            self.assertEqual(fixture["expected"], expected)
            self.assertEqual(fixture["actual"], expected)
            self.assertLess(int(output["ok"]), p)
            receipt.append({"program": fixture["program"], "inputs": fixture["inputs"], "raw_result": output["ok"]})
        (EXPORTS / "emitter-test-src" / "fixture-results.json").write_text(json.dumps(receipt, indent=2) + "\n")

    def test_pack_and_unpack_never_hide_normalization(self):
        p = int(load_emitter().FIELD_MODULI[0])
        maximum = str(2**64 - 1)
        huge = "1" + "0" * 6000
        rows = [{"program": "raw-nat-pack", "inputs": [huge]},
                {"program": "raw-nat-pack", "inputs": [str(p + 1)]},
                {"program": "raw-u64-pack", "inputs": [[maximum] * 4]},
                {"program": "raw-u64-unpack", "inputs": [str(p - 1)]},
                {"program": "nat-mod-zero", "inputs": [huge]},
                {"program": "word-max", "inputs": []},
                {"program": "bool-true", "inputs": []}]
        self.assertEqual(self.cases(rows), [{"ok": huge}, {"ok": str(p + 1)}, {"ok": str(2**256 - 1)},
            {"ok": [str(((p - 1) >> (64*i)) & (2**64 - 1)) for i in range(4)]},
            {"ok": huge}, {"ok": maximum}, {"ok": True}])

    def test_nested_option_output_encoding_is_injective(self):
        rows, expected = [], []
        for mode in ("native", "nat", "u64"):
            for op, inputs, value in (("none", [], None), ("some", [None], {"some": None}),
                                      ("some", [False], {"some": False}),
                                      ("some", [True], {"some": True})):
                rows.append({"program": f"nested-{mode}-{op}", "inputs": inputs})
                expected.append({"ok": value})
        outputs = self.cases(rows)
        self.assertEqual(outputs, expected)
        # Raw JSON shapes are compared exactly; no null/tag normalization.
        self.assertEqual(len({json.dumps(o, sort_keys=True) for o in outputs}), 4)

    def test_nested_option_input_roundtrips_strictly(self):
        values = [None, {"some": None}, {"some": False}, {"some": True}]
        triples = [None, {"some": None}] + [{"some": v} for v in values[1:]]
        rows, expected = [], []
        for mode in ("native", "nat", "u64"):
            for op, data in (("identity", values), ("pair", [[True, v] for v in values]),
                             ("option-pair", [None] + [[False, v] for v in values]),
                             ("triple", triples)):
                for value in data:
                    rows.append({"program": f"nested-{mode}-{op}", "inputs": [value]})
                    expected.append({"ok": value})
        outputs = self.cases(rows)
        self.assertEqual(outputs, expected)
        # Feed the actual encoded results back through the emitted decoders.
        replay = [{**row, "inputs": [out["ok"]]} for row, out in zip(rows, outputs)]
        self.assertEqual(self.cases(replay), outputs)

    def test_nested_option_invalid_tags_rejected(self):
        invalid = [False, True, "true", 0, [], {}, {"Some": None}, {"none": True},
                   {"some": None, "extra": 0}, {"some": "true"}, {"some": []},
                   {"some": {"some": None}}]
        negatives = []
        for mode in ("native", "nat", "u64"):
            for bad in invalid:
                for op, value in (("identity", bad), ("pair", [True, bad]),
                                  ("option-pair", [False, bad])):
                    negatives.append({"program": f"nested-{mode}-{op}", "inputs": [value]})
            for bad in ({"some": True}, {"some": {}}, {"some": {"some": None, "extra": 0}}):
                negatives.append({"program": f"nested-{mode}-triple", "inputs": [bad]})
            # Option<Pair> is still an untagged array, even with nullable fields.
            negatives.append({"program": f"nested-{mode}-option-pair",
                              "inputs": [{"some": [True, None]}]})
        errors = self.cases(negatives)
        self.assertEqual([r.get("error") for r in errors], ["invalid_input_type"] * len(negatives))

    def test_generic_structural_operations_execute(self):
        word = ["1", "2", "3", "4"]
        data = [("pair", [True, "17"], [True, "17"]), ("fst", [[False, "8"]], False),
                ("snd", [[False, "8"]], "8"), ("some", [word], word), ("none", [], None),
                ("bind", [word], word), ("bind", [None], None)]
        self.assertEqual(self.cases([{"program": n, "inputs": a} for n, a, _ in data]),
                         [{"ok": result} for _, _, result in data])
        errors = self.cases([{"program": "some", "inputs": [["0", "0"]]},
                             {"program": "some", "inputs": [[str(2**64), "0", "0", "0"]]},
                             {"program": "fst", "inputs": [["true", "8"]]}])
        self.assertEqual([o["error"] for o in errors], ["input_length", "word_overflow", "invalid_input_type"])

    def test_native_fields_and_identity_points_execute(self):
        p = int(load_emitter().FIELD_MODULI[0])
        data = [(f"native-const-{i}", [], "17") for i in range(3)]
        data += [("bn254-square", [str(p - 1)], "1"), ("point-identity", [], "00"),
                 ("to-affine", ["00"], None), ("point-x", ["00"], "0")]
        self.assertEqual(self.cases([{"program": n, "inputs": a} for n, a, _ in data]),
                         [{"ok": result} for _, _, result in data])

    def test_mixed_actual_secp_program_against_independent_group_math(self):
        p, n = map(int, load_emitter().FIELD_MODULI[1:])
        g = (int("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798", 16),
             int("483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8", 16))
        def add(a, b):
            if a is None: return b
            if b is None: return a
            x, y = a
            u, v = b
            if x == u and (y + v) % p == 0: return None
            slope = (3*x*x * pow(2*y, -1, p) if a == b else (v-y) * pow(u-x, -1, p)) % p
            xx = (slope*slope - x - u) % p
            return (xx, (slope*(x-xx)-y) % p)
        def scale(k):
            answer, base = None, g
            while k:
                if k & 1: answer = add(answer, base)
                base = add(base, base)
                k >>= 1
            return answer
        triples = [(1, 1, 3), (0, 0, 5), (1, 0, 9), (3, 4, p-1), (n-1, n-1, 2**192+1)]
        outputs = self.cases([{"program": "mixed", "inputs": list(map(str, triple))} for triple in triples])
        expected = []
        for s, t, b in triples:
            k = (s*s*t+s) % n
            q = add(scale(k), (g[0], -g[1] % p))
            expected.append({"ok": str((b*b*(0 if q is None else q[0])+g[0]) % p)})
        self.assertEqual(outputs, expected)

    def test_real_optional_affine_and_boundary_errors(self):
        scalar = load_emitter().FIELD_MODULI[2]
        rows = [{"program": "affine", "inputs": []},
                {"program": "from-affine", "inputs": [["0", "0"]]},
                {"program": "from-affine", "inputs": [["0"]]},
                {"program": "nat", "inputs": [scalar, "0"]},
                {"program": "u64", "inputs": [scalar, "0"]},
                {"program": "nat", "inputs": ["-1", "0"]},
                {"program": "u64", "inputs": [True, "0"]},
                {"program": "u64", "inputs": []}]
        outputs = self.cases(rows)
        self.assertEqual(outputs[0], {"ok": "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"})
        self.assertEqual(outputs[1], {"ok": None})
        self.assertEqual([row["error"] for row in outputs[2:]],
                         ["input_length", "noncanonical_field", "noncanonical_field", "negative_natural", "invalid_input_type", "input_arity"])


if __name__ == "__main__":
    unittest.main()
