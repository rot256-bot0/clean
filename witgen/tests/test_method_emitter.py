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
        def scalar_as_base(m): m["inputs"][0]["type"] = {"field": 1, "modulus": emitter.FIELD_MODULI[1]}
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
                       "point_generator", "point_mul", "point_inv", "point_add", "to_affine"):
            self.assertIn("typed::" + helper + "(", mixed)
        affine = emitter.emit_module(exported("affine"), "native")
        self.assertIn("typed::to_affine(", affine)
        self.assertIn("typed::from_affine(", affine)
        self.assertIn("match ", affine)
        self.assertRegex(affine, r"None => \{\s+let \w+: Option<typed::SecpPoint> = None::<typed::SecpPoint>;")
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
            bad = {"pair": ["bool", {"option": {"point": curve_descriptor()}}]}
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
    curve = curve_descriptor()
    point = {"point": curve}
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
        "to-affine": (primitive_module("curve.toAffine", [point], {"option": {"pair": [fields[1], fields[1]]}}, {"curve": curve}), "native"),
        "point-identity": (primitive_module("curve.identity", [], point, {"curve": curve}), "native"),
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
    target = os.environ.get("CARGO_TARGET_DIR", str(EXPORTS / "cargo-target"))
    env = dict(os.environ, CARGO_TARGET_DIR=str(target))
    try:
        built = subprocess.run(["cargo", "build", "--offline", "--locked", "--bin", bin_name,
                                "--message-format=json-render-diagnostics"],
                               cwd=ROOT / "backend", env=env, capture_output=True, text=True, timeout=180)
        (directory / "build.log").write_text(built.stdout + built.stderr)
        if built.returncode:
            raise AssertionError("actual Rust compilation failed:\n" + built.stdout + built.stderr)
        artifacts = [event for line in built.stdout.splitlines() if
                     (event := json.loads(line)).get("reason") == "compiler-artifact"
                     and event.get("target", {}).get("name") == bin_name
                     and "bin" in event["target"].get("kind", []) and event.get("executable")]
        if len(artifacts) != 1:
            raise AssertionError("expected exactly one Cargo emitter-test executable")
        binary = Path(artifacts[0]["executable"])
    finally:
        bin_path.unlink(missing_ok=True)
    return binary


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
                    elif dep.split(".")[0] not in {"Std", "Lean", "Init", "Mathlib"}:
                        raise AssertionError(f"unexpected external dependency: {dep}")
        order.append((module, source))
    visit("Witgen.U64.BitAtTests")
    # Field inversion adds pinned Mathlib primality dependencies. Preserve the
    # fresh local closure rather than falling back to potentially stale Witgen
    # oleans; only Lake's dependency paths may supplement the isolated build.
    configured = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT,
                                capture_output=True, text=True, timeout=60, check=True)
    local_cache = (ROOT / ".lake/build/lib/lean").resolve()
    external = [path for path in configured.stdout.strip().split(os.pathsep)
                if path and Path(path).resolve() != local_cache]
    if any((Path(path) / "Witgen").exists() for path in external):
        raise AssertionError("dependency path unexpectedly contains local Witgen oleans")
    before = {source: source.read_bytes() for _, source in order}
    with tempfile.TemporaryDirectory(prefix="witgen-bit-domain-") as build:
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([build] + external))
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
    if before != {source: source.read_bytes() for _, source in order}:
        raise AssertionError("local Lean sources changed during fresh bit controls")
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
                 ("to-affine", ["00"], None)]
        self.assertEqual(self.cases([{"program": n, "inputs": a} for n, a, _ in data]),
                         [{"ok": result} for _, _, result in data])

    def test_mixed_actual_secp_program_against_independent_group_math(self):
        p, n = map(int, load_emitter().FIELD_MODULI[1:])
        pairs = [(1, 1), (0, 0), (1, 0), (3, 4), (n-1, n-1), (2**200+7, 2**129+9)]
        outputs = self.cases([{"program": "mixed", "inputs": list(map(str, pair))} for pair in pairs])
        expected = []
        minus_g = (SECP_G[0], -SECP_G[1] % p)
        for s, t in pairs:
            k = (s*s*t+s) % n
            q = secp_add_oracle(secp_mul_oracle(k, SECP_G), minus_g)
            expected.append({"ok": None if q is None else str((q[0]*q[0]*q[1]+q[0]) % p)})
        self.assertEqual(outputs, expected)
        self.assertEqual(outputs[pairs.index((1, 0))], {"ok": None})

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


def curve_descriptor():
    fields = [{"field": i, "modulus": p} for i, p in enumerate(load_emitter().FIELD_MODULI)]
    return {"id": "secp256k1", "base": fields[1], "scalar": fields[2], "weierstrass": ["0", "0", "0", "0", "7"]}


def identity_module(ty):
    return {"version": 2, "name": "identity", "methods": [],
            "inputs": [{"name": "x", "type": ty}], "output": ty,
            "body": {"tag": "ret", "ref": 0}}


SECP_BASE_MODULUS = int(load_emitter().FIELD_MODULI[1])


def secp_add_oracle(a, b):
    p = SECP_BASE_MODULUS
    if a is None: return b
    if b is None: return a
    x, y = a
    u, v = b
    if x == u and (y + v) % p == 0: return None
    slope = (3*x*x * pow(2*y, -1, p) if a == b else (v-y) * pow(u-x, -1, p)) % p
    xx = (slope*slope - x - u) % p
    return xx, (slope*(x-xx)-y) % p


def secp_mul_oracle(k, point):
    answer = None
    while k:
        if k & 1: answer = secp_add_oracle(answer, point)
        point = secp_add_oracle(point, point)
        k >>= 1
    return answer


def secp_hex_oracle(point):
    return "00" if point is None else f"{2 + (point[1] & 1):02x}{point[0]:064x}"


SECP_G = (int("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798", 16),
          int("483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8", 16))


def run_curve_cases(test, binary, rows):
    import subprocess
    result = subprocess.run([str(binary)],
        input="\n".join(json.dumps(row) for row in rows) + "\n",
        capture_output=True, text=True, timeout=60)
    test.assertEqual(result.returncode, 0, result.stderr)
    test.assertNotIn("panicked", result.stderr)
    outputs = [json.loads(line) for line in result.stdout.splitlines()]
    test.assertEqual(len(outputs), len(rows))
    return outputs


class FieldNegInvEmitterTests(unittest.TestCase):
    def test_compilation_honors_isolated_target_and_cargo_executable(self):
        import os
        import tempfile
        from unittest.mock import patch
        with tempfile.TemporaryDirectory(prefix="emitter-target-", dir=EXPORTS) as target:
            with patch.dict(os.environ, {"CARGO_TARGET_DIR": target}):
                binary = compile_modules({"identity": (identity_module("bool"), "native")})
            self.assertTrue(binary.is_relative_to(target),str(binary))
            self.assertEqual(run_curve_cases(self,binary,[{"program":"identity","inputs":[True]}]),[{"ok":True}])

    def test_lowered_nat_neg_inv_raw_pack_semantics_and_strict_admission(self):
        import copy
        emitter = load_emitter()
        modules, rows, expected = {}, [], []
        for fid, modulus in enumerate(emitter.FIELD_MODULI):
            field = {"field": fid, "modulus": modulus}
            p = int(modulus)
            for op in ("neg", "inv"):
                tag = "nat.field." + op
                direct = primitive_module(tag, [field], field, field)
                label = f"direct-{fid}-{op}"
                modules[label] = (direct, "nat")
                for mode in ("native", "u64"):
                    with self.assertRaises(emitter.EmitError): emitter.emit_module(direct, mode)
                for key, bad in (("static", {"field": fid}),
                                 ("static", {**field, "extra": 0}),
                                 ("static", {**field, "modulus": "17"}),
                                 ("static", {**field, "field": True}),
                                 ("regions", [{"inputs": [], "output": field, "body": {"tag": "ret", "ref": 0}}])):
                    malformed = copy.deepcopy(direct); malformed["body"][key] = bad
                    with self.assertRaises(emitter.EmitError): emitter.emit_module(malformed, "nat")
                other = {"field": (fid+1)%3, "modulus": emitter.FIELD_MODULI[(fid+1)%3]}
                for args, out in (([], field), ([field, field], field), ([other], field), ([field], other)):
                    with self.assertRaises(emitter.EmitError):
                        emitter.emit_module(primitive_module(tag, args, out, field), "nat")
                raw = primitive_module("nat.field.pack", ["nat"], field, {"field": fid})
                raw["body"]["next"] = copy.deepcopy(direct["body"])
                modules[f"raw-{fid}-{op}"] = (raw, "nat")
                for a in (0, 1, 2, p-1, p, p+1, 2*p, 2*p+7, 2**600+17):
                    reduced = a % p
                    out = (-reduced) % p if op == "neg" else 0 if reduced == 0 else pow(reduced, -1, p)
                    rows.append({"program": f"raw-{fid}-{op}", "inputs": [str(a)]})
                    expected.append({"ok": str(out)})
                    if a < p:
                        rows.append({"program": label, "inputs": [str(a)]})
                        expected.append({"ok": str(out)})
                for a in (p, p+1, 2*p):
                    rows.append({"program": label, "inputs": [str(a)]})
                    expected.append({"error": "noncanonical_field"})
                # Pair the unchanged raw record with its operation result. The
                # operation's explicit modulo must not repair the original pack.
                paired = copy.deepcopy(raw)
                paired["output"] = {"pair": [field, field]}
                pair = primitive_module("value.pair", [field, field], paired["output"])["body"]
                pair["args"] = [1, 0]
                paired["body"]["next"]["next"] = pair
                modules[f"paired-{fid}-{op}"] = (paired, "nat")
                rows.append({"program": f"paired-{fid}-{op}", "inputs": [str(p+1)]})
                expected.append({"ok": [str(p+1), str(p-1 if op == "neg" else 1)]})
        binary = compile_modules(modules)
        outputs = run_curve_cases(self, binary, rows)
        self.assertEqual([{k: v for k, v in row.items() if k != "message"} for row in outputs], expected)

    def test_unary_field_signatures_metadata_and_input_canonicality(self):
        import copy
        emitter = load_emitter()
        c = curve_descriptor()
        field, other = c["scalar"], c["base"]
        modules = {}
        for op in ("neg", "inv"):
            module = primitive_module("field." + op, [field], field, field)
            modules[op] = (module, "native")
            for args, output, metadata in (([], field, field), ([field, field], field, field),
                                          ([other], field, field), ([field], other, field),
                                          ([field], field, {**field, "modulus": other["modulus"]}),
                                          ([field], field, {**field, "field": True}),
                                          ([field], field, {**field, "extra": 0})):
                with self.subTest(op=op, args=args, output=output, metadata=metadata):
                    with self.assertRaises(emitter.EmitError):
                        emitter.emit_module(primitive_module("field."+op, args, output, metadata), "native")
            malformed = copy.deepcopy(module)
            malformed["body"]["regions"] = [{"inputs": [], "output": field, "body": {"tag": "ret", "ref": 0}}]
            with self.assertRaises(emitter.EmitError): emitter.emit_module(malformed, "native")
        binary = compile_modules(modules)
        invalid = [(field["modulus"], "noncanonical_field"), (True, "invalid_input_type"), ("-1", "negative_natural")]
        rows = [{"program": op, "inputs": [value]} for op in modules for value, _ in invalid]
        outputs = run_curve_cases(self, binary, rows)
        self.assertEqual([out.get("error") for out in outputs], [error for _ in modules for _, error in invalid])

    def test_native_neg_inv_total_zero_and_full_width_oracles(self):
        emitter = load_emitter()
        modules, rows, expected = {}, [], []
        for fid, modulus in enumerate(emitter.FIELD_MODULI):
            field = {"field": fid, "modulus": modulus}
            p = int(modulus)
            values = (0, 1, 2, 7, p-1, p-2, 2**192+17)
            for op in ("neg", "inv"):
                label = f"{fid}-{op}"
                modules[label] = (primitive_module("field." + op, [field], field, field), "native")
                for x in values:
                    y = -x % p if op == "neg" else 0 if x == 0 else pow(x, -1, p)
                    if op == "inv" and x: self.assertEqual(x*y % p, 1)
                    rows.append({"program": label, "inputs": [str(x)]})
                    expected.append({"ok": str(y)})
        binary = compile_modules(modules)
        self.assertEqual(run_curve_cases(self, binary, rows), expected)
        for (module, mode) in modules.values():
            source = emitter.emit_module(module, mode)
            fid = module["output"]["field"]
            prefix = ("bn254", "secp_base", "secp_scalar")[fid]
            self.assertIn(f"typed::{prefix}_{module['name'].split('.')[-1]}(", source)
            with self.assertRaises(emitter.EmitError): emitter.emit_module(module, "u64")


class BranchEmitterTests(unittest.TestCase):
    def test_control_if_executes_both_closed_arithmetic_regions(self):
        modules, rows, expected = {}, [], []
        field = curve_descriptor()["scalar"]
        for mode, ty, prefix, static in (("native", field, "field", field), ("nat", "nat", "nat", {})):
            regions = [{"inputs": [ty, ty], "output": ty,
                        "body": primitive_module(prefix + "." + op, [ty, ty], ty, static)["body"]}
                       for op in ("mul", "add")]
            module = primitive_module("control.if", ["bool", ty, ty], ty, regions=regions)
            modules[mode] = (module, mode)
            for condition in (True, False):
                rows.append({"program": mode, "inputs": [condition, "7", "11"]})
                expected.append({"ok": "77" if condition else "18"})
        binary = compile_modules(modules)
        self.assertEqual(run_curve_cases(self, binary, rows), expected)
        for module, mode in modules.values():
            source = load_emitter().emit_module(module, mode)
            self.assertIn("if a0.clone() {", source)
            self.assertIn("} else {", source)

    def test_option_match_payload_and_explicit_captures_execute(self):
        c = curve_descriptor()
        field = c["scalar"]
        none = {"inputs": [field, field], "output": field,
                "body": primitive_module("field.add", [field, field], field, field)["body"]}
        some_body = primitive_module("field.mul", [field, field], field, field)["body"]
        some_body["args"] = [0, 2]
        some = {"inputs": [field, field, field], "output": field, "body": some_body}
        module = primitive_module("option.match", [{"option": field}, field, field], field, regions=[none, some])
        binary = compile_modules({"match": (module, "native")})
        rows = [{"program": "match", "inputs": [value, "7", "11"]} for value in (None, "3", "0")]
        self.assertEqual(run_curve_cases(self, binary, rows), [{"ok": "18"}, {"ok": "33"}, {"ok": "0"}])
        source = load_emitter().emit_module(module, "native")
        self.assertIn("match a0.clone()", source)
        self.assertIn("None =>", source)
        self.assertIn("Some(", source)

    def test_unselected_if_and_option_match_regions_are_not_evaluated(self):
        import subprocess
        captures = ["word4"] * 4
        loop = primitive_module("u64.repeat", captures, "word4", {"count": 2**64-1}, regions=[{
            "inputs": ["nat"] + captures, "output": "word4", "body": {"tag": "ret", "ref": 1}}])["body"]
        dead = {"inputs": captures, "output": "word4", "body": loop}
        live = {"inputs": captures, "output": "word4", "body": {"tag": "ret", "ref": 0}}
        some_live = {"inputs": ["bool"] + captures, "output": "word4", "body": {"tag": "ret", "ref": 1}}
        import copy
        some_dead = copy.deepcopy(dead)
        some_dead["inputs"] = ["bool"] + captures
        some_dead["body"]["args"] = [1, 2, 3, 4]
        modules = {
            "if-true": (primitive_module("control.if", ["bool"] + captures, "word4", regions=[live, dead]), "u64"),
            "if-false": (primitive_module("control.if", ["bool"] + captures, "word4", regions=[dead, live]), "u64"),
            "match-none": (primitive_module("option.match", [{"option": "bool"}] + captures, "word4", regions=[live, some_dead]), "u64"),
            "match-some": (primitive_module("option.match", [{"option": "bool"}] + captures, "word4", regions=[dead, some_live]), "u64"),
        }
        binary = compile_modules(modules)
        word = ["1", "2", "3", "4"]
        rows = [{"program": program, "inputs": [flag] + [word]*4}
                for program, flag in (("if-true", True), ("if-false", False), ("match-none", None), ("match-some", False))]
        # A non-selected loop has a finite but infeasible count. Only correct lazy
        # branch emission completes this bounded run; no foreign helper is mocked.
        result = subprocess.run([str(binary)], input="\n".join(map(json.dumps, rows)) + "\n",
                                capture_output=True, text=True, timeout=3)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([json.loads(line) for line in result.stdout.splitlines()], [{"ok": word}] * len(rows))

    def test_branch_region_metadata_and_scope_rejected_before_emission(self):
        import copy
        emitter = load_emitter()
        field = curve_descriptor()["scalar"]
        live = {"inputs": [field], "output": field, "body": {"tag": "ret", "ref": 0}}
        some = {"inputs": [field, field], "output": field, "body": {"tag": "ret", "ref": 0}}
        for op, inp, regions in (("control.if", "bool", [live, live]),
                                  ("option.match", {"option": field}, [live, some])):
            module = primitive_module(op, [inp, field], field, regions=regions)
            self.assertIn("pub fn run", emitter.emit_module(module, "native"))
            bads = []
            for bad_regions in ([], [live], [live, live, live]):
                bad = copy.deepcopy(module); bad["body"]["regions"] = bad_regions; bads.append(bad)
            for i in (0, 1):
                for key, value in (("inputs", []), ("output", "bool"),
                                   ("body", {"tag": "ret", "ref": len(regions[i]["inputs"])})):
                    bad = copy.deepcopy(module); bad["body"]["regions"][i][key] = value; bads.append(bad)
            bad = copy.deepcopy(module); bad["body"]["static"] = {"extra": 0}; bads.append(bad)
            bad = copy.deepcopy(module)
            bad["inputs"][0]["type"] = bad["body"]["arg_types"][0] = "u64"
            bads.append(bad)
            for bad in bads:
                with self.subTest(op=op, body=bad["body"]):
                    with self.assertRaises(emitter.EmitError): emitter.emit_module(bad, "native")


class GenericCurveEmitterTests(unittest.TestCase):
    def test_checked_curve_constants_compile_direct_points(self):
        c = curve_descriptor()
        pt = {"point": c}
        p = int(c["base"]["modulus"])
        points = [None, SECP_G, (SECP_G[0], -SECP_G[1] % p), secp_add_oracle(SECP_G, SECP_G)]
        modules = {}
        for i, point in enumerate(points):
            literal = {"infinity": True} if point is None else {"x": str(point[0]), "y": str(point[1])}
            modules[str(i)] = (primitive_module("curve.const", [], pt, {"curve": c, "value": literal}), "native")
        binary = compile_modules(modules)
        rows = [{"program": name, "inputs": []} for name in modules]
        self.assertEqual(run_curve_cases(self, binary, rows), [{"ok": secp_hex_oracle(point)} for point in points])
        emitter = load_emitter()
        for module, mode in modules.values():
            source = emitter.emit_module(module, mode)
            self.assertIn("Result<typed::SecpPoint>", source)
            self.assertNotIn("Option<", source)
            self.assertNotIn("from_affine(", source)
        literals = [{}, {"infinity": False}, {"infinity": 1}, {"infinity": True, "x": "0"},
                    {"x": "0", "y": "0"}, {"x": "1", "y": "1"},
                    {"x": str(p), "y": "0"}, {"x": str(SECP_G[0]), "y": str(p)},
                    {"x": "0" + str(SECP_G[0]), "y": str(SECP_G[1])},
                    {"x": SECP_G[0], "y": str(SECP_G[1])},
                    {"x": "-1", "y": "0"}, {"x": str(SECP_G[0]), "y": str(SECP_G[1]), "extra": 0}]
        for literal in literals:
            with self.subTest(literal=literal):
                with self.assertRaises(emitter.EmitError):
                    emitter.emit_module(primitive_module("curve.const", [], pt, {"curve": c, "value": literal}), "native")
        for arguments, result in (([pt], pt), ([], {"option": pt}), ([], c["base"])):
            with self.assertRaises(emitter.EmitError):
                emitter.emit_module(primitive_module("curve.const", arguments, result,
                    {"curve": c, "value": {"infinity": True}}), "native")

    def test_equation_metadata_is_required_and_exact(self):
        import copy
        emitter = load_emitter()
        c = curve_descriptor()
        missing = copy.deepcopy(c); del missing["weierstrass"]
        bads = [missing] + [{**c, "weierstrass": coefficients} for coefficients in
                           (None, [], ["0"]*4, [0, 0, 0, 0, 7], ["0", "0", "0", "0", "07"],
                            ["0", "0", "0", "1", "7"], ["0", "0", "0", "0", c["base"]["modulus"]])]
        for descriptor in bads:
            for module in (identity_module({"point": descriptor}),
                           primitive_module("curve.generator", [], {"point": c}, {"curve": descriptor})):
                with self.subTest(descriptor=descriptor):
                    with self.assertRaises(emitter.EmitError): emitter.emit_module(module, "native")

    def test_curve_metadata_signatures_and_recursive_ids_fail_closed(self):
        import copy
        emitter = load_emitter()
        c = curve_descriptor()
        pt = {"point": c}
        terms = {"list": {"pair": [c["scalar"], pt]}}
        wrong_curves = [None, "secp256k1", {}, {**c, "id": "other"}, {**c, "id": True},
                        {**c, "base": c["scalar"]}, {**c, "scalar": c["base"]},
                        {**c, "extra": 0}, {"id": c["id"], "base": c["base"]}]
        for role in ("base", "scalar"):
            for bad_field in ({"field": True, "modulus": c[role]["modulus"]},
                              {"field": 3, "modulus": c[role]["modulus"]},
                              {**c[role], "modulus": "0" + c[role]["modulus"]},
                              {**c[role], "modulus": int(c[role]["modulus"])},
                              {**c[role], "extra": 0}, {}, None):
                wrong_curves.append({**c, role: bad_field})
        original = primitive_module("curve.msm", [terms], pt, {"curve": c})
        for bad_curve in wrong_curves:
            probes = [identity_module({"list": {"option": {"pair": [c["base"], {"point": bad_curve}]}}})]
            static = copy.deepcopy(original)
            static["body"]["static"]["curve"] = bad_curve
            probes.append(static)
            mixed = primitive_module("curve.eq", [pt, {"point": bad_curve}], "bool", {"curve": c})
            probes.append(mixed)
            for probe in probes:
                with self.subTest(curve=bad_curve, probe=probe["name"]):
                    with self.assertRaises(emitter.EmitError): emitter.emit_module(probe, "native")
        bad_signatures = [
            primitive_module("curve.mul", [c["base"], pt], pt, {"curve": c}),
            primitive_module("curve.eq", [pt, pt], c["base"], {"curve": c}),
            primitive_module("curve.eq", [pt], "bool", {"curve": c}),
            primitive_module("curve.msm", [{"list": {"pair": [c["base"], pt]}}], pt, {"curve": c}),
            primitive_module("curve.msm", [{"list": {"pair": [pt, c["scalar"]]}}], pt, {"curve": c}),
            primitive_module("curve.msm", [{"list": c["scalar"]}, {"list": pt}], pt, {"curve": c}),
            primitive_module("curve.fromAffine", [{"pair": [c["base"], c["scalar"]]}], {"option": pt}, {"curve": c}),
            primitive_module("value.cons", [c["base"], {"list": c["scalar"]}], {"list": c["scalar"]}),
        ]
        nested = {"list": {"option": {"pair": [c["base"], c["scalar"]]}}}
        call = primitive_module("method.call", [nested], nested, {"name": "nested", "index": 0})
        call["methods"] = [{"name": "nested", "args": [nested], "result": nested,
                            "body": {"tag": "ret", "ref": 0}}]
        self.assertIn("method_0(", emitter.emit_module(call, "native"))
        # Swap same-representation field IDs at a method boundary, including nested carriers.
        call["methods"][0]["args"] = [{"list": {"option": {"pair": [c["scalar"], c["base"]]}}}]
        call["methods"][0]["result"] = copy.deepcopy(call["methods"][0]["args"][0])
        bad_signatures.append(call)
        for probe in bad_signatures:
            with self.subTest(signature=probe["name"]):
                with self.assertRaises(emitter.EmitError): emitter.emit_module(probe, "native")
        for mode in ("nat", "u64"):
            with self.assertRaises(emitter.EmitError): emitter.emit_module(original, mode)
        for ty in ({"list": "nat"}, {"list": {"option": {"pair": ["bool", "nat"]}}}):
            with self.assertRaises(emitter.EmitError): emitter.emit_module(identity_module(ty), "u64")

    def test_msm_parser_checks_unused_zero_and_late_terms_without_panics(self):
        c = curve_descriptor()
        pt = {"point": c}
        terms = {"list": {"pair": [c["scalar"], pt]}}
        unused = primitive_module("curve.identity", [], pt, {"curve": c})
        unused["inputs"] = [{"name": "unused", "type": terms}]
        nested = {"list": {"option": {"option": terms}}}
        binary = compile_modules({
            "msm": (primitive_module("curve.msm", [terms], pt, {"curve": c}), "native"),
            "unused": (unused, "native"), "nested": (identity_module(nested), "native"),
        })
        g = secp_hex_oracle(SECP_G)
        invalid = [(None, "invalid_input_type"), ({}, "invalid_input_type"),
                   ([[]], "input_length"), ([["1"]], "input_length"),
                   ([["1", g, "extra"]], "input_length"), ([[g, "1"]], "invalid_integer"),
                   ([["0", "zz"]], "invalid_point_encoding"),
                   ([["1", g], [c["scalar"]["modulus"], g]], "noncanonical_field"),
                   ([["1", g], ["1", "04" + "00"*64]], "invalid_point_encoding"),
                   ([["-1", g]], "negative_natural"), ([[True, g]], "invalid_input_type"),
                   ([["1", g], ["0", None]], "invalid_input_type")]
        rows = [{"program": program, "inputs": [value]} for program in ("msm", "unused") for value, _ in invalid]
        expected = [error for _ in ("msm", "unused") for _, error in invalid]
        for value in ([[]], [{"some": [], "extra": 0}], [{"some": [["1", g, "extra"]]}]):
            rows.append({"program": "nested", "inputs": [value]})
            expected.append("input_length" if value == [{"some": [["1", g, "extra"]]}] else "invalid_input_type")
        outputs = run_curve_cases(self, binary, rows)
        self.assertEqual([out.get("error") for out in outputs], expected)
        self.assertEqual(run_curve_cases(self, binary, [{"program": "msm", "inputs": [[]]}]), [{"ok": "00"}])

    def test_list_constructors_nested_option_roundtrip_and_method_calls(self):
        c = curve_descriptor()
        leaf = {"pair": [c["scalar"], {"point": c}]}
        terms = {"list": leaf}
        nested = {"list": {"option": {"option": {"pair": [c["base"], terms]}}}}
        modules = {
            "nil": (primitive_module("value.nil", [], terms), "native"),
            "cons": (primitive_module("value.cons", [leaf, terms], terms), "native"),
        }
        module = primitive_module("method.call", [nested], nested, {"name": "nested.identity", "index": 0})
        module["methods"] = [{"name": "nested.identity", "args": [nested], "result": nested,
                              "body": {"tag": "ret", "ref": 0}}]
        modules["nested"] = (module, "native")
        portable = {"list": {"option": {"option": {"list": {"pair": [c["base"], c["scalar"]]}}}}}
        for mode in ("native", "nat", "u64"):
            modules[mode] = (identity_module(portable), mode)
        binary = compile_modules(modules)
        p, n = map(int, load_emitter().FIELD_MODULI[1:])
        first, second = [str(n-1), secp_hex_oracle(SECP_G)], ["0", "00"]
        value = [None, {"some": None}, {"some": [str(p-1), []]}, {"some": ["7", [first, second, first]]}]
        portable_value = [None, {"some": None}, {"some": []}, {"some": [[str(p-1), str(n-1)], ["0", "7"]]}]
        rows = [{"program": "nil", "inputs": []},
                {"program": "cons", "inputs": [first, [second, first]]},
                {"program": "nested", "inputs": [value]}]
        expected = [{"ok": []}, {"ok": [first, second, first]}, {"ok": value}]
        for mode in ("native", "nat", "u64"):
            rows.append({"program": mode, "inputs": [portable_value]})
            expected.append({"ok": portable_value})
        outputs = run_curve_cases(self, binary, rows)
        self.assertEqual(outputs, expected)
        replay = [{"program": row["program"], "inputs": [out["ok"]]} for row, out in zip(rows[2:], outputs[2:])]
        self.assertEqual(run_curve_cases(self, binary, replay), outputs[2:])
        source = load_emitter().emit_module(module, "native")
        self.assertIn("method_0(a0.clone())?", source)
        self.assertIn("Option<Option<(typed::SecpBase, Vec<(typed::SecpScalar, typed::SecpPoint)>)>>", source)

    def test_msm_list_executes_against_independent_affine_group_oracle(self):
        c = curve_descriptor()
        pt = {"point": c}
        terms = {"list": {"pair": [c["scalar"], pt]}}
        modules = {
            "msm": (primitive_module("curve.msm", [terms], pt, {"curve": c}), "native"),
            "terms": (identity_module(terms), "native"),
            "mul": (primitive_module("curve.mul", [c["scalar"], pt], pt, {"curve": c}), "native"),
        }
        binary = compile_modules(modules)
        p, n = map(int, load_emitter().FIELD_MODULI[1:])
        g = SECP_G
        neg_g = (g[0], -g[1] % p)
        two_g = secp_add_oracle(g, g)
        samples = [[], [(0, g)], [(1, g)], [(n-1, g)], [(2**255, g)],
                   [(7, None)], [(2, g), (3, two_g)], [(1, g), (1, neg_g)],
                   [(n-1, g), (1, g)], [(2**255, g), (n-2**255, g)],
                   [(n-1, g), (n-2, two_g), (2**192+7, neg_g)], [(1, g)] * 40]
        rows, expected = [], []
        for sample in samples:
            inputs = [[str(k), secp_hex_oracle(point)] for k, point in sample]
            total = None
            for k, point in sample:
                total = secp_add_oracle(total, secp_mul_oracle(k, point))
            rows.extend([{"program": "msm", "inputs": [inputs]}, {"program": "terms", "inputs": [inputs]}])
            expected.extend([{"ok": secp_hex_oracle(total)}, {"ok": inputs}])
            if len(sample) == 1:
                rows.append({"program": "mul", "inputs": inputs[0]})
                expected.append({"ok": secp_hex_oracle(total)})
        self.assertEqual(run_curve_cases(self, binary, rows), expected)
        source = load_emitter().emit_module(modules["msm"][0], "native")
        self.assertIn("Vec<(typed::SecpScalar, typed::SecpPoint)>", source)
        self.assertIn("typed::point_msm(", source)

    def test_curve_mul_eq_descriptor_ir_executes_real_rust(self):
        import subprocess
        c = curve_descriptor()
        pt = {"point": c}
        modules = {
            "mul": (primitive_module("curve.mul", [c["scalar"], pt], pt, {"curve": c}), "native"),
            "eq": (primitive_module("curve.eq", [pt, pt], "bool", {"curve": c}), "native"),
        }
        binary = compile_modules(modules)
        g = "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
        minus_g = "03" + g[2:]
        uncompressed = "04" + g[2:] + "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8"
        rows = [("mul", ["0", g], "00"), ("mul", ["1", g], g),
                ("mul", [str(int(c["scalar"]["modulus"]) - 1), g], minus_g),
                ("eq", [g, uncompressed], True), ("eq", [g, minus_g], False),
                ("eq", ["00", "00"], True), ("eq", ["00", g], False)]
        result = subprocess.run([str(binary)],
            input="\n".join(json.dumps({"program": name, "inputs": args}) for name, args, _ in rows) + "\n",
            capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([json.loads(line) for line in result.stdout.splitlines()],
                         [{"ok": out} for _, _, out in rows])
        source = load_emitter().emit_module(modules["eq"][0], "native")
        self.assertIn("typed::point_eq(", source)
        self.assertIn("Result<bool>", source)
        self.assertNotIn("point_hex(a", source)

    def test_no_x_or_scale_primitive_or_runtime_export(self):
        emitter = load_emitter()
        c = curve_descriptor()
        for point, metadata in (({"point": "secp256k1"}, "secp256k1"), ({"point": c}, c)):
            for op in ("secp.x", "curve.x", "secp.scale", "curve.scale"):
                args, result = ([point], c["base"]) if op.endswith(".x") else ([c["scalar"], point], point)
                with self.subTest(op=op, point=point):
                    with self.assertRaises(emitter.EmitError):
                        emitter.emit_module(primitive_module(op, args, result, {"curve": metadata}), "native")
        runtime = (ROOT / "backend/src/typed.rs").read_text()
        self.assertNotRegex(runtime, r"pub fn point_(?:x|scale)\(")


class ActualCurveExportTests(unittest.TestCase):
    def test_actual_lean_eq_msm_and_constructed_msm_exports_execute(self):
        names = ("curve_eq", "curve_msm", "curve_msm_constructed")
        modules = {name: (json.loads((EXPORTS / "bundle" / (name + ".json")).read_text()), "native") for name in names}
        for name, (module, _) in modules.items():
            self.assertEqual(module["name"], name)
        binary = compile_modules(modules)
        n = int(load_emitter().FIELD_MODULI[2])
        g = secp_hex_oracle(SECP_G)
        uncompressed = "04" + f"{SECP_G[0]:064x}{SECP_G[1]:064x}"
        rows = [{"program": "curve_eq", "inputs": [g, uncompressed]},
                {"program": "curve_eq", "inputs": [g, "00"]},
                {"program": "curve_msm", "inputs": [[]]},
                {"program": "curve_msm", "inputs": [[[str(n-1), g], ["1", g]]]},
                {"program": "curve_msm", "inputs": [[["2", g], ["3", uncompressed]]]},
                {"program": "curve_msm_constructed", "inputs": [str(2**255), g]},
                {"program": "curve_msm_constructed", "inputs": ["0", g]}]
        expected = [{"ok": True}, {"ok": False}, {"ok": "00"}, {"ok": "00"},
                    {"ok": secp_hex_oracle(secp_mul_oracle(5, SECP_G))},
                    {"ok": secp_hex_oracle(secp_mul_oracle(2**255, SECP_G))}, {"ok": "00"}]
        self.assertEqual(run_curve_cases(self, binary, rows), expected)
        source = load_emitter().emit_module(modules["curve_msm_constructed"][0], "native")
        self.assertIn("typed::point_msm(", source)
        self.assertIn(".extend(", source)


if __name__ == "__main__":
    unittest.main()
