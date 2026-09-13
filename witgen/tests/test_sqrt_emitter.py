"""Supplemental v2 sqrt/sub IR probes: emitted Rust execution, not Lean fixtures.

Run from witgen with an isolated CARGO_TARGET_DIR:
    python3 -B -m unittest discover -s tests -p test_sqrt_emitter.py -v
The parent pipeline separately exports and checks the proved Lean programs.
"""
import copy
import json
import subprocess
import unittest

from test_method_emitter import compile_modules, load_emitter, primitive_module


def fields():
    return [{"field": i, "modulus": p}
            for i, p in enumerate(load_emitter().FIELD_MODULI)]


def sqrt_module(field, mode):
    op = "field.sqrt" if mode == "native" else "nat.field.sqrt"
    return primitive_module(op, [field], {"option": field}, copy.deepcopy(field))


def sqrt_vectors(p):
    """Independent Python integer arithmetic: known squares and Euler criterion."""
    roots = [0, 1, 2, 17, (1 << 200) + 17, p // 2, p // 2 + 1,
             p - ((1 << 200) + 17), p - 17, p - 2, p - 1]
    # The Rust typed test checks that these full-width cases exercise both
    # Arkworks sign choices in every field; expected values remain Python math.
    roots.extend((i << 180) + i for i in range(1, 65))
    cases: list[tuple[str, str | None]] = [(str(r * r % p), str(min(r, (-r) % p))) for r in roots]
    nonresidue = next(n for n in range(2, 1000) if pow(n, (p - 1) // 2, p) == p - 1)
    cases.append((str(nonresidue), None))
    return cases


def execute(modules, requests):
    binary = compile_modules(modules)
    result = subprocess.run([str(binary)], input="\n".join(map(json.dumps, requests)) + "\n",
                            text=True, capture_output=True, timeout=30, check=True)
    rows = [json.loads(line) for line in result.stdout.splitlines()]
    if len(rows) != len(requests):
        raise AssertionError(f"expected {len(requests)} Rust responses, got {len(rows)}")
    return rows


class SqrtEmitterTests(unittest.TestCase):
    def test_sqrt_rejects_bad_static_signature_regions_and_modes(self):
        emitter = load_emitter()
        for field in fields():
            other = fields()[(field["field"] + 1) % 3]
            for mode in ("native", "nat"):
                original = sqrt_module(field, mode)
                prefix = ("bn254", "secp_base", "secp_scalar")[field["field"]]
                helper = (f"typed::{prefix}_sqrt(" if mode == "native"
                          else f"typed::nat_field_sqrt::<{field['field']}>(")
                self.assertIn(helper, emitter.emit_module(original, mode))
                controls = [
                    ("static", {}, "schema"),
                    ("static", {"field": field["field"]}, "schema"),
                    ("static", {**field, "value": "0"}, "schema"),
                    ("static", {**field, "field": True}, "integer"),
                    ("static", {**field, "field": -1}, "integer"),
                    ("static", {**field, "field": 3}, "integer"),
                    ("static", {**field, "modulus": other["modulus"]}, "field_modulus"),
                    ("static", {**field, "modulus": int(field["modulus"])}, "field_modulus"),
                    ("static", {**field, "modulus": "0" + field["modulus"]}, "field_modulus"),
                    ("static", other, "signature"),
                    ("result", field, "signature"),
                    ("result", {"option": other}, "signature"),
                    ("result", {"option": {"option": field}}, "signature"),
                    ("result", {"pair": [field, field]}, "signature"),
                    ("result", "bool", "signature"),
                    ("regions", [{}], "regions"),
                ]
                for key, value, code in controls:
                    bad = copy.deepcopy(original)
                    bad["body"][key] = value
                    with self.subTest(field=field["field"], mode=mode, key=key, value=value):
                        with self.assertRaises(emitter.EmitError) as caught:
                            emitter.emit_module(bad, mode)
                        self.assertEqual(caught.exception.code, code)
                for args in ([], [0, 0]):
                    bad = copy.deepcopy(original)
                    bad["body"].update(args=args, arg_types=[field] * len(args))
                    with self.assertRaises(emitter.EmitError) as caught:
                        emitter.emit_module(bad, mode)
                    self.assertEqual(caught.exception.code, "signature")
                bad = copy.deepcopy(original)
                bad["inputs"][0]["type"] = "nat"
                bad["body"]["arg_types"] = ["nat"]
                with self.assertRaises(emitter.EmitError) as caught:
                    emitter.emit_module(bad, mode)
                self.assertEqual(caught.exception.code, "signature")
                for wrong_mode in ({"native", "nat", "u64"} - {mode}):
                    with self.assertRaises(emitter.EmitError) as caught:
                        emitter.emit_module(original, wrong_mode)
                    self.assertEqual(caught.exception.code, "operation")
                # No hidden whole-field sqrt inside an unused word method or region.
                hidden = copy.deepcopy(original)
                hidden["methods"] = [{"name": "hidden", "args": [field],
                                      "result": {"option": field}, "body": hidden["body"]}]
                hidden["body"] = {"tag": "ret", "ref": 0}
                hidden["output"] = field
                with self.assertRaises(emitter.EmitError) as caught:
                    emitter.emit_module(hidden, "u64")
                self.assertEqual(caught.exception.code, "operation")
                region = {"inputs": [field], "output": {"option": field},
                          "body": original["body"]}
                hidden = primitive_module("option.bind", [{"option": field}],
                                          {"option": field}, regions=[region])
                with self.assertRaises(emitter.EmitError) as caught:
                    emitter.emit_module(hidden, "u64")
                self.assertEqual(caught.exception.code, "operation")
        with self.assertRaises(emitter.EmitError) as caught:
            emitter.emit_module(sqrt_module(fields()[0], "native"), "sqrt")
        self.assertEqual(caught.exception.code, "mode")

    def test_sqrt_external_inputs_remain_strictly_canonical(self):
        modules, requests, codes = {}, [], []
        for field in fields():
            for mode in ("native", "nat"):
                label = f"{mode}-{field['field']}"
                modules[label] = (sqrt_module(field, mode), mode)
                for inputs, code in [
                    ([field["modulus"]], "noncanonical_field"),
                    ([str(int(field["modulus"]) + 4)], "noncanonical_field"),
                    (["-1"], "negative_natural"),
                    (["not-a-number"], "invalid_integer"),
                    ([4], "invalid_input_type"),
                    ([None], "invalid_input_type"),
                    ([], "input_arity"),
                    (["4", "4"], "input_arity"),
                ]:
                    requests.append({"program": label, "inputs": inputs})
                    codes.append(code)
        self.assertEqual([row.get("error") for row in execute(modules, requests)], codes)

    def test_sqrt_composes_with_existing_recursive_option_codec(self):
        modules, requests, expected = {}, [], []
        for field in fields():
            for mode in ("native", "nat"):
                prefix = f"{mode}-{field['field']}"
                for depth in (1, 2):
                    module = sqrt_module(field, mode)
                    last, ty = module["body"], module["output"]
                    for _ in range(depth):
                        wrapped = {"option": ty}
                        last["next"] = primitive_module("option.some", [ty], wrapped)["body"]
                        last, ty = last["next"], wrapped
                    module["output"] = ty
                    label = prefix + f"-wrap-{depth}"
                    modules[label] = (module, mode)
                    for value, root in sqrt_vectors(int(field["modulus"])):
                        result = root
                        for _ in range(depth):
                            result = {"some": result}
                        requests.append({"program": label, "inputs": [value]})
                        expected.append({"ok": result})
                opt = {"option": field}
                label = prefix + "-bind"
                region = {"inputs": [field], "output": opt,
                          "body": sqrt_module(field, mode)["body"]}
                modules[label] = (primitive_module("option.bind", [opt], opt, regions=[region]), mode)
                for value, root in [(None, None)] + sqrt_vectors(int(field["modulus"])):
                    requests.append({"program": label, "inputs": [value]})
                    expected.append({"ok": root})
        self.assertEqual(execute(modules, requests), expected)

    def test_recursive_field_option_roundtrips_and_rejects_malformed_tags(self):
        modules, requests, expected, errors = {}, [], [], []
        for field in fields():
            opt = {"option": field}
            nested = {"option": opt}
            for mode in ("native", "nat", "u64"):
                for shape, ty, values in [
                    ("nested", nested, [None, {"some": None}, {"some": "0"}, {"some": "2"}]),
                    ("triple", {"option": nested}, [None, {"some": None}, {"some": {"some": None}},
                                                   {"some": {"some": "2"}}]),
                    ("pair", {"option": {"pair": [opt, nested]}},
                     [None, [None, {"some": None}], ["2", {"some": "0"}]]),
                ]:
                    label = f"{mode}-{field['field']}-{shape}"
                    modules[label] = ({"version": 2, "name": label, "methods": [],
                                       "inputs": [{"name": "input", "type": ty}], "output": ty,
                                       "body": {"tag": "ret", "ref": 0}}, mode)
                    for value in values:
                        requests.append({"program": label, "inputs": [value]})
                        expected.append({"ok": value})
                    if shape == "nested":
                        for value in ["0", {}, {"none": None}, {"some": "0", "extra": None},
                                      {"some": {"some": "0"}}]:
                            errors.append({"program": label, "inputs": [value]})
        rows = execute(modules, requests + errors)
        self.assertEqual(rows[:len(expected)], expected)
        self.assertTrue(all(row.get("error") == "invalid_input_type" for row in rows[len(expected):]))

    def test_nat_sqrt_executes_raw_pack_and_preserves_original(self):
        modules, requests, expected = {}, [], []
        for field in fields():
            p = int(field["modulus"])
            label = f"nat-{field['field']}"
            module = sqrt_module(field, "nat")
            modules[label] = (module, "nat")
            raw = primitive_module("nat.field.pack", ["nat"], field, {"field": field["field"]})
            pair = {"pair": [field, {"option": field}]}
            root = copy.deepcopy(module["body"])
            root["next"] = primitive_module("value.pair", [field, {"option": field}], pair)["body"]
            # After pack then sqrt, newest-first scope is [sqrt, raw, input].
            root["next"]["args"] = [1, 0]
            raw["body"]["next"] = root
            raw["output"] = pair
            modules[label + "-raw"] = (raw, "nat")
            for value, result in sqrt_vectors(p):
                requests.append({"program": label, "inputs": [value]})
                expected.append({"ok": result})
                for multiple in (1, 2, 1 << 600):
                    unreduced = str(int(value) + multiple * p)
                    requests.append({"program": label + "-raw", "inputs": [unreduced]})
                    expected.append({"ok": [unreduced, result]})
        self.assertEqual(execute(modules, requests), expected)

    def test_native_sqrt_executes_all_three_fields_against_integer_math(self):
        modules, requests, expected = {}, [], []
        for field in fields():
            label = f"native-{field['field']}"
            modules[label] = (sqrt_module(field, "native"), "native")
            for value, root in sqrt_vectors(int(field["modulus"])):
                requests.append({"program": label, "inputs": [value]})
                expected.append({"ok": root})
        self.assertEqual(execute(modules, requests), expected)


def sub_vectors(p):
    values = [0, 1, 2, p - 1, p - 2, (1 << 200) + 17, p // 2]
    return [(a, b, (a - b) % p) for a in values for b in values]


class SubEmitterTests(unittest.TestCase):
    def test_sub_metadata_types_arity_regions_and_mode_fail_closed(self):
        emitter = load_emitter()
        for field in fields():
            other = fields()[(field["field"] + 1) % 3]
            for mode, op in (("native", "field.sub"), ("nat", "nat.field.sub")):
                direct = primitive_module(op, [field, field], field, field)
                prefix = ("bn254", "secp_base", "secp_scalar")[field["field"]]
                helper = (f"typed::{prefix}_sub(" if mode == "native"
                          else f"typed::nat_field_sub::<{field['field']}>(")
                self.assertIn(helper, emitter.emit_module(direct, mode))
                for static in ({}, {"field": field["field"]}, {**field, "extra": 0},
                               {**field, "field": True}, {**field, "field": 3},
                               {**field, "modulus": other["modulus"]},
                               {**field, "modulus": int(field["modulus"])},
                               {**field, "modulus": "0" + field["modulus"]}):
                    with self.assertRaises(emitter.EmitError):
                        emitter.emit_module(primitive_module(op, [field, field], field, static), mode)
                for args, output in (([], field), ([field], field), ([field] * 3, field),
                                     ([other, field], field), ([field, other], field),
                                     (["nat", field], field), ([field, "nat"], field),
                                     ([field, field], other), ([field, field], {"option": field})):
                    with self.assertRaises(emitter.EmitError) as caught:
                        emitter.emit_module(primitive_module(op, args, output, field), mode)
                    self.assertEqual(caught.exception.code, "signature")
                bad = copy.deepcopy(direct)
                bad["body"]["regions"] = [{}]
                with self.assertRaises(emitter.EmitError) as caught:
                    emitter.emit_module(bad, mode)
                self.assertEqual(caught.exception.code, "regions")
                for wrong in ({"native", "nat", "u64"} - {mode}):
                    with self.assertRaises(emitter.EmitError) as caught:
                        emitter.emit_module(direct, wrong)
                    self.assertEqual(caught.exception.code, "operation")
                hidden = copy.deepcopy(direct)
                hidden["methods"] = [{"name": "hidden", "args": [field, field],
                                      "result": field, "body": hidden["body"]}]
                hidden["body"] = {"tag": "ret", "ref": 0}
                with self.assertRaises(emitter.EmitError) as caught:
                    emitter.emit_module(hidden, "u64")
                self.assertEqual(caught.exception.code, "operation")
                region = {"inputs": [field, field], "output": field, "body": direct["body"]}
                hidden = primitive_module("control.if", ["bool", field, field], field,
                                          regions=[region, copy.deepcopy(region)])
                with self.assertRaises(emitter.EmitError) as caught:
                    emitter.emit_module(hidden, "u64")
                self.assertEqual(caught.exception.code, "operation")

    def test_sub_rejects_noncanonical_external_operands_on_both_sides(self):
        modules, requests, expected = {}, [], []
        for field in fields():
            for mode, op in (("native", "field.sub"), ("nat", "nat.field.sub")):
                label = f"{mode}-{field['field']}"
                modules[label] = (primitive_module(op, [field, field], field, field), mode)
                for value, code in [(field["modulus"], "noncanonical_field"),
                                    (str(int(field["modulus"]) + 1), "noncanonical_field"),
                                    ("-1", "negative_natural"), (0, "invalid_input_type")]:
                    for inputs in ([value, "0"], ["0", value]):
                        requests.append({"program": label, "inputs": inputs})
                        expected.append(code)
                for inputs in ([], ["0"], ["0", "0", "0"]):
                    requests.append({"program": label, "inputs": inputs})
                    expected.append("input_arity")
        self.assertEqual([row.get("error") for row in execute(modules, requests)], expected)

    def test_nat_sub_executes_raw_operands_without_normalizing_either(self):
        modules, requests, expected = {}, [], []
        for field in fields():
            p = int(field["modulus"])
            label = f"sub-nat-{field['field']}"
            direct = primitive_module("nat.field.sub", [field, field], field, field)
            modules[label] = (direct, "nat")
            raw = primitive_module("nat.field.pack", ["nat", "nat"], field, {"field": field["field"]})
            raw["body"].update(args=[0], arg_types=["nat"])
            second = primitive_module("nat.field.pack", ["nat"], field, {"field": field["field"]})["body"]
            second["args"] = [2]
            difference = copy.deepcopy(direct["body"])
            difference["args"] = [1, 0]
            originals_ty = {"pair": [field, field]}
            originals = primitive_module("value.pair", [field, field], originals_ty)["body"]
            originals["args"] = [2, 1]
            output = {"pair": [originals_ty, field]}
            result = primitive_module("value.pair", [originals_ty, field], output)["body"]
            raw["body"]["next"] = second
            second["next"] = difference
            difference["next"] = originals
            originals["next"] = result
            raw["output"] = output
            modules[label + "-raw"] = (raw, "nat")
            for a, b, d in sub_vectors(p):
                requests.append({"program": label, "inputs": [str(a), str(b)]})
                expected.append({"ok": str(d)})
                for ka, kb in [(1, 0), (0, 2), (1 << 600, 7), (0, 1 << 600)]:
                    inputs = [str(a + ka * p), str(b + kb * p)]
                    requests.append({"program": label + "-raw", "inputs": inputs})
                    expected.append({"ok": [inputs, str(d)]})
        self.assertEqual(execute(modules, requests), expected)

    def test_native_sub_executes_all_fields_against_independent_integers(self):
        modules, requests, expected = {}, [], []
        for field in fields():
            label = f"sub-native-{field['field']}"
            modules[label] = (primitive_module("field.sub", [field, field], field, field), "native")
            for a, b, difference in sub_vectors(int(field["modulus"])):
                requests.append({"program": label, "inputs": [str(a), str(b)]})
                expected.append({"ok": str(difference)})
        self.assertEqual(execute(modules, requests), expected)


if __name__ == "__main__":
    unittest.main()
