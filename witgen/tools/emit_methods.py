#!/usr/bin/env python3
"""Fail-closed typed v2 AST → inspectable Rust method libraries.

API: emit_module(module: dict, mode: str) -> str. Modes are native/nat/u64.
The returned source is a Rust module, with one private `method_N` per registry
ordinal (oldest first), `pub fn run(a0, ...) -> witgen_native::Result<T>`, and
`pub fn run_json(inputs: &[serde_json::Value]) -> witgen_native::Result<Value>`.
The v2 `u64-shared-library` bundle is also accepted in u64 mode: its registry is
emitted once for every caller, with `program_N` / `program_N_json` functions and
`run_json(program: usize, inputs: &[Value])`, using oldest-first program ordinals.
Single modules and bundles must be embedded in separate Rust module namespaces.

Names are escaped comment receipts, never Rust identifiers. Calls remain calls;
no model execution or caller expansion is used. Runtime namespace/signatures are
in docs/NativeMethodsAPI.md; no concrete curve-library types are emitted. The u64
backend targets 64-bit usize and admits Nat only as an internally bounded index,
never as an external input/result, including inside pair/option types.

Example (after generating the real MainTyped exports)::

    from tools.emit_methods import emit_module
    import json
    source = emit_module(json.load(open("artifacts/methods/u64.json")), "u64")

No files or builds are produced by this pure API. The scoped execution harness is
in tests/test_method_emitter.py (`compile_modules`), which uses the parent crate,
ignored artifacts/methods build/source files, and a temporary ignored binary.
Run: python3 -B -m unittest discover -s tests -p test_method_emitter.py -v

This emitter, JSON boundary, Rust compiler and foreign arithmetic are tested TCB,
not Lean-kernel-verified. Nat field pack/unpack and WordField layout wrappers are
raw; arithmetic reductions must be explicit AST nodes. Static field constants
implement the source constant's explicit modulo, not a field-pack normalization.
Nat arithmetic and literals remain unbounded rug::Integer operations.
"""
import json
import re
from typing import NoReturn


FIELD_MODULI = (
    "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    "115792089237316195423570985008687907853269984665640564039457584007908834671663",
    "115792089237316195423570985008687907852837564279074904382605163141518161494337",
)


class EmitError(ValueError):
    """Typed compiler failure; code/path are stable machine-readable context."""
    def __init__(self, code, path, detail):
        self.code, self.path, self.detail = code, path, detail
        super().__init__(f"{code} at {path}: {detail}")


def fail(code, path, detail) -> NoReturn:
    raise EmitError(code, path, detail)


def keys(value, expected, path):
    if not isinstance(value, dict) or set(value) != set(expected.split()):
        fail("schema", path, f"expected object keys {expected}")


def array(value, path):
    if not isinstance(value, list):
        fail("schema", path, "expected array")
    return value


def name(value, path):
    if not isinstance(value, str):
        fail("schema", path, "expected name string")
    return value


def natural(value, path, bound=None):
    if type(value) is not int or value < 0 or (bound is not None and value >= bound):
        fail("integer", path, "expected in-range natural integer")
    return value


def decimal(value, path, bound=None):
    if not isinstance(value, str) or not re.fullmatch(r"0|[1-9][0-9]*", value):
        fail("decimal", path, "expected exact nonnegative decimal string")
    if bound is None:
        return value  # Leave unbounded literals to rug, never Python's digit cap.
    maximum = str(bound - 1)
    if len(value) > len(maximum) or (len(value) == len(maximum) and value > maximum):
        fail("integer", path, "decimal exceeds its word bound")
    return int(value)


def field_id(value, path):
    return natural(value, path, len(FIELD_MODULI))


def field_metadata(value, path):
    if not isinstance(value, dict) or not {"field", "modulus"} <= set(value):
        fail("schema", path, "expected field ID and modulus")
    f = field_id(value["field"], path + ".field")
    if value["modulus"] != FIELD_MODULI[f]:
        fail("field_modulus", path, "field ID requires its exact decimal modulus")
    return ("field", f)


def curve_metadata(value, path):
    keys(value, "id base scalar weierstrass", path)
    ident = name(value["id"], path + ".id")
    keys(value["base"], "field modulus", path + ".base")
    keys(value["scalar"], "field modulus", path + ".scalar")
    base = field_metadata(value["base"], path + ".base")
    scalar = field_metadata(value["scalar"], path + ".scalar")
    if (ident, base, scalar) != ("secp256k1", ("field", 1), ("field", 2)):
        fail("curve", path, "unsupported curve descriptor or mismatched base/scalar fields")
    coefficients = array(value["weierstrass"], path + ".weierstrass")
    if coefficients != ["0", "0", "0", "0", "7"]:
        fail("curve", path, "unsupported curve equation: exact canonical secp256k1 coefficients required")
    return ("point", ident, base, scalar, tuple(coefficients))


def curve_constant(value, path):
    if isinstance(value, dict) and set(value) == {"infinity"}:
        if value["infinity"] is not True:
            fail("curve_literal", path, "infinity literal requires true")
        return "typed::point_identity()"
    keys(value, "x y", path)
    modulus = int(FIELD_MODULI[1])
    x = int(decimal(value["x"], path + ".x", modulus))
    y = int(decimal(value["y"], path + ".y", modulus))
    if (y*y - x*x*x - 7) % modulus != 0:
        fail("curve_literal", path, "affine constant is not on the descriptor's curve")
    return (f'typed::point_const(typed::secp_base_from_str("{x}")?, '
            f'typed::secp_base_from_str("{y}")?)')


def rust_integer(value):
    # The decoder uses checked decimal strings, so this cannot contain Rust code.
    return f'rug::Integer::from_str_radix("{value}", 10)?'


def indent(text):
    return "\n".join("    " + line for line in text.splitlines())


def block(lines, result):
    return "{\n" + indent("\n".join(lines + [result])) + "\n}"


def signature(args, result, expected, output, path):
    if [t for _, t in args] != expected or result != output:
        fail("signature", path, "operation argument/result types differ from exact signature")


def contains_nat(ty):
    return ty == "nat" or (isinstance(ty, tuple) and ty[0] in ("pair", "option", "list")
                           and any(contains_nat(t) for t in ty[1:]))


def native_field_helper(f, op):
    if f == 0:
        return f"typed::bn254_{op}" if op in ("square", "neg", "inv", "sqrt", "sub") else f"witgen_native::bn254_{op}"
    return f"typed::secp_{'base' if f == 1 else 'scalar'}_{op}"


class Emitter:
    def __init__(self, module, mode):
        if mode not in ("native", "nat", "u64"):
            fail("mode", "mode", "expected native, nat or u64")
        self.mode = mode
        self.module = module
        self.counter = 0

    def ty(self, value, path):
        if isinstance(value, str) and value in ("nat", "bool", "u64", "word4"):
            return value
        if isinstance(value, dict) and set(value) == {"field", "modulus"}:
            return field_metadata(value, path)
        if isinstance(value, dict) and set(value) == {"point"}:
            if self.mode != "native":
                fail("type_mode", path, "only native mode supports secp256k1 points")
            return curve_metadata(value["point"], path + ".point")
        if isinstance(value, dict) and set(value) == {"pair"}:
            pair = array(value["pair"], path + ".pair")
            if len(pair) != 2:
                fail("type", path, "pair type requires exactly two elements")
            return ("pair", self.ty(pair[0], path + ".pair[0]"), self.ty(pair[1], path + ".pair[1]"))
        if isinstance(value, dict) and set(value) == {"option"}:
            return ("option", self.ty(value["option"], path + ".option"))
        if isinstance(value, dict) and set(value) == {"list"}:
            return ("list", self.ty(value["list"], path + ".list"))
        fail("type", path, "unsupported or malformed logical type")

    def types(self, values, path):
        return [self.ty(t, f"{path}[{i}]") for i, t in enumerate(array(values, path))]

    def rust_type(self, ty):
        if isinstance(ty, tuple) and ty[0] == "field":
            if self.mode == "u64":
                return f"typed::WordField<{ty[1]}>"
            if self.mode == "nat":
                return f"typed::NatField<{ty[1]}>"
            return ("witgen_native::Bn254Scalar", "typed::SecpBase", "typed::SecpScalar")[ty[1]]
        if isinstance(ty, tuple):
            if ty[0] == "point":
                return "typed::SecpPoint"
            if ty[0] == "pair":
                return f"({self.rust_type(ty[1])}, {self.rust_type(ty[2])})"
            if ty[0] == "list":
                return f"Vec<{self.rust_type(ty[1])}>"
            return f"Option<{self.rust_type(ty[1])}>"
        return {"nat": "usize" if self.mode == "u64" else "rug::Integer",
                "u64": "u64", "bool": "bool", "word4": "typed::Word4"}[ty]

    def fresh(self, prefix="v"):
        n = f"{prefix}{self.counter}"
        self.counter += 1
        return n

    def ref(self, index, env, path):
        return env[natural(index, path, len(env))]

    def operation(self, node, args, result, scope, path):
        op, static = node["op"], node["static"]
        expressions = [f"{n}.clone()" for n, _ in args]
        actual = [t for _, t in args]
        expected, output = [], result
        if op in ("control.if", "option.match"):
            return self.branch_operation(node, args, result, scope, path)
        if op.startswith(("value.", "option.")):
            return self.value_operation(node, args, result, scope, path)
        if self.mode == "native" and op.startswith(("field.", "secp.", "curve.")):
            return self.native_operation(node, args, result, path)
        if self.mode == "u64" and op.startswith("u64."):
            return self.u64_operation(node, args, result, scope, path)
        if array(node["regions"], path + ".regions"):
            fail("regions", path, "operation takes no regions")
        if op == "method.call":
            keys(static, "name index", path + ".static")
            index = natural(static["index"], path + ".static.index", len(scope))
            ordinal, method_name, expected, output = scope[-1 - index]
            if static["name"] != method_name:
                fail("method_link", path, "method name and local newest-first index disagree")
            expression = f"method_{ordinal}({', '.join(expressions)})?"
        elif self.mode == "nat" and op in ("nat.add", "nat.mul"):
            keys(static, "", path + ".static")
            expected, output = ["nat", "nat"], "nat"
            operator = "+" if op == "nat.add" else "*"
            expression = f"{expressions[0]} {operator} {expressions[1]}" if len(args) == 2 else ""
        elif self.mode == "nat" and op == "nat.mod":
            keys(static, "modulus", path + ".static")
            modulus = decimal(static["modulus"], path + ".static.modulus")
            expected, output = ["nat"], "nat"
            expression = (f"{expressions[0]} % {rust_integer(static['modulus'])}" if modulus != "0"
                          else expressions[0]) if len(args) == 1 else ""
        elif self.mode == "nat" and op in ("nat.field.neg", "nat.field.inv", "nat.field.sqrt", "nat.field.sub"):
            keys(static, "field modulus", path + ".static")
            fty = field_metadata(static, path + ".static")
            arity = 2 if op == "nat.field.sub" else 1
            expected, output = [fty] * arity, ("option", fty) if op == "nat.field.sqrt" else fty
            helper = "nat_field_" + op.rsplit(".", 1)[1]
            expression = f"typed::{helper}::<{fty[1]}>({', '.join(expressions)})?"
        elif self.mode == "nat" and op in ("nat.field.const", "nat.field.pack", "nat.field.unpack"):
            if op == "nat.field.const":
                keys(static, "field modulus value", path + ".static")
                fty = field_metadata(static, path + ".static")
                decimal(static["value"], path + ".static.value")
                expected, output = [], fty
                expression = (f"typed::NatField::<{fty[1]}>({rust_integer(static['value'])}"
                              f" % {rust_integer(static['modulus'])})")
            else:
                keys(static, "field", path + ".static")
                fty = ("field", field_id(static["field"], path + ".static.field"))
                if op == "nat.field.pack":
                    expected, output = ["nat"], fty
                    expression = f"typed::NatField::<{fty[1]}>({expressions[0]})" if len(args) == 1 else ""
                else:
                    expected, output = [fty], "nat"
                    expression = f"({expressions[0]}).0" if len(args) == 1 else ""
        else:
            fail("operation", path, f"unsupported operation {op!r} in {self.mode} mode")
        if actual != expected or result != output:
            fail("signature", path, "operation argument/result types differ from exact signature")
        return expression

    def native_operation(self, node, args, result, path):
        op, static = node["op"], node["static"]
        if array(node["regions"], path + ".regions"):
            fail("regions", path, "native primitive takes no regions")
        if op in ("field.const", "field.add", "field.sub", "field.mul", "field.square", "field.neg", "field.inv", "field.sqrt"):
            keys(static, "field modulus value" if op == "field.const" else "field modulus", path + ".static")
            field = field_metadata(static, path + ".static")
            arity = {"field.const": 0, "field.add": 2, "field.sub": 2, "field.mul": 2,
                     "field.square": 1, "field.neg": 1, "field.inv": 1, "field.sqrt": 1}[op]
            output = ("option", field) if op == "field.sqrt" else field
            signature(args, result, [field] * arity, output, path)
            f = field[1]
            if op == "field.const":
                decimal(static["value"], path + ".static.value")
                value = f"{rust_integer(static['value'])} % {rust_integer(static['modulus'])}"
                return f"{native_field_helper(f, 'from_nat')}(&({value}))?"
            helper = native_field_helper(f, op.split(".")[1])
        else:
            keys(static, "curve value" if op == "curve.const" else "curve", path + ".static")
            point = curve_metadata(static["curve"], path + ".static.curve")
            base, scalar = point[2:4]
            if op == "curve.const":
                signature(args, result, [], point, path)
                return curve_constant(static["value"], path + ".static.value")
            affine = ("pair", base, base)
            shapes = {
                "curve.add": ([point, point], point, "point_add"),
                "curve.mul": ([scalar, point], point, "point_mul"),
                "curve.eq": ([point, point], "bool", "point_eq"),
                "curve.msm": ([("list", ("pair", scalar, point))], point, "point_msm"),
                "curve.inv": ([point], point, "point_inv"),
                "curve.generator": ([], point, "point_generator"),
                "curve.identity": ([], point, "point_identity"),
                "curve.toAffine": ([point], ("option", affine), "to_affine"),
                "curve.fromAffine": ([affine], ("option", point), "from_affine"),
            }
            if op not in shapes:
                fail("operation", path, f"unsupported native operation {op!r}")
            expected, output, helper = shapes[op]
            signature(args, result, expected, output, path)
            helper = "typed::" + helper
        return f"{helper}({', '.join(n + '.clone()' for n, _ in args)})" + ("?" if op == "curve.msm" else "")

    def value_operation(self, node, args, result, scope, path):
        op = node["op"]
        keys(node["static"], "", path + ".static")
        regions = array(node["regions"], path + ".regions")
        if len(regions) != (1 if op == "option.bind" else 0):
            fail("regions", path, "wrong structural region count")
        a = [n + ".clone()" for n, _ in args]
        if op == "value.nil" and not args and isinstance(result, tuple) and result[0] == "list":
            return f"Vec::<{self.rust_type(result[1])}>::new()"
        if op == "value.cons" and len(args) == 2:
            head = args[0][1]
            signature(args, result, [head, ("list", head)], ("list", head), path)
            items = self.fresh("items")
            return block([f"let mut {items} = vec![{a[0]}];", f"{items}.extend({a[1]});"], items)
        if op == "value.pair" and len(args) == 2:
            signature(args, result, [args[0][1], args[1][1]], ("pair", args[0][1], args[1][1]), path)
            return f"({a[0]}, {a[1]})"
        if op in ("value.fst", "value.snd") and len(args) == 1:
            pair = args[0][1]
            if isinstance(pair, tuple) and pair[0] == "pair":
                part = 0 if op == "value.fst" else 1
                signature(args, result, [pair], pair[part + 1], path)
                return f"({a[0]}).{part}"
        if op == "option.some" and len(args) == 1:
            signature(args, result, [args[0][1]], ("option", args[0][1]), path)
            return f"Some({a[0]})"
        if op == "option.none" and not args and isinstance(result, tuple) and result[0] == "option":
            return f"None::<{self.rust_type(result[1])}>"
        if op == "option.bind" and len(args) == 1:
            inp = args[0][1]
            if (isinstance(inp, tuple) and inp[0] == "option"
                    and isinstance(result, tuple) and result[0] == "option"):
                x = self.fresh("some")
                body = self.region(regions[0], [(x, inp[1])], result, scope, path + ".regions[0]")
                return f"match {a[0]} {{\n" + indent(f"Some({x}) => {body},\nNone => None,") + "\n}"
        fail("signature", path, "unsupported structural operation or incorrect signature")

    def branch_operation(self, node, args, result, scope, path):
        keys(node["static"], "", path + ".static")
        regions = array(node["regions"], path + ".regions")
        if len(regions) != 2:
            fail("regions", path, "branch operation requires exactly two regions")
        if not args:
            fail("signature", path, "branch operation requires a discriminator")
        discr, ty = args[0]
        captures = args[1:]
        if node["op"] == "control.if":
            if ty != "bool":
                fail("signature", path, "if condition requires Bool")
            yes = self.region(regions[0], captures, result, scope, path + ".regions[0]")
            no = self.region(regions[1], captures, result, scope, path + ".regions[1]")
            return f"if {discr}.clone() {yes} else {no}"
        if not isinstance(ty, tuple) or ty[0] != "option":
            fail("signature", path, "option match requires an Option discriminator")
        payload = self.fresh("_some")
        none = self.region(regions[0], captures, result, scope, path + ".regions[0]")
        some = self.region(regions[1], [(payload, ty[1])] + captures, result, scope, path + ".regions[1]")
        return f"match {discr}.clone() {{\n" + indent(f"None => {none},\nSome({payload}) => {some},") + "\n}"

    def region(self, region, env, output, scope, path):
        keys(region, "inputs output body", path)
        if self.types(region["inputs"], path + ".inputs") != [t for _, t in env]:
            fail("region_type", path, "region input signature mismatch")
        if self.ty(region["output"], path + ".output") != output:
            fail("region_type", path, "region result signature mismatch")
        # Closed region: only declared inputs, never the enclosing program env.
        lines, result = self.program(region["body"], env, output, scope, path + ".body")
        return block(lines, result)

    def u64_operation(self, node, args, result, scope, path):
        op, static = node["op"], node["static"]
        shapes = {
            "u64.word": ([], "u64", "value"),
            "u64.flag": ([], "bool", "value"),
            "u64.literal": ([], "word4", "limbs"),
            "u64.get": (["word4"], "u64", "limb"),
            "u64.pack": (["u64"] * 4, "word4", ""),
            "u64.adcWord": (["u64", "u64", "bool"], "u64", ""),
            "u64.adcFlag": (["u64", "u64", "bool"], "bool", ""),
            "u64.sbbWord": (["u64", "u64", "bool"], "u64", ""),
            "u64.sbbFlag": (["u64", "u64", "bool"], "bool", ""),
            "u64.or": (["bool", "bool"], "bool", ""),
            "u64.not": (["bool"], "bool", ""),
            "u64.select": (["bool", "word4", "word4"], "word4", ""),
            "u64.bitAt": (["word4", "nat"], "bool", ""),
            "u64.repeat": (["word4"] * 4, "word4", "count"),
        }
        if op in ("u64.toWord", "u64.fromWord", "u64.fieldLiteral"):
            keys(static, "field limbs" if op == "u64.fieldLiteral" else "field", path + ".static")
            f = field_id(static["field"], path + ".static.field")
            ft = ("field", f)
            expected, output = {"u64.toWord": ([ft], "word4"),
                                "u64.fromWord": (["word4"], ft),
                                "u64.fieldLiteral": ([], ft)}[op]
        elif op in shapes:
            expected, output, required = shapes[op]
            keys(static, required, path + ".static")
        else:
            fail("operation", path, f"unsupported U64 operation {op!r}")
        signature(args, result, expected, output, path)
        regions = array(node["regions"], path + ".regions")
        if len(regions) != (1 if op == "u64.repeat" else 0):
            fail("regions", path, "wrong U64 region count")
        a = [f"{n}.clone()" for n, _ in args]
        if op == "u64.word":
            return str(decimal(static["value"], path + ".static.value", 1 << 64)) + "u64"
        if op == "u64.flag":
            if type(static["value"]) is not bool:
                fail("literal", path, "flag literal must be Boolean")
            return "true" if static["value"] else "false"
        if op in ("u64.literal", "u64.fieldLiteral"):
            limbs = array(static["limbs"], path + ".static.limbs")
            if len(limbs) != 4:
                fail("literal", path, "word literal requires exactly four limbs")
            values = [str(decimal(v, f"{path}.static.limbs[{i}]", 1 << 64)) + "u64"
                      for i, v in enumerate(limbs)]
            raw = "[" + ", ".join(values) + "]"
            return f"typed::WordField::<{static['field']}>({raw})" if op == "u64.fieldLiteral" else raw
        if op == "u64.get":
            limb = natural(static["limb"], path + ".static.limb", 4)
            return f"{a[0]}[{limb}]"
        if op == "u64.pack":
            return "[" + ", ".join(a) + "]"
        if op in ("u64.adcWord", "u64.adcFlag", "u64.sbbWord", "u64.sbbFlag"):
            helper = "adc" if op.startswith("u64.adc") else "sbb"
            part = 0 if op.endswith("Word") else 1
            return f"typed::{helper}({', '.join(a)}).{part}"
        if op == "u64.or":
            return f"{a[0]} || {a[1]}"
        if op == "u64.not":
            return f"!{a[0]}"
        if op == "u64.select":
            return f"if {a[0]} {{ {a[1]} }} else {{ {a[2]} }}"
        if op == "u64.bitAt":
            return f"typed::bit_at({a[0]}, {a[1]})"
        if op == "u64.toWord":
            return f"({a[0]}).0"
        if op == "u64.fromWord":
            return f"typed::WordField::<{static['field']}>({a[0]})"
        if op == "u64.repeat":
            # u64 backend targets 64-bit usize; never silently truncate counts.
            count = natural(static["count"], path + ".static.count", 1 << 64)
            index, acc = self.fresh("index"), self.fresh("acc")
            env = [(index, "nat"), (acc, "word4")] + args[:3]
            region = self.region(regions[0], env, "word4", scope, path + ".regions[0]")
            loop = f"for {index} in (0..{count}usize).rev() {{\n" + indent(f"{acc} = {region};") + "\n}"
            return block([f"let mut {acc}: typed::Word4 = {a[3]};", loop], acc)
        fail("operation", path, "unimplemented U64 operation")

    def program(self, body, env, output, scope, path):
        lines = []
        while True:
            if not isinstance(body, dict):
                fail("schema", path, "expected program object")
            if body.get("tag") == "ret":
                keys(body, "tag ref", path)
                n, t = self.ref(body["ref"], env, path + ".ref")
                if t != output:
                    fail("result_type", path, "return ref differs from declared result")
                return lines, n + ".clone()"
            keys(body, "tag op static args arg_types result regions next", path)
            if body["tag"] != "let" or not isinstance(body["op"], str):
                fail("schema", path, "expected let operation")
            args = [self.ref(r, env, f"{path}.args[{i}]")
                    for i, r in enumerate(array(body["args"], path + ".args"))]
            arg_types = self.types(body["arg_types"], path + ".arg_types")
            if [t for _, t in args] != arg_types:
                fail("argument_type", path, "reference types differ from arg_types")
            result = self.ty(body["result"], path + ".result")
            expression = self.operation(body, args, result, scope, path)
            variable = self.fresh()
            lines.append(f"let {variable}: {self.rust_type(result)} = {expression};")
            env = [(variable, result)] + env
            body = body["next"]
            path += ".next"

    def function(self, symbol, args, output, body, scope, path):
        env = [(f"a{i}", t) for i, t in enumerate(args)]
        lines, result = self.program(body, env, output, scope, path)
        params = ", ".join(f"{n}: {self.rust_type(t)}" for n, t in env)
        return (f"{symbol}({params}) -> witgen_native::Result<{self.rust_type(output)}> {{\n"
                + indent("\n".join(lines + [f"Ok({result})"]))
                + "\n}\n")

    def json_boundary(self, inputs, output, function="run", prefix=""):
        decoders, encoders = {}, {}
        definitions = []

        def decoder(ty):
            if ty in decoders:
                return decoders[ty]
            symbol = f"{prefix}decode_{len(decoders)}"
            decoders[ty] = symbol
            if isinstance(ty, tuple) and ty[0] == "field":
                f = ty[1]
                if self.mode == "native":
                    expr = f"{native_field_helper(f, 'from_nat')}(&typed::parse_nat(value)?)?"
                else:
                    rep = "word" if self.mode == "u64" else "nat"
                    expr = f"typed::parse_{rep}_field::<{f}>(value)?"
            elif isinstance(ty, tuple) and ty[0] == "pair":
                left, right = decoder(ty[1]), decoder(ty[2])
                expr = block([
                    'let pair = value.as_array().ok_or(witgen_native::Error::InvalidInputType { expected: "pair array" })?;',
                    'if pair.len() != 2 { return Err(witgen_native::Error::InputLength { expected: 2, actual: pair.len() }); }',
                ], f"({left}(&pair[0])?, {right}(&pair[1])?)")
            elif isinstance(ty, tuple) and ty[0] == "list":
                child = decoder(ty[1])
                expr = block([
                    'let values = value.as_array().ok_or(witgen_native::Error::InvalidInputType { expected: "list array" })?;',
                ], f"values.iter().map({child}).collect::<witgen_native::Result<Vec<_>>>()?")
            elif isinstance(ty, tuple) and ty[0] == "option":
                child = decoder(ty[1])
                if isinstance(ty[1], tuple) and ty[1][0] == "option":
                    error = 'witgen_native::Error::InvalidInputType { expected: "single-key some option object" }'
                    some = block([
                        f"let tagged = value.as_object().ok_or({error})?;",
                        f"if tagged.len() != 1 {{ return Err({error}); }}",
                        f'let payload = tagged.get("some").ok_or({error})?;',
                    ], f"Some({child}(payload)?)")
                    expr = f"if value.is_null() {{ None }} else {some}"
                else:
                    expr = f"if value.is_null() {{ None }} else {{ Some({child}(value)?) }}"
            elif isinstance(ty, tuple) and ty[0] == "point":
                expr = "typed::parse_point(value)?"
            elif ty == "bool":
                expr = 'value.as_bool().ok_or(witgen_native::Error::InvalidInputType { expected: "Boolean" })?'
            else:
                helper = {"nat": "parse_nat", "u64": "parse_u64", "word4": "parse_word4"}[ty]
                expr = f"typed::{helper}(value)?"
            definitions.append(f"fn {symbol}(value: &serde_json::Value) -> witgen_native::Result<{self.rust_type(ty)}> {{\n"
                               + indent(f"Ok({expr})") + "\n}\n")
            return symbol

        def encoder(ty):
            if ty in encoders:
                return encoders[ty]
            symbol = f"{prefix}encode_{len(encoders)}"
            encoders[ty] = symbol
            if isinstance(ty, tuple) and ty[0] == "field":
                f = ty[1]
                if self.mode == "native":
                    raw = f"{native_field_helper(f, 'to_nat')}(value).to_string()"
                elif self.mode == "nat":
                    raw = "value.0.to_string()"
                else:
                    raw = f"typed::word_field_decimal::<{f}>(value)"
                expr = f"serde_json::Value::String({raw})"
            elif isinstance(ty, tuple) and ty[0] == "pair":
                expr = f"serde_json::Value::Array(vec![{encoder(ty[1])}(value.0), {encoder(ty[2])}(value.1)])"
            elif isinstance(ty, tuple) and ty[0] == "list":
                expr = f"serde_json::Value::Array(value.into_iter().map({encoder(ty[1])}).collect())"
            elif isinstance(ty, tuple) and ty[0] == "option":
                payload = f"{encoder(ty[1])}(x)"
                # Only an Option payload can itself encode as JSON null.
                # Pairs (even pairs containing options) remain non-null arrays.
                if isinstance(ty[1], tuple) and ty[1][0] == "option":
                    payload = 'serde_json::json!({"some": ' + payload + '})'
                expr = f"match value {{ Some(x) => {payload}, None => serde_json::Value::Null }}"
            elif ty == "bool":
                expr = "serde_json::Value::Bool(value)"
            elif ty == "word4":
                expr = "typed::word4_json(value)"
            elif isinstance(ty, tuple) and ty[0] == "point":
                expr = "serde_json::Value::String(typed::point_hex(value))"
            else:
                expr = "serde_json::Value::String(value.to_string())"
            definitions.append(f"fn {symbol}(value: {self.rust_type(ty)}) -> serde_json::Value {{\n"
                               + indent(expr) + "\n}\n")
            return symbol

        dec = [decoder(t) for t in inputs]
        enc = encoder(output)
        args = ", ".join(f"{d}(&inputs[{i}])?" for i, d in enumerate(dec))
        lines = [f"if inputs.len() != {len(inputs)} {{ return Err(witgen_native::Error::InputArity {{ expected: {len(inputs)}, actual: inputs.len() }}); }}",
                 f"Ok({enc}({function}({args})?))"]
        definitions.append(f"pub fn {function}_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {{\n"
                           + indent("\n".join(lines)) + "\n}\n")
        return "\n".join(definitions)

    def emit(self):
        m = self.module
        bundled = isinstance(m, dict) and "kind" in m
        keys(m, "version kind methods programs" if bundled else "version name inputs output body methods", "module")
        if type(m["version"]) is not int or m["version"] != 2:
            fail("version", "module.version", "expected v2")
        if bundled and (m["kind"] != "u64-shared-library" or self.mode != "u64"):
            fail("bundle_mode", "module", "only the U64 shared-library bundle is supported")
        methods = array(m["methods"], "module.methods")
        scope, seen, sections = [], set(), ["use witgen_native::typed;\n"]
        for ordinal, method in enumerate(methods):
            path = f"module.methods[{ordinal}]"
            keys(method, "name args result body", path)
            original = name(method["name"], path + ".name")
            if original in seen:
                fail("duplicate_method", path, "duplicate method name")
            seen.add(original)
            args, result = self.types(method["args"], path + ".args"), self.ty(method["result"], path + ".result")
            sections.append(f"// method {ordinal}: {json.dumps(original, ensure_ascii=True)}\n"
                            + self.function(f"fn method_{ordinal}", args, result, method["body"], scope, path + ".body"))
            scope.append((ordinal, original, args, result))
        programs = array(m["programs"], "module.programs") if bundled else [m]
        program_names = set()
        for ordinal, program in enumerate(programs):
            base = f"module.programs[{ordinal}]" if bundled else "module"
            if bundled:
                keys(program, "name inputs output body", base)
            original = name(program["name"], base + ".name")
            if original in program_names:
                fail("duplicate_program", base, "duplicate program name")
            program_names.add(original)
            inputs, input_names = [], set()
            for i, entry in enumerate(array(program["inputs"], base + ".inputs")):
                path = f"{base}.inputs[{i}]"
                keys(entry, "name type", path)
                inp = name(entry["name"], path + ".name")
                if inp in input_names:
                    fail("duplicate_input", path, "duplicate input name")
                input_names.add(inp)
                inputs.append(self.ty(entry["type"], path + ".type"))
            output = self.ty(program["output"], base + ".output")
            if self.mode == "u64" and any(contains_nat(t) for t in inputs + [output]):
                fail("unbounded_nat", base, "U64 ABI accepts no external Nat inputs/results")
            symbol = f"program_{ordinal}" if bundled else "run"
            sections.append("// program: " + json.dumps(original, ensure_ascii=True) + "\n"
                            + self.function(f"pub fn {symbol}", inputs, output, program["body"], scope, base + ".body"))
            sections.append(self.json_boundary(inputs, output, symbol, symbol + "_" if bundled else ""))
        if bundled:
            arms = [f"{i} => program_{i}_json(inputs)," for i in range(len(programs))]
            arms.append("_ => Err(witgen_native::Error::UnknownProgram(program.to_string())),")
            sections.append("pub fn run_json(program: usize, inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {\n"
                            + indent("match program {\n" + indent("\n".join(arms)) + "\n}") + "\n}\n")
        source = "\n".join(sections[1:])
        # Receipts are line comments; a user's name must not create an import use.
        if any("typed::" in line for line in source.splitlines() if not line.lstrip().startswith("//")):
            source = sections[0] + "\n" + source
        return source


def emit_module(module: dict, mode: str) -> str:
    """Validate the entire actual module and emit one non-inlined method library."""
    try:
        return Emitter(module, mode).emit()
    except RecursionError:
        raise EmitError("depth", "module", "IR nesting exceeds compiler limit") from None
