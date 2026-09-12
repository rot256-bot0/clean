#!/usr/bin/env python3
"""Typed, fail-closed Rust emission for the prototype's exported IR.

This text emitter is tested infrastructure, not part of the Lean kernel proof.
"""

import re


class EmitError(ValueError):
    pass


BN254_MODULUS = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def cell_backend(field):
    """Explicit native cell backends; field identifiers are never normalized."""
    if type(field) is int and field in {17, 257}:
        return f"f{field}", f"witgen_native::F{field}"
    if field == "bn254":
        return "bn254", "witgen_native::Bn254Scalar"
    raise EmitError("unsupported witness cell field")


KEYWORDS = {
    "as",
    "break",
    "const",
    "continue",
    "crate",
    "else",
    "enum",
    "extern",
    "false",
    "fn",
    "for",
    "if",
    "impl",
    "in",
    "let",
    "loop",
    "match",
    "mod",
    "move",
    "mut",
    "pub",
    "ref",
    "return",
    "self",
    "Self",
    "static",
    "struct",
    "super",
    "trait",
    "true",
    "type",
    "unsafe",
    "use",
    "where",
    "while",
    "async",
    "await",
    "dyn",
    "abstract",
    "become",
    "box",
    "do",
    "final",
    "macro",
    "override",
    "priv",
    "typeof",
    "unsized",
    "virtual",
    "yield",
    "try",
    "union",
}


def identifier(value):
    if (
        not isinstance(value, str)
        or value == "_"
        or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", value)
        or value in KEYWORDS
    ):
        raise EmitError(f"invalid Rust identifier: {value!r}")
    return value


class RustEmitter:
    def __init__(self, module):
        if type(module.get("version")) is not int or module.get("version") != 1:
            raise EmitError("unsupported IR version")
        if module.get("domain") not in {"field17", "bn254", "nat", "word"}:
            raise EmitError("unsupported scalar domain")
        layout = module.get("wire_layout")
        bn254_cells = isinstance(layout, dict) and layout.get("field") == "bn254"
        if module.get("domain") == "bn254" or module.get("input_semantics") == "bn254" or bn254_cells:
            if module.get("field_modulus") != str(BN254_MODULUS):
                raise EmitError("BN254 requires its exact decimal scalar modulus")
            if module["domain"] == "word":
                raise EmitError("BN254 field values do not fit in one u64")
        self.module = module
        self.domain = module["domain"]
        self.is_field = self.domain in {"field17", "bn254"}
        self.records = {}
        self.used = set()
        self.counter = 0

    def rust_type(self, ty):
        if ty == "scalar":
            return {
                "field17": "witgen_native::F17",
                "bn254": "witgen_native::Bn254Scalar",
                "nat": "rug::Integer",
                "word": "u64",
            }[self.domain]
        if ty == "bool":
            return "bool"
        if isinstance(ty, dict) and set(ty) == {"list"}:
            return f"Vec<{self.rust_type(ty['list'])}>"
        if isinstance(ty, dict) and set(ty) == {"record", "fields"}:
            name = identifier(ty["record"])
            fields = ty["fields"]
            if not isinstance(fields, list) or not fields:
                raise EmitError("record needs a nonempty declared field list")
            names = [identifier(f["name"]) for f in fields]
            if len(names) != len(set(names)):
                raise EmitError("duplicate record fields")
            if name in self.records and self.records[name] != ty:
                raise EmitError("conflicting record type declarations")
            for field in fields:
                self.rust_type(field["type"])
            self.records[name] = ty
            return name
        raise EmitError(f"unsupported type: {ty!r}")

    def fresh(self):
        while True:
            name = f"_wg{self.counter}"
            self.counter += 1
            if name not in self.used:
                self.used.add(name)
                return name

    def reference(self, index, env):
        if (
            isinstance(index, bool)
            or not isinstance(index, int)
            or index < 0
            or index >= len(env)
        ):
            raise EmitError(f"reference {index!r} is outside its scope")
        return env[index]

    def copy(self, expr, ty):
        return (
            expr
            if ty == "bool" or (ty == "scalar" and self.domain != "nat")
            else f"({expr}).clone()"
        )

    @staticmethod
    def indent(text):
        return "\n".join("    " + line for line in text.splitlines())

    def region(self, region, env, expected):
        if (
            region.get("inputs") != [ty for _, ty in env]
            or region.get("output") != expected
        ):
            raise EmitError("region signature mismatch")
        lines, value, ty = self.block(region["body"], env)
        if ty != expected:
            raise EmitError("region body return type mismatch")
        return "{\n" + self.indent("\n".join(lines + [value])) + "\n}"

    def literal(self, value):
        if isinstance(value, bool) or not re.fullmatch(r"[0-9]+", str(value)):
            raise EmitError("constant must be a nonnegative decimal integer")
        n = int(value)
        if self.domain == "nat":
            return f'witgen_native::nat_from_str("{n}")?'
        if self.domain == "bn254":
            return f'witgen_native::bn254_from_str("{n % BN254_MODULUS}")?'
        limit = 17 if self.domain == "field17" else 2**64
        # Static const follows Field17.ofNat / UInt64.ofNat, not input decoding.
        n %= limit
        return (
            f"witgen_native::f17_from_u64({n}_u64)?"
            if self.domain == "field17"
            else f"{n}_u64"
        )

    def block(self, term, env):
        if not isinstance(term, dict):
            raise EmitError("block must be an object")
        if term.get("tag") == "ret":
            expr, ty = self.reference(term.get("ref"), env)
            return [], self.copy(expr, ty), ty
        if term.get("tag") != "let":
            raise EmitError("unknown block constructor")
        regions = term.get("regions")
        if not isinstance(regions, list):
            raise EmitError("regions must be explicitly declared")
        arguments = term.get("args")
        if not isinstance(arguments, list):
            raise EmitError("argument references must be a list")
        refs = [self.reference(i, env) for i in arguments]
        if "arg_types" in term and term["arg_types"] != [ty for _, ty in refs]:
            raise EmitError("declared argument types differ from references")
        result = term.get("result")
        self.rust_type(result)
        op = term.get("op")
        if not isinstance(op, str):
            raise EmitError("operation tag must be a string")
        static = term.get("static", {})
        allowed_static = (
            {"value"}
            if op in {"field.const", "nat.const", "word.const"}
            else ({"index"} if op in {"record.get", "record.set"} else set())
        )
        if not isinstance(static, dict) or set(static) - allowed_static:
            raise EmitError("unexpected static operation parameters")
        prefix = {"field17": "field", "bn254": "field", "nat": "nat", "word": "word"}[self.domain]
        arithmetic = {prefix + ".add", prefix + ".mul"}
        if not self.is_field:
            arithmetic |= {prefix + ".div", prefix + ".mod"}
        if op == "control.branch":
            if not refs or refs[0][1] != "bool" or len(regions) != 2:
                raise EmitError("branch signature mismatch")
            yes = self.region(regions[0], refs[1:], result)
            no = self.region(regions[1], refs[1:], result)
            value = f"if {refs[0][0]} {yes} else {no}"
        elif op == "control.map":
            if (
                not refs
                or not isinstance(refs[0][1], dict)
                or set(refs[0][1]) != {"list"}
                or len(regions) != 1
            ):
                raise EmitError("map input signature mismatch")
            if not isinstance(result, dict) or set(result) != {"list"}:
                raise EmitError("map must return a list")
            xs, list_ty = refs[0]
            element = self.fresh()
            vector = self.fresh()
            body = self.region(
                regions[0], [(element, list_ty["list"])] + refs[1:], result["list"]
            )
            loop = (
                f"for {element} in {xs}.iter().cloned() {{\n"
                + self.indent(f"{vector}.push({body});")
                + "\n}"
            )
            value = (
                "{\n"
                + self.indent(
                    f"let mut {vector}: {self.rust_type(result)} = Vec::with_capacity({xs}.len());\n{loop}\n{vector}"
                )
                + "\n}"
            )
        elif op == "control.fold":
            if (
                len(refs) < 2
                or not isinstance(refs[0][1], dict)
                or set(refs[0][1]) != {"list"}
                or len(regions) != 1
            ):
                raise EmitError("fold input signature mismatch")
            if result != refs[1][1]:
                raise EmitError("fold accumulator/result type mismatch")
            xs, list_ty = refs[0]
            element = self.fresh()
            acc = self.fresh()
            body = self.region(
                regions[0],
                [(element, list_ty["list"]), (acc, result)] + refs[2:],
                result,
            )
            loop = (
                f"for {element} in {xs}.iter().cloned() {{\n"
                + self.indent(f"{acc} = {body};")
                + "\n}"
            )
            value = (
                "{\n"
                + self.indent(
                    f"let mut {acc}: {self.rust_type(result)} = {self.copy(refs[1][0], result)};\n{loop}\n{acc}"
                )
                + "\n}"
            )
        elif regions:
            raise EmitError("unexpected regions on first-order operation")
        elif op == "list.empty":
            if refs or not isinstance(result, dict) or set(result) != {"list"}:
                raise EmitError("empty-list signature mismatch")
            value = "Vec::new()"
        elif op == "list.push":
            if (
                len(refs) != 2
                or refs[0][1] != result
                or not isinstance(result, dict)
                or set(result) != {"list"}
                or refs[1][1] != result["list"]
            ):
                raise EmitError("list-push signature mismatch")
            vector = self.fresh()
            value = (
                "{\n"
                + self.indent(
                    f"let mut {vector} = {self.copy(refs[0][0], result)};\n{vector}.push({self.copy(refs[1][0], result['list'])});\n{vector}"
                )
                + "\n}"
            )
        elif op == prefix + ".const":
            if refs or result != "scalar":
                raise EmitError("constant operation signature mismatch")
            value = self.literal(term.get("static", {}).get("value"))
        elif op == prefix + ".eq":
            if [ty for _, ty in refs] != ["scalar", "scalar"] or result != "bool":
                raise EmitError("equality operation signature mismatch")
            value = f"{refs[0][0]} == {refs[1][0]}"
        elif op in arithmetic:
            if [ty for _, ty in refs] != ["scalar", "scalar"] or result != "scalar":
                raise EmitError("arithmetic operation signature mismatch")
            suffix = op.split(".")[1]
            method = {"field17": "f17", "bn254": "bn254", "nat": "nat", "word": "word"}[self.domain] + "_" + suffix
            a, b = refs[0][0], refs[1][0]
            if self.domain == "nat":
                a, b = "&" + a, "&" + b
            checked = "?" if suffix in {"div", "mod"} else ""
            value = f"witgen_native::{method}({a}, {b}){checked}"
        elif op == "record.make":
            if not isinstance(result, dict) or "record" not in result:
                raise EmitError("record constructor must return a record")
            fields = result["fields"]
            if [ty for _, ty in refs] != [f["type"] for f in fields]:
                raise EmitError("record constructor signature mismatch")
            assignments = ", ".join(
                f"{f['name']}: {self.copy(expr, ty)}"
                for f, (expr, ty) in zip(fields, refs)
            )
            value = f"{result['record']} {{ {assignments} }}"
        elif op in {"record.get", "record.set"}:
            if (
                len(refs) != (1 if op == "record.get" else 2)
                or not isinstance(refs[0][1], dict)
                or "record" not in refs[0][1]
            ):
                raise EmitError("record projection input mismatch")
            index = term.get("static", {}).get("index")
            fields = refs[0][1]["fields"]
            if (
                isinstance(index, bool)
                or not isinstance(index, int)
                or not 0 <= index < len(fields)
            ):
                raise EmitError("record projection index out of range")
            field = fields[index]
            if op == "record.get":
                if result != field["type"]:
                    raise EmitError("record projection result mismatch")
                value = self.copy(f"{refs[0][0]}.{field['name']}", result)
            else:
                if result != refs[0][1] or refs[1][1] != field["type"]:
                    raise EmitError("record update value/result type mismatch")
                updated = self.fresh()
                value = "{\n" + self.indent(
                    f"let mut {updated} = {self.copy(refs[0][0], result)};\n"
                    f"{updated}.{field['name']} = {self.copy(refs[1][0], field['type'])};\n"
                    f"{updated}"
                ) + "\n}"
        else:
            raise EmitError(f"unsupported feature operation: {op!r}")
        name = self.fresh()
        rest, out, out_ty = self.block(term["next"], [(name, result)] + env)
        return [f"let {name}: {self.rust_type(result)} = {value};"] + rest, out, out_ty

    def scalar_paths(self, ty, prefix=(), output_length=None):
        if ty == "scalar":
            return [prefix]
        if isinstance(ty, dict) and "record" in ty:
            return [
                path
                for field in ty["fields"]
                for path in self.scalar_paths(field["type"], prefix + (field["name"],))
            ]
        if isinstance(ty, dict) and set(ty) == {"list"} and not prefix:
            if type(output_length) is not int or output_length < 0:
                raise EmitError("list witness output needs an explicit fixed length")
            return [
                path
                for i in range(output_length)
                for path in self.scalar_paths(ty["list"], (i,))
            ]
        raise EmitError("unsupported witness result layout")

    def emit_writer(self):
        layout = self.module.get("wire_layout")
        if layout is None:
            return ""
        cell_field = layout.get("field")
        cell_prefix, cell_type = cell_backend(cell_field)
        if self.domain == "field17" and cell_field != 17:
            raise EmitError("field17 generator needs field17 cells")
        if self.domain == "bn254" and cell_field != "bn254":
            raise EmitError("BN254 generator needs BN254 cells")
        if cell_field == "bn254" and self.domain == "word":
            raise EmitError("BN254 cells need a full-width representation, not one u64")
        count, outputs = layout.get("cells"), layout.get("outputs")
        if type(count) is not int or count < 1 or not isinstance(outputs, list):
            raise EmitError("invalid witness buffer/output declaration")
        bindings = layout.get("input_bindings")
        if bindings is None:
            slots = layout.get("input_slots")
            if not isinstance(slots, list):
                raise EmitError("wire input bindings missing")
            bindings = [{"slot": slot} for slot in slots]
        elif "input_slots" in layout:
            raise EmitError("use one input-binding representation")
        if not isinstance(bindings, list) or len(bindings) != len(
            self.module["inputs"]
        ):
            raise EmitError("wire input/output arity mismatch")
        typed = []
        for parameter, binding in zip(self.module["inputs"], bindings):
            ty = parameter["type"]
            if not isinstance(binding, dict):
                raise EmitError("invalid input binding")
            if ty in ("scalar", "bool") and set(binding) == {"slot"}:
                typed.append((ty, [binding["slot"]]))
            elif (
                ty == {"list": "scalar"}
                and set(binding) == {"slots"}
                and isinstance(binding["slots"], list)
            ):
                typed.append((ty, binding["slots"]))
            else:
                raise EmitError("unsupported structured input binding")
        inputs = [slot for _, slots in typed for slot in slots]
        slots = inputs + [item.get("slot") for item in outputs]
        if any(type(i) is not int or not 0 <= i < count for i in slots):
            raise EmitError("wire slot out of bounds")
        if len(slots) != len(set(slots)) or set(slots) != set(range(count)):
            raise EmitError(
                "wire binding must cover each input/witness cell exactly once"
            )
        paths = []
        for item in outputs:
            path = item.get("path")
            if not isinstance(path, list) or any(
                not (isinstance(x, str) or type(x) is int) for x in path
            ):
                raise EmitError("invalid output projection path")
            paths.append(tuple(path))
        expected = self.scalar_paths(
            self.module["output"], output_length=layout.get("output_length")
        )
        if len(paths) != len(set(paths)) or set(paths) != set(expected):
            raise EmitError("wire outputs must cover result scalar fields exactly once")
        if self.module["name"] == "populate":
            raise EmitError("entry name collides with generated writer")
        policy = layout.get("policy")
        if policy not in {None, "modmul_small", "batch3"}:
            raise EmitError("unknown circuit input policy")
        if cell_field == 257 and policy != "modmul_small":
            raise EmitError("field257 prototype requires modmul input policy")
        if policy == "modmul_small" and (
            cell_field != 257 or [t for t, _ in typed] != ["scalar"] * 3
        ):
            raise EmitError("modmul policy requires three scalar inputs")
        if policy == "batch3" and (
            cell_field != 17
            or count != 11
            or typed
            != [("bool", [0]), ({"list": "scalar"}, [1, 2, 3]), ("scalar", [4])]
            or layout.get("output_length") != 3
        ):
            raise EmitError("batch3 policy/layout mismatch")
        lines = []

        def raw(slot):
            conversion = "to_nat" if cell_field == "bn254" else "to_u64"
            return f"witgen_native::{cell_prefix}_{conversion}(cells[{slot}])"

        def scalar(slot):
            if self.is_field:
                return f"cells[{slot}]"
            return (
                f"rug::Integer::from({raw(slot)})"
                if self.domain == "nat"
                else raw(slot)
            )

        args = []
        for i, (ty, positions) in enumerate(typed):
            if ty == "bool":
                lines.append(f"let _bit{i} = {raw(positions[0])};")
                lines.append(
                    f'if _bit{i} > 1 {{ return Err(witgen_native::Error::NonBooleanCell {{ slot: {positions[0]} }}); }}'
                )
                args.append(f"_bit{i} == 1")
            elif ty == "scalar":
                args.append(scalar(positions[0]))
            else:
                args.append(
                    "vec![" + ", ".join(scalar(slot) for slot in positions) + "]"
                )
        if policy == "modmul_small":
            lines += [f"let _raw{i} = {raw(slot)};" for i, slot in enumerate(inputs)]
            lines.append(
                'if _raw2 == 0 || _raw2 > 16 || _raw0 >= _raw2 || _raw1 >= _raw2 { return Err(witgen_native::Error::CircuitAssumptions { circuit: "modmul" }); }'
            )
        lines.append(f"let result = {self.module['name']}({', '.join(args)})?;")
        if isinstance(self.module["output"], dict) and "list" in self.module["output"]:
            lines.append(
                f'if result.len() != {layout["output_length"]} {{ return Err(witgen_native::Error::WitnessLength {{ expected: {layout["output_length"]}, actual: result.len() }}); }}'
            )
        for i, path in enumerate(paths):
            value = "result"
            for part in path:
                value += f"[{part}]" if type(part) is int else "." + identifier(part)
            converted = (
                value
                if self.is_field
                else (
                    f"witgen_native::{cell_prefix}_from_nat(&{value})?"
                    if self.domain == "nat"
                    else f"witgen_native::{cell_prefix}_from_u64({value})?"
                )
            )
            lines.append(f"let _cell{i} = {converted};")
        # Validate every result and encoder before touching any reserved cell.
        lines.extend(
            f"cells[{item['slot']}] = _cell{i};" for i, item in enumerate(outputs)
        )
        lines.append("Ok(())")
        return (
            f"\npub fn populate(cells: &mut [{cell_type}; {count}]) -> witgen_native::Result<()> {{\n"
            + self.indent("\n".join(lines))
            + "\n}\n"
        )

    def emit(self):
        name = identifier(self.module.get("name"))
        inputs = self.module.get("inputs")
        if not isinstance(inputs, list):
            raise EmitError("inputs must be declared")
        env = [(identifier(p["name"]), p["type"]) for p in inputs]
        if len({n for n, _ in env}) != len(env):
            raise EmitError("duplicate input names")
        self.used.update(n for n, _ in env)
        params = ", ".join(f"{n}: {self.rust_type(t)}" for n, t in env)
        output = self.module["output"]
        output_type = self.rust_type(output)
        lines, value, result = self.block(self.module["body"], env)
        if result != output:
            raise EmitError("entry return type differs from declared output")
        declarations = []
        for record in self.records.values():
            fields = "\n".join(
                f"    pub {f['name']}: {self.rust_type(f['type'])},"
                for f in record["fields"]
            )
            declarations.append(
                f"#[derive(Clone, Debug)]\npub struct {record['record']} {{\n{fields}\n}}"
            )
        body = self.indent("\n".join(lines + [f"Ok({value})"]))
        return (
            "// Generated from typed witness IR. Do not hand-edit.\n\n"
            + "\n\n".join(declarations)
            + f"\n\npub fn {name}({params}) -> witgen_native::Result<{output_type}> {{\n{body}\n}}\n"
            + self.emit_writer()
        )


def emit_module(module):
    return RustEmitter(module).emit()
