#!/usr/bin/env python3
"""Build a Rust source bundle from the real Lean export manifest."""

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from emit_rust import EmitError, emit_module, identifier, cell_backend

ROOT = Path(__file__).resolve().parents[1]


def rust_type(ty, domain, module):
    if ty == "scalar":
        return {"field17": "witgen_native::F17", "bn254": "witgen_native::Bn254Scalar", "nat": "rug::Integer", "word": "u64"}[
            domain
        ]
    if ty == "bool":
        return "bool"
    if isinstance(ty, dict) and "list" in ty:
        return "Vec<" + rust_type(ty["list"], domain, module) + ">"
    return module + "::" + identifier(ty["record"])


def parse_expr(value, ty, domain, semantic, module, depth=0):
    if ty == "scalar":
        natural = f"parse_scalar({value}, {json.dumps(semantic)})?"
        if domain == "nat":
            return natural
        method = {"field17": "f17_from_nat", "bn254": "bn254_from_nat", "word": "word_from_nat"}[domain]
        return f"witgen_native::{method}(&{natural})?"
    if ty == "bool":
        return (
            f'({value}).as_bool().ok_or(witgen_native::Error::InvalidInputType {{ expected: "Boolean" }})?'
        )
    if isinstance(ty, dict) and "list" in ty:
        variable = f"item_{depth}"
        item = parse_expr(variable, ty["list"], domain, semantic, module, depth + 1)
        item_type = rust_type(ty["list"], domain, module)
        return f'({value}).as_array().ok_or(witgen_native::Error::InvalidInputType {{ expected: "array" }})?.iter().map(|{variable}| -> witgen_native::Result<{item_type}> {{ Ok({item}) }}).collect::<witgen_native::Result<Vec<_>>>()?'
    fields = []
    for field in ty["fields"]:
        key = identifier(field["name"])
        child = f'({value}).get({json.dumps(key)}).ok_or(witgen_native::Error::MissingField({json.dumps(key)}))?'
        fields.append(
            key
            + ": "
            + parse_expr(child, field["type"], domain, semantic, module, depth + 1)
        )
    return module + "::" + identifier(ty["record"]) + " { " + ", ".join(fields) + " }"


def value_json(reference, ty, domain, depth=0):
    if ty == "scalar":
        if domain == "bn254":
            return f"serde_json::Value::String(witgen_native::bn254_to_decimal(*({reference})))"
        value = (
            f"witgen_native::f17_to_u64(*({reference})).to_string()"
            if domain == "field17"
            else f"({reference}).to_string()"
        )
        return f"serde_json::Value::String({value})"
    if ty == "bool":
        return f"serde_json::Value::Bool(*({reference}))"
    if isinstance(ty, dict) and "list" in ty:
        variable = f"output_{depth}"
        item = value_json(variable, ty["list"], domain, depth + 1)
        return f"serde_json::Value::Array(({reference}).iter().map(|{variable}| {item}).collect())"
    fields = []
    for field in ty["fields"]:
        name = identifier(field["name"])
        value = value_json(f"&({reference}).{name}", field["type"], domain, depth + 1)
        fields.append(json.dumps(name) + ": " + value)
    return "serde_json::json!({" + ", ".join(fields) + "})"


def dispatch_arm(key, module):
    domain = module["domain"]
    semantic = module.get(
        "input_semantics", domain if domain in {"field17", "bn254"} else "nat"
    )
    if semantic not in {"field17", "bn254", "nat"}:
        raise EmitError("unsupported logical input contract")
    count = len(module["inputs"])
    lines = [
        f'if inputs.len() != {count} {{ return Err(witgen_native::Error::InputArity {{ expected: {count}, actual: inputs.len() }}); }}'
    ]
    layout = module.get("wire_layout")
    if layout is not None:
        prime = layout["field"]
        cell_prefix, cell_type = cell_backend(prime)
        size = layout["cells"]
        lines.append(f"let mut cells = [{cell_type}::from(0u64); {size}];")
        bindings = layout.get("input_bindings")
        if bindings is None:
            bindings = [{"slot": slot} for slot in layout["input_slots"]]
        for index, (parameter, binding) in enumerate(zip(module["inputs"], bindings)):
            ty = parameter["type"]
            if ty == "bool":
                flag = f"_flag{index}"
                lines.append(
                    f'let {flag} = inputs[{index}].as_bool().ok_or(witgen_native::Error::InvalidInputType {{ expected: "Boolean" }})?;'
                )
                lines.append(
                    f"cells[{binding['slot']}] = {cell_type}::from(if {flag} {{1u64}} else {{0u64}});"
                )
            elif ty == "scalar":
                lines.append(
                    f"cells[{binding['slot']}] = witgen_native::{cell_prefix}_from_nat(&parse_scalar(&inputs[{index}], {json.dumps(semantic)})?)?;"
                )
            else:
                array = f"_array{index}"
                slots = binding["slots"]
                lines.append(
                    f'let {array} = inputs[{index}].as_array().ok_or(witgen_native::Error::InvalidInputType {{ expected: "array" }})?;'
                )
                lines.append(
                    f'if {array}.len() != {len(slots)} {{ return Err(witgen_native::Error::InputLength {{ expected: {len(slots)}, actual: {array}.len() }}); }}'
                )
                for item, slot in enumerate(slots):
                    lines.append(
                        f"cells[{slot}] = witgen_native::{cell_prefix}_from_nat(&parse_scalar(&{array}[{item}], {json.dumps(semantic)})?)?;"
                    )
        lines.append(f"{key}::populate(&mut cells)?;")
        output_converter = f"{cell_prefix}_to_decimal" if prime == "bn254" else f"{cell_prefix}_to_u64"
        lines.append(
            f'Ok(serde_json::json!({{"program": {json.dumps(key)}, "cells": cells.into_iter().map(witgen_native::{output_converter}).collect::<Vec<_>>()}}))'
        )
    else:
        args = [
            parse_expr(f"&inputs[{i}]", item["type"], domain, semantic, key)
            for i, item in enumerate(module["inputs"])
        ]
        lines.append(
            f"let result = {key}::{identifier(module['name'])}({', '.join(args)})?;"
        )
        output = value_json("&result", module["output"], domain)
        lines.append(
            f'Ok(serde_json::json!({{"program": {json.dumps(key)}, "value": {output}}}))'
        )
    return json.dumps(key) + " => {\n" + "\n".join("    " + x for x in lines) + "\n}"


def build(directory, *, generated_subdir="generated", binary=None):
    identifier(generated_subdir)
    if binary is not None and not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_-]*", binary):
        raise EmitError("invalid native binary name")
    manifest = json.loads((directory / "manifest.json").read_text())
    names = manifest["programs"]
    if not isinstance(names, list) or len(names) != len(set(names)):
        raise EmitError("invalid program manifest")
    output = ROOT / "backend/src" / generated_subdir
    output.mkdir(parents=True, exist_ok=True)
    arms = []
    receipts = []
    for name in names:
        identifier(name)
        raw = (directory / (name + ".json")).read_bytes()
        module = json.loads(raw)
        code = emit_module(module)
        (output / (name + ".rs")).write_text(code)
        arms.append(dispatch_arm(name, module))
        receipts.append(
            {
                "program": name,
                "ir_sha256": hashlib.sha256(raw).hexdigest(),
                "rust_sha256": hashlib.sha256(code.encode()).hexdigest(),
            }
        )
    declarations = "\n".join("pub mod " + name + ";" for name in names)
    helpers = r"""
fn parse_scalar(value: &serde_json::Value, semantic: &str) -> witgen_native::Result<rug::Integer> {
    let text = if let Some(s) = value.as_str() {
        s.to_string()
    } else if let Some(n) = value.as_u64() {
        n.to_string()
    } else {
        return Err(witgen_native::Error::InvalidInputType { expected: "nonnegative decimal integer" });
    };
    let n = witgen_native::nat_from_str(&text)?;
    if semantic == "field17" && n >= 17 {
        return Err(witgen_native::Error::NonCanonicalField { field: "field17" });
    }
    if semantic == "bn254" && n >= witgen_native::bn254_modulus() {
        return Err(witgen_native::Error::NonCanonicalField { field: "bn254" });
    }
    Ok(n)
}
"""
    dispatch = (
        "\npub fn dispatch(program: &str, inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {\n match program {\n"
        + ",\n".join(arms)
        + ',\n _ => Err(witgen_native::Error::UnknownProgram(program.to_owned())),\n }\n}\n'
    )
    (output / "mod.rs").write_text(
        "// Generated typed-program dispatch.\n" + declarations + helpers + dispatch
    )
    main = r"""mod generated;
use std::io::{self, BufRead};

fn run(request: &serde_json::Value) -> witgen_native::Result<serde_json::Value> {
    let program = request.get("program").ok_or(witgen_native::Error::MissingField("program"))?;
    let name = program.as_str().ok_or(witgen_native::Error::InvalidInputType { expected: "program string" })?;
    let input = request.get("inputs").ok_or(witgen_native::Error::MissingField("inputs"))?;
    let inputs = input.as_array().ok_or(witgen_native::Error::InvalidInputType { expected: "inputs array" })?;
    generated::dispatch(name, inputs)
}

fn main() {
    for line in io::stdin().lock().lines() {
        let response = match line {
            Ok(text) => match serde_json::from_str::<serde_json::Value>(&text) {
                Ok(request) => run(&request),
                Err(error) => Err(witgen_native::Error::Json(error)),
            },
            Err(error) => Err(witgen_native::Error::Io(error)),
        };
        match response {
            Ok(value) => println!("{}", value),
            Err(error) => println!("{}", serde_json::json!({"error": error.to_string(), "error_code": error.code()})),
        }
    }
}
"""
    if binary is None:
        target = ROOT / "backend/src/main.rs"
        if generated_subdir != "generated":
            main = main.replace("mod generated;", f'#[path = "{generated_subdir}/mod.rs"]\nmod generated;', 1)
    else:
        target = ROOT / "backend/src/bin" / (binary + ".rs")
        main = main.replace("mod generated;", f'#[path = "../{generated_subdir}/mod.rs"]\nmod generated;', 1)
    target.parent.mkdir(exist_ok=True)
    target.write_text(main)
    subprocess.run(
        ["rustfmt", "--edition", "2021", str(target)],
        cwd=ROOT,
        check=True,
    )
    for receipt in receipts:
        actual = (output / (receipt["program"] + ".rs")).read_bytes()
        receipt["rust_sha256"] = hashlib.sha256(actual).hexdigest()
    (output / "receipt.json").write_text(json.dumps(receipts, indent=2) + "\n")
    print(
        json.dumps(
            {"emitted": len(names), "programs": names, "output": str(output)}, indent=2
        )
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    build(args.directory)
