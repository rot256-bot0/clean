#!/usr/bin/env python3
"""Build a Rust source bundle from the real Lean export manifest."""

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

from emit_rust import EmitError, emit_module, identifier

ROOT = Path(__file__).resolve().parents[1]


def rust_type(ty, domain, module):
    if ty == "scalar":
        return {"field17": "witgen_native::F17", "nat": "rug::Integer", "word": "u64"}[
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
        method = "f17_from_nat" if domain == "field17" else "word_from_nat"
        return f"witgen_native::{method}(&{natural})?"
    if ty == "bool":
        return (
            f'({value}).as_bool().ok_or_else(|| "expected Boolean input".to_string())?'
        )
    if isinstance(ty, dict) and "list" in ty:
        variable = f"item_{depth}"
        item = parse_expr(variable, ty["list"], domain, semantic, module, depth + 1)
        item_type = rust_type(ty["list"], domain, module)
        return f'({value}).as_array().ok_or_else(|| "expected array input".to_string())?.iter().map(|{variable}| -> Result<{item_type}, String> {{ Ok({item}) }}).collect::<Result<Vec<_>, String>>()?'
    fields = []
    for field in ty["fields"]:
        key = identifier(field["name"])
        child = f'({value}).get({json.dumps(key)}).ok_or_else(|| "missing record input field".to_string())?'
        fields.append(
            key
            + ": "
            + parse_expr(child, field["type"], domain, semantic, module, depth + 1)
        )
    return module + "::" + identifier(ty["record"]) + " { " + ", ".join(fields) + " }"


def value_json(reference, ty, domain, depth=0):
    if ty == "scalar":
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
        "input_semantics", "field17" if domain == "field17" else "nat"
    )
    if semantic not in {"field17", "nat"}:
        raise EmitError("unsupported logical input contract")
    count = len(module["inputs"])
    lines = [
        f'if inputs.len() != {count} {{ return Err("input arity mismatch".into()); }}'
    ]
    layout = module.get("wire_layout")
    if layout is not None:
        prime = layout["field"]
        size = layout["cells"]
        lines.append(f"let mut cells = [witgen_native::F{prime}::from(0u64); {size}];")
        bindings = layout.get("input_bindings")
        if bindings is None:
            bindings = [{"slot": slot} for slot in layout["input_slots"]]
        for index, (parameter, binding) in enumerate(zip(module["inputs"], bindings)):
            ty = parameter["type"]
            if ty == "bool":
                flag = f"_flag{index}"
                lines.append(
                    f'let {flag} = inputs[{index}].as_bool().ok_or_else(|| "expected Boolean input".to_string())?;'
                )
                lines.append(
                    f"cells[{binding['slot']}] = witgen_native::F{prime}::from(if {flag} {{1u64}} else {{0u64}});"
                )
            elif ty == "scalar":
                lines.append(
                    f"cells[{binding['slot']}] = witgen_native::f{prime}_from_nat(&parse_scalar(&inputs[{index}], {json.dumps(semantic)})?)?;"
                )
            else:
                array = f"_array{index}"
                slots = binding["slots"]
                lines.append(
                    f'let {array} = inputs[{index}].as_array().ok_or_else(|| "expected array input".to_string())?;'
                )
                lines.append(
                    f'if {array}.len() != {len(slots)} {{ return Err("input array length differs from circuit layout".into()); }}'
                )
                for item, slot in enumerate(slots):
                    lines.append(
                        f"cells[{slot}] = witgen_native::f{prime}_from_nat(&parse_scalar(&{array}[{item}], {json.dumps(semantic)})?)?;"
                    )
        lines.append(f"{key}::populate(&mut cells)?;")
        lines.append(
            f'Ok(serde_json::json!({{"program": {json.dumps(key)}, "cells": cells.into_iter().map(witgen_native::f{prime}_to_u64).collect::<Vec<_>>()}}))'
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


def build(directory):
    manifest = json.loads((directory / "manifest.json").read_text())
    names = manifest["programs"]
    if not isinstance(names, list) or len(names) != len(set(names)):
        raise EmitError("invalid program manifest")
    output = ROOT / "backend/src/generated"
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
fn parse_scalar(value: &serde_json::Value, semantic: &str) -> Result<rug::Integer, String> {
    let text = if let Some(s) = value.as_str() {
        s.to_string()
    } else if let Some(n) = value.as_u64() {
        n.to_string()
    } else {
        return Err("expected a nonnegative decimal integer".into());
    };
    let n = witgen_native::nat_from_str(&text)?;
    if semantic == "field17" && n >= 17 {
        return Err("source field17 input is not canonical".into());
    }
    Ok(n)
}
"""
    dispatch = (
        "\npub fn dispatch(program: &str, inputs: &[serde_json::Value]) -> Result<serde_json::Value, String> {\n match program {\n"
        + ",\n".join(arms)
        + ',\n _ => Err("unknown exported program".into()),\n }\n}\n'
    )
    (output / "mod.rs").write_text(
        "// Generated typed-program dispatch.\n" + declarations + helpers + dispatch
    )
    main = r"""mod generated;
use std::io::{self, BufRead};

fn run(request: &serde_json::Value) -> Result<serde_json::Value, String> {
    let name = request.get("program").and_then(|v| v.as_str()).ok_or("missing program")?;
    let inputs = request.get("inputs").and_then(|v| v.as_array()).ok_or("missing inputs")?;
    generated::dispatch(name, inputs)
}

fn main() {
    for line in io::stdin().lock().lines() {
        let response = match line {
            Ok(text) => match serde_json::from_str::<serde_json::Value>(&text) {
                Ok(request) => run(&request),
                Err(error) => Err(error.to_string()),
            },
            Err(error) => Err(error.to_string()),
        };
        match response {
            Ok(value) => println!("{}", value),
            Err(error) => println!("{}", serde_json::json!({"error": error})),
        }
    }
}
"""
    (ROOT / "backend/src/main.rs").write_text(main)
    subprocess.run(
        ["rustfmt", "--edition", "2021", str(ROOT / "backend/src/main.rs")],
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
