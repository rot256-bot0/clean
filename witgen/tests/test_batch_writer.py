import copy
import importlib.util
import json
import subprocess
import unittest
from pathlib import Path

from test_native_emitter import QUAD, quad_fixture

ROOT = Path(__file__).resolve().parents[1]
SEQ = {"list": "scalar"}
OUT = {"list": QUAD}


def batch_module():
    yes = {
        "tag": "let",
        "op": "control.map",
        "args": [0, 1],
        "result": OUT,
        "regions": [
            {
                "inputs": ["scalar", "scalar"],
                "output": QUAD,
                "body": quad_fixture()["body"],
            }
        ],
        "next": {"tag": "ret", "ref": 0},
    }
    zero = {
        "tag": "let",
        "op": "field.const",
        "args": [],
        "regions": [],
        "result": "scalar",
        "static": {"value": "0"},
        "next": {
            "tag": "let",
            "op": "record.make",
            "args": [0, 0],
            "regions": [],
            "result": QUAD,
            "next": {"tag": "ret", "ref": 0},
        },
    }
    no = {
        "tag": "let",
        "op": "control.map",
        "args": [0, 1],
        "result": OUT,
        "regions": [{"inputs": ["scalar", "scalar"], "output": QUAD, "body": zero}],
        "next": {"tag": "ret", "ref": 0},
    }
    return {
        "version": 1,
        "name": "generate",
        "domain": "field17",
        "input_semantics": "field17",
        "inputs": [
            {"name": "enabled", "type": "bool"},
            {"name": "xs", "type": SEQ},
            {"name": "c", "type": "scalar"},
        ],
        "output": OUT,
        "body": {
            "tag": "let",
            "op": "control.branch",
            "args": [0, 1, 2],
            "result": OUT,
            "regions": [
                {"inputs": [SEQ, "scalar"], "output": OUT, "body": yes},
                {"inputs": [SEQ, "scalar"], "output": OUT, "body": no},
            ],
            "next": {"tag": "ret", "ref": 0},
        },
        "wire_layout": {
            "field": 17,
            "cells": 11,
            "policy": "batch3",
            "output_length": 3,
            "input_bindings": [{"slot": 0}, {"slots": [1, 2, 3]}, {"slot": 4}],
            "outputs": [
                {"path": [i, name], "slot": 5 + 2 * i + j}
                for i in range(3)
                for j, name in enumerate(["square", "output"])
            ],
        },
    }


class BatchWriterTests(unittest.TestCase):
    def test_native_records_fill_every_batch_slot_and_reject_short_result(self):
        spec = importlib.util.spec_from_file_location(
            "emit_rust", ROOT / "tools/emit_rust.py"
        )
        assert spec is not None and spec.loader is not None
        emitter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(emitter)
        module = batch_module()
        try:
            good = emitter.emit_module(module)
        except ValueError as e:
            self.fail(f"structured batch writer missing: {e}")
        short = copy.deepcopy(module)
        short["body"]["regions"][1]["body"] = {
            "tag": "let",
            "op": "list.empty",
            "args": [],
            "regions": [],
            "result": OUT,
            "next": {"tag": "ret", "ref": 0},
        }
        bad = emitter.emit_module(short)
        main = """
fn main() {
 let mut cells=[1u64,3,4,16,4,7,7,7,7,7,7].map(witgen_native::F17::from);
 good::populate(&mut cells).unwrap();
 println!("{}",serde_json::json!(cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()));
 let mut disabled=[0u64,3,4,16,4,7,7,7,7,7,7].map(witgen_native::F17::from);
 good::populate(&mut disabled).unwrap();
 println!("{}",serde_json::json!(disabled.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()));
 let mut short=[0u64,3,4,16,4,7,7,7,7,7,7].map(witgen_native::F17::from);
 let old=short;assert!(bad::populate(&mut short).is_err());assert_eq!(short,old);
}
"""
        path = ROOT / "backend/src/bin/batch_writer_test.rs"
        path.write_text(
            "mod good {\n" + good + "\n}\nmod bad {\n" + bad + "\n}\n" + main
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
                "batch_writer_test",
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        rows = [json.loads(x) for x in result.stdout.splitlines()]
        self.assertEqual(
            rows,
            [[1, 3, 4, 16, 4, 9, 13, 16, 3, 1, 5], [0, 3, 4, 16, 4, 0, 0, 0, 0, 0, 0]],
        )


if __name__ == "__main__":
    unittest.main()
