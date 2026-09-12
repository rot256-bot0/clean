#!/usr/bin/env python3
"""Refresh the code-first design document from the actual implementation."""
from pathlib import Path
import hashlib
import json

PACKAGE = Path(__file__).resolve().parents[1]
REPO = PACKAGE.parent
URL = "https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/"
receipts = []


def sample(relative, start=None, end=None, language="lean"):
    path = PACKAGE / relative
    source = path.read_text()
    first = source.index(start) if start else 0
    last = source.index(end, first) if end else len(source)
    text = source[first:last].rstrip()
    lo = source[:first].count("\n") + 1
    hi = lo + text.count("\n")
    receipts.append({"path": "witgen/" + relative, "start": lo, "end": hi,
                     "sha256": hashlib.sha256(text.encode()).hexdigest()})
    link = URL + "witgen/" + relative + f"#L{lo}-L{hi}"
    return f"[{relative}]({link})\n\n```{language}\n{text}\n```\n"


parts = ["""# Clean WitGen DSL

**Implementation reference.** Code blocks below are copied from the fork branch, not invented APIs. The new package is in `witgen/`; parent Clean's current circuit API/toolchain remain unchanged while this replacement is developed.

[Branch](https://github.com/rot256-bot0/clean/tree/feat/clean-witgen-dsl) · [Run instructions](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/README.md)

<details>
<summary>Contents</summary>

- [The Same Program, Different Targets](#1-the-same-program-different-targets)
- [Actual Rust Output](#2-actual-rust-output)
- [The Small Typed Core](#3-the-small-typed-core)
- [Proof-Bearing Lowering](#4-proof-bearing-lowering)
- [Map, Branch, and Records](#5-map-branch-and-records)
- [Circuits and Witness Cells](#6-circuits-and-witness-cells)
- [Verification and Limits](#7-verification-and-limits)

</details>

## 1. The Same Program, Different Targets

The source requests field arithmetic and record construction. `Has` chooses a typed feature embedding, not a native implementation.

""",
 sample("Witgen/Demo.lean", "def quadratic {", "theorem quadraticField_eval"),
 "The two arithmetic passes operate on that same AST:\n\n",
 sample("Witgen/Pipeline.lean", "def quadraticNat :", "theorem quadraticNat_correct"),
 "Field operations become target subprograms, including explicit modular reduction:\n\n",
 sample("Witgen/Pipeline.lean", "def fieldScalarToNat :", "def natScalarToWord :"),
 """
The backend receives different remaining features:

- Source Field17 program → arkworks field operations.
- Field → Nat lowering → GMP-backed `rug::Integer` operations.
- Field → Nat → bounded UInt64 lowering → word operations.

All three use the same circuit and full witness layout. The word theorem is conditional on representability; this is not arbitrary bignum arithmetic squeezed into one word.

## 2. Actual Rust Output

Each example returns a native record, then the generated `populate` adapter writes its fields into the reserved witness cells. Input cells stay unchanged. The code is generated from the AST above, not transcribed from its evaluated result.

### Direct Field Backend

""",
 sample("backend/src/generated/quadratic_field.rs", language="rust"),
 "\n### After Field → Nat: GMP Backend\n\n",
 sample("backend/src/generated/quadratic_nat.rs", language="rust"),
 "\n### After Field → Nat → UInt64\n\n",
 sample("backend/src/generated/quadratic_word.rs", language="rust"),
 """
For inputs `3,4`, every path fills `[3,4,9,13]`. The square is an actual witness cell, not an unexported local. A source-local `let` becomes a witness only through the explicit result/layout binding.

## 3. The Small Typed Core

The sort universe and feature signature are parameters. Records, words, lists, and control are in optional libraries, not kernel constructors. Return values are typed references; continuations and regions are finite syntax.

""",
 sample("Witgen/Core.lean", "structure RegionShape", "namespace Var"),
 sample("Witgen/Core.lean", "mutual\n  inductive Program", "abbrev Body"),
 """
Regions have explicit input contexts. Captures are passed as arguments, not hidden host closures. The optional demo library introduces actual record sorts and preserves their names/field order through Rust emission:

""",
 sample("Witgen/Demo.lean", "inductive Ty", "def Val.map"),
 """
## 4. Proof-Bearing Lowering

A template supplies a target **subprogram** for each source operation. `Template.Respects` proves that subprogram implements the original feature semantics, uniformly over related region bodies. The generic theorem lifts the local proof through the caller and its continuation.

""",
 sample("Witgen/Core.lean", "abbrev Template", "mutual\n  theorem Program.eval_lower_related"),
 sample("Witgen/Core.lean", "structure CertifiedLowering", "def CertifiedLowering.ofHandler"),
 "Manual composition preserves the intermediate representation relation. No automatic lowering planner is required.\n\n",
 sample("Witgen/Core.lean", "def CertifiedLowering.comp", "/-- Drop a formal result binder"),
 """
## 5. Map, Branch, and Records

Map may remain available to the Rust backend, or be lowered on the Lean side to Fold plus list construction. The body remains typed code with explicit captures.

""",
 sample("Witgen/Pipeline.lean", "def mapBodyToFold", "theorem mapBodyToFold_eval"),
 "The fixed-size gated circuit maps a branch-producing record body over three inputs:\n\n",
 sample("Witgen/Batch.lean", "def gatedQuad", "/-- Mathematical specification"),
 """
The generated Rust uses real `if` and `for` constructs. Both branches return three records; disabled execution writes all six zeros. A short return is rejected before indexing or writing, not padded with fabricated values.

- [Direct batch Rust](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated/batch_field.rs)
- [Map → Fold → Field → Nat → UInt64 Rust](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated/batch_fold_word.rs)

## 6. Circuits and Witness Cells

The circuit relation is independent of generator choice. A generator proves the **full** relation, including internal cells, rather than only the public output spec. Feature-relative completeness also fixes the boundary adapters: arbitrary host computation cannot be existentially hidden in a newly chosen encoder/decoder.

""",
 sample("Witgen/Circuits.lean", "structure Circuit", "namespace FormalWitgen"),
 "The compiled field generator is the actual program stored in the certificate:\n\n",
 sample("Witgen/Integration.lean", "def quadraticFieldWitgen", "theorem quadraticField_buffer"),
 """
Layouts are fixed and proved complete. Native encoders validate every output before any store. The three circuit families are:

- Quadratic over field17: input cells `0,1`; square/output cells `2,3`.
- Modular multiplication over field257: inputs `0,1,2`; product/quotient/remainder `3,4,5`.
- Gated batch: inputs `0..4`; three square/output pairs `5..10`.

The modular multiplication pattern uses `a*b = q*n+r` and `r<n`; the example is not full RSA signature verification. The GMP path additionally executes raw modular multiplication on 4096-bit inputs without claiming those values fit the small field257 circuit.

## 7. Verification and Limits

The native comparison suite checks the actual Lean reference interpreter against emitted Rust and separately checks every circuit cell: **7,472 cases across18 variants**. Wrong-slot, missing-cell, bad-length, noncanonical-input and dirty-disabled-buffer controls are included. An exact named axiom audit rejects empty/missing reports and permits only the documented standard foundations.

```sh
cd witgen
python3 tools/run_demo.py
python3 -m unittest discover -s tests -v
```

**Proved:** typed scope, feature/subprogram lowering, composed semantics, full circuit witnesses and the pure vector writer.

**Tested TCB:** JSON encoding/checking, Rust printing, rustfmt/rustc, arkworks/GMP and native execution. Native division rejects zero; equivalence is claimed on the declared nonzero-divisor domains.

**Current limits:** pure semantics, explicit-input regions, fixed abstract sort indices with representation changes through model relations, and no general bignum-to-word pass or arbitrary dynamic type/procedure registry. Parent Clean's current WitnessIR has not been replaced by this package yet.
"""]

output = REPO / "doc/witgen-dsl-design.md"
output.write_text("\n".join(parts))
(PACKAGE / "artifacts").mkdir(exist_ok=True)
(PACKAGE / "artifacts/design-snippets.json").write_text(json.dumps(receipts, indent=2) + "\n")
print(output)
