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


def caliper_profiles():
    runtime = json.loads((PACKAGE / "examples/caliper/runtime.json").read_text())
    labels = {"quadratic": "Quadratic", "modMul": "Modular Multiplication",
              "fixedGated/on": "Two-Row Gated, Enabled",
              "fixedGated/off": "Two-Row Gated, Disabled"}
    lines = []
    observed = []
    for program in runtime["programs"]:
        assembly = PACKAGE / "examples/caliper" / (program["name"] + ".caliper")
        assert assembly.read_text() == program["assembly"] + "\n"
        cases = {}
        for run in program["runs"]:
            costs = cases.setdefault(run["case"], {})
            assert run["cost_model"] not in costs
            costs[run["cost_model"]] = run
        for case, costs in cases.items():
            assert set(costs) == {"unit", "cycles"}
            unit, cycles = costs["unit"], costs["cycles"]
            assert unit["cells"] == cycles["cells"]
            assert unit["net_words"] == cycles["net_words"]
            assert unit["peak_words"] == cycles["peak_words"]
            observed.append(case)
            lines.append(f"- **{labels[case]}:** `.unit` time {unit['time']}; "
                         f"`.cycles` time {cycles['time']}; net/peak buffer growth "
                         f"{unit['net_words']}/{unit['peak_words']} words; "
                         f"static register endpoint {program['next_register']}.")
    assert set(observed) == set(labels) and len(observed) == len(labels)
    return "\n".join(lines) + "\n"


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
- [Caliper Integration and Runtime Proofs](#7-caliper-integration-and-runtime-proofs)
- [Verification and Limits](#8-verification-and-limits)

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

## 7. Caliper Integration and Runtime Proofs

Caliper is a second **analysis target**, not the native execution engine. We lower the source features until only words, records, static lists and supported control remain; the Caliper backend then traverses that actual `Program WordSig` into `Caliper.Stmt 64`. The Rust backend remains separate.

### Compile the Program, Not a Handwritten Lookalike

The checked examples are extracted from `compile`; there is no failure fallback to unrelated code:

""",
 sample("Witgen/Backends/Caliper.lean", "def quadraticCompiled :", "/-- Constructor equality"),
 """
Input registers must be below the first fresh register. Records become register layouts. Map/fold unroll static lists, while branches emit `ifNZ` and copies into a common fresh result layout. Unequal branch-result shapes are rejected, including nested list mismatches. Field/Nat/GMP are not opaque Caliper precompiles: any such operation must first be lowered with its required representation proof.

Then append the full witness writer. The named buffer contains **inputs and every witness cell**, not just the public result:

""",
 sample("Witgen/Backends/CaliperExamples.lean", "def withWitness", "def quadraticTime"),
 "The complete generated quadratic program, rendered directly by pinned Caliper:\n\n",
 sample("examples/caliper/quadratic.caliper", language="text"),
 """
The zero-cost `skip` nodes are retained, not silently optimized away. Input registers `r0,r1` are preserved; the output layout copies `[r0,r1,r4,r7]` into buffer `b0`.

### Charge Allocation and Initialization

Reserving capacity does not initialize readable cells. The actual writer reserves an empty buffer and pushes each register value in layout order:

""",
 sample("Witgen/Backends/CaliperWitness.lean", "def pushRegs", "/-- The exact state transformer"),
 r"""
For a memory-neutral producer and a fresh output buffer of $n$ words, the proved composed cost is

$$
T_{\mathrm{full}} = T_{\mathrm{producer}}
 + C.\mathrm{memAlloc}
 + n\,C.\mathrm{allocPerWord}
 + n\,C.\mathrm{memPush}.
$$

`writeRegs_exec` proves the generic writer execution. `withWitness_exec` composes it with a producer's `Exec` theorem, full-cell correspondence, preserved input registers and buffer/tape frame. Net and peak **buffer-capacity growth** are both $n$; physical-memory claims additionally require a well-formed initial state. Loading from reserved-but-uninitialized storage is explicitly rejected.

### A Checked Runtime Proof

This complete Lean example specializes the generic quadratic certificate to Caliper's shipped `.cycles` cost table. It is compiled by the tests and included in the named axiom audit:

""",
 sample("Witgen/Backends/CaliperRuntimeGuide.lean"),
 """
`Triple C tape P code Q T D M` proves: every state satisfying `P` has a terminating `Exec` reaching `Q`, with time at most `T`, net capacity growth at most `D`, and peak growth at most `M`. Here the result includes the full buffer, unchanged inputs/other buffers/tape, and preserved well-formedness. The second theorem uses determinism to show the exact resource values for every completed run; an upper bound alone would not establish that.

The clock starts with inputs already in registers. It counts all emitted producer instructions and output allocation/population, but not Lean code generation, compilation, input parsing, or host ABI conversion. **The number 90 is an abstract Caliper charge, not a Rust runtime or a measured hardware cycle count.** Changing the cost table specializes the generic proof; it does not calibrate a real processor.

### Observed Runs and Proved Profiles

These profiles include **the complete producer plus input-and-witness buffer allocation and population**. The sample observations are exported by `Caliper.run`; the universal execution theorems above, not the sample runs, justify the program-wide claims:

""",
 caliper_profiles(),
 """
[All Assembly and Runtime Observations](https://github.com/rot256-bot0/clean/tree/feat/clean-witgen-dsl/witgen/examples/caliper)

Reproduce without compiling all of Mathlib to native code:

```sh
cd witgen
python3 tools/run_caliper.py
# Or export after building the imported Lean modules:
lake build Witgen.Backends.CaliperExamples
lake env lean --run MainCaliper.lean export artifacts/caliper
```

The verification runner builds the proof modules, directly rechecks the compiler/interpreter test files and axiom audit, requires every named theorem report, and checks the canonical quadratic and bounded modular-multiplication domains. Runtime JSON and assembly are tested serialization; proofs concern the actual `Stmt`, not the printer.

### Connect Runtime to Correct Witnesses

Runtime without a semantic link could certify a fast program computing the wrong thing. The current chain is:

1. The existing feature-lowering theorems relate the source program to its word program under explicit representation bounds.
2. `quadratic_run` / `modMul_run` prove the **actual compiler outputs** return the source word records, universally over input word values, initial scratch registers, tapes and cost models.
3. `quadratic_witness_exec` / `modMul_witness_exec` append the actual full-layout writer.
4. `quadratic_circuit_exec` / `modMul_circuit_exec` additionally prove that the Nat view of the **actual filled buffer** satisfies the unchanged circuit constraints, with the stated input-domain hypotheses.

For quadratic, the circuit claim requires canonical Field17 inputs. For modular multiplication it requires `0 < n ≤ 16`, `a < n`, `b < n`. The unrestricted word execution theorems cover wrapping arithmetic and totalized zero division, not an unrestricted Nat or circuit guarantee.

### Apply the Method to Another WitGen

Fix the source program, input domain, ABI and cost model. Prove each feature fallback preserves its unchanged semantics, then compile the resulting word AST with an explicit input layout. Prove preservation and an `Exec` resource formula for that **checked compiler result**; reuse the primitive correspondence lemmas, frame rules and `withWitness_exec`. Finally connect every copied witness cell to the circuit relation and derive a `Triple`.

For a variable-size family, parameterize the program/layout and prove a bound in its size parameter; checking one size or timing the reference interpreter is not an asymptotic proof. Static map/fold lowering is available, but **there is no generic whole-compiler preservation theorem yet**. Only the documented quadratic, modular-multiplication and fixed two-row gated artifacts currently have universal whole-program certificates. A new arbitrary program still needs that proof step.

The two-row gated artifact covers word semantics and both branches; it is **not** a proof for the separate three-row batch circuit. Dynamic output shapes, general runtime-length containers, arbitrary named subroutines and general bignum-to-word lowering are not supplied by this backend. Register endpoints are static namespaces, not liveness peaks; buffer-memory numbers exclude registers and are not total machine memory.

[Compiler API](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/docs/CaliperBackendAPI.md) · [Witness, Cost and Circuit Theorems](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/docs/CaliperCostAPI.md)

## 8. Verification and Limits

The native comparison suite checks the actual Lean reference interpreter against emitted Rust and separately checks every circuit cell: **7,472 cases across18 variants**. Wrong-slot, missing-cell, bad-length, noncanonical-input and dirty-disabled-buffer controls are included. An exact named axiom audit rejects empty/missing reports and permits only the documented standard foundations.

```sh
cd witgen
python3 tools/run_demo.py
python3 -m unittest discover -s tests -v
```

**Proved:** typed scope, feature/subprogram lowering, composed semantics, full circuit witnesses, the pure vector writer, and the scoped Caliper compiler-output/witness/cost theorems above. The core axiom audit permits `propext` and `Quot.sound`; the separate Caliper audit also permits standard `Classical.choice`. Neither permits `sorryAx`, custom axioms or `native_decide`/`trustCompiler`.

**Tested TCB:** JSON encoding/checking, Rust printing, rustfmt/rustc, arkworks/GMP and native execution. Native division rejects zero; equivalence is claimed on the declared nonzero-divisor domains.

**Current limits:** pure semantics, explicit-input regions, fixed abstract sort indices with representation changes through model relations, and no general bignum-to-word pass or arbitrary dynamic type/procedure registry. Parent Clean's current WitnessIR has not been replaced by this package yet.
"""]

output = REPO / "doc/witgen-dsl-design.md"
output.write_text("\n".join(parts))
(PACKAGE / "artifacts").mkdir(exist_ok=True)
(PACKAGE / "artifacts/design-snippets.json").write_text(json.dumps(receipts, indent=2) + "\n")
print(output)
