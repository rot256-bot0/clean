#!/usr/bin/env python3
"""Publish code-first interfaces by copying the checked implementation verbatim."""
from pathlib import Path
import hashlib
import json

PACKAGE = Path(__file__).resolve().parents[1]
REPO = PACKAGE.parent
URL = "https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/"
receipts = []


def sample(relative, start=None, end=None, language="lean"):
    source = (PACKAGE / relative).read_text()
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

[Source branch](https://github.com/rot256-bot0/clean/tree/feat/clean-witgen-dsl) · [Run instructions](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/README.md)

All code blocks below are extracted from checked source or actual generated output. This package is developed inside the Clean fork; it does not yet replace the parent Clean WitnessIR.

<details>
<summary>Contents</summary>

- [Write the WitGen](#1-write-the-witgen)
- [General Structures](#2-general-structures)
- [Custom Types and Features](#3-custom-types-and-features)
- [Proof-Bearing Lowering](#4-proof-bearing-lowering)
- [Native Code and Typed Errors](#5-native-code-and-typed-errors)
- [The Full Circuit Witness](#6-the-full-circuit-witness)
- [Caliper Integration and Runtime Proofs](#7-caliper-integration-and-runtime-proofs)
- [Checks and Boundaries](#8-checks-and-boundaries)

</details>

## 1. Write the WitGen

The main example uses the **BN254 scalar field**, not a small test field. The author asks for field arithmetic and generic structure operations, using named bindings and named fields:

""", sample("Witgen/Crypto/Program.lean", "def quadratic {", "/-- Circuit-level feature"), """
`Has` requests a feature in the program signature; it does not select a backend implementation. `fieldMul` and `fieldAdd` are smart constructors for the arithmetic feature. `makeNamedStruct` is the same reusable operation for every caller-defined schema.

`witgen [x, y] do` elaborates to finite, intrinsically typed `Program` syntax. Ordinary authoring does not expose de Bruijn indices or explicit feature injections. Names and aliases are weakened across bindings; nested regions declare their inputs/captures explicitly. The implemented surface supports `let x ← step`, reference aliases `let x := reference`, and `return reference`. Other statements and ambient reference captures are rejected, not given guessed scoping semantics. This is an implemented authoring subset, not a claim to support every Lean `do` construct.

The ambient-parameter interface is deliberately closed: static scalar values, type-valued families, and restricted direct uses of abstract-target `Has` capabilities are supported. Unknown records, containers, value callbacks, proof carriers and unsolved holes are rejected rather than presumed reference-free. Define schemas and smart builders globally and pass region data as explicit named inputs. Global low-level builders remain trusted; this elaborator check is not a kernel provenance theorem or a sandbox for arbitrary Lean code. [Exact policy and diagnostics](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/docs/StructAuthoringAPI.md#closed-ambient-parameter-interface).

The exact field modulus is:

""", sample("backend/src/crypto.rs", "pub const BN254_MODULUS", "#[derive", language="rust"), """
This is BN254 **Fr**, distinct from its base field Fq. The native representation has four 64-bit limbs. Canonical inputs and output cells use decimal strings at the JSON boundary; no conversion through `u64` or floating point occurs. The parameter's size is not a claim of 254-bit cryptographic security.

## 2. General Structures

A schema names the result sort and its ordered fields. The sort universe and schema family belong to the caller:

""", sample("Witgen/Structs.lean", "structure StructDesc", "def StructDesc.sorts"),
 sample("Witgen/Structs.lean", "inductive StructOp", "/-- Explicit isomorphism"), """
There are only two structural operations: make a structure, and get a typed field. Adding `QuadWitness`, a nested envelope, a limb record, or a circuit-specific structure does not add another constructor to this operation family or to the core DSL.

Here are the actual caller-owned schemas for the cryptographic example:

""", sample("Witgen/Crypto/Features.lean", "@[reducible] def schemaDesc", "def schemaRepr"), """
`fields![square := square, output := output]` checks both the names and their declared order. Duplicate field names are forbidden. `getField schemaDesc .envelope "trace" envelope` checks that the field exists and has the requested sort. Field order is explicit; this version does not automatically reorder named arguments.

The semantic representation is not an unchecked bag of constructor/projection callbacks. It includes both inverse laws:

""", sample("Witgen/Structs.lean", "structure StructRepr", "def structModel"), """
`structModel_respects` proves the generic representation law for every schema and field. Lists are a separate `ListOp` feature with `empty` and `push`; branching/map/fold are a separate optional control feature. No arithmetic, structure, list, or control vocabulary is mandatory in `Witgen.Core`.

## 3. Custom Types and Features

A circuit can expose its own type and operations first, then lower them to structures. This is more than giving a standard tuple another name. The executable example introduces a native `SplitWitness` and a source `SplitOp`; the target representation of the same abstract sort is an ordered heterogeneous field list:

""", sample("Witgen/Custom.lean", "@[reducible] def Native", "def repr"),
 sample("Witgen/Custom.lean", "def splitProgram", "/-- The lowering author"), """
The implementation expands the custom feature into Nat arithmetic and generic structure operations. Access to a custom field becomes a checked structural projection:

""", sample("Witgen/Custom.lean", "def lowerSplit", "def Related"),
 sample("Witgen/Custom.lean", "def Related", "/-- Per-feature proof"), """
`lowerSplit_law` proves each replacement against the source specification. The generic core theorem then handles every program using that feature:

""", sample("Witgen/Custom.lean", "def certifiedLowering", "/-- A circuit-facing"), """
The relation preserves both limbs, not merely the low output. Separate theorems establish reconstruction and the low-limb bound. The native demonstration fixes a positive base and includes an input larger than `u64`; the pure Nat model's totalized zero division is not a promise that native division accepts zero.

**Type conversion here changes semantic representation, not abstract sort indices.** A source sort can mean a native circuit structure in one model and a field-list representation in another. Reindexing into a different sort universe is a separate pass not implemented here. A custom feature still needs a lowering proof and a data-only serializer for the selected backend; it is not automatically supported merely because it has a type.

## 4. Proof-Bearing Lowering

The cryptographic example itself begins as a circuit-level `QuadFeature`. Its implementation lowers to field arithmetic and `StructOp`; field operations can then lower to arbitrary-precision Nat arithmetic with explicit reduction:

""", sample("Witgen/Crypto/Program.lean", "def quadraticField :", "theorem quadraticField_eval"), """
The proof-bearing interface keeps models and representation relations explicit:

""", sample("Witgen/Core.lean", "structure CertifiedLowering", "def CertifiedLowering.ofHandler"), """
A `Template` maps a source operation to a **target subprogram**, not just another operation tag. Its law quantifies over related arguments and regions. `Program.eval_lower_related` lifts that law through all continuations and nested regions; certified passes compose without erasing intermediate representation conditions.

For BN254, `fieldToNat_correct` covers arbitrary finite programs over the supplied arithmetic/structure signature at any positive modulus. `quadToField_correct` certifies the preceding custom-feature expansion. Neither theorem asserts that BN254 arithmetic fits in one machine word.

## 5. Native Code and Typed Errors

Both following files are generated from the actual certified ASTs. Each returns a native structure; `populate` writes every required witness cell without overwriting inputs.

### Direct BN254 Backend

""", sample("backend/src/generated_crypto/quad_bn254.rs", language="rust"), """
### After Field → Nat: GMP Backend

""", sample("backend/src/generated_crypto/quad_nat.rs", language="rust"), """
The same emitter handles the nested `QuadEnvelope` schema and the lowered custom `SplitWitness` without adding special record-operation cases. Structure names and ordered field types travel in the schema metadata.

### Errors Are Values, Not Strings

The shared native API has a concrete error enum and a fixed result alias:

""", sample("backend/src/error.rs", "pub type Result", "impl Error", language="rust"), """
Callers can match `Error::DivisionByZero`, inspect expected/actual lengths, or distinguish canonical-field failures from malformed input. `Error` implements `Display` and `std::error::Error`; integer-parse, JSON and I/O errors retain their original `source()`. Providers, generated functions, writers and dispatch all propagate this type. Only the CLI formats a diagnostic string, alongside a stable `error_code`.

The tests execute high-width multiplication/reduction and reject noncanonical field values, negative Nat values, malformed integers, wrong arities and bad lengths. Output validation is completed before any witness stores. The raw Nat backend remains arbitrary precision; the BN254 backend admits only canonical scalar representatives.

## 6. The Full Circuit Witness

A correct public output alone is insufficient. The BN254 quadratic witness exposes both the internal square and the public output. The complete buffer is `[x, y, square, output]`, and its independent relation requires:

```text
inputs are bound unchanged
0 ≤ square, output < p
square = x*x mod p
output = square+y mod p
```

`QuadCircuit.sound` is generator-independent. `quadFieldWitgen` and `quadNatWitgen` store the actual programs with fixed input/output adapters. `quad_nat_raw_buffer` proves that the **raw** Nat result already equals the field witness buffer—no hidden modular repair in an output decoder. `envelope_nat_buffer_correct` carries the same complete witness through a nested custom structure.

The arithmetic proof models canonical residues as `Fin p` and uses `0 < p`. It does not prove primality or declare a Lean algebraic `Field` instance; the exact known-prime BN254 scalar parameter identifies the intended native field. The add/multiply/reduction proofs do not need primality.

The main native validation executes four actual ASTs on twelve input pairs, for 48 complete witnesses. Ten pairs have an input outside `u64`; unreduced squares reach 508 bits. Both backends are compared to Lean and to a separate integer arithmetic oracle. These are boundary/representative tests, not an exhaustive enumeration of a cryptographic field.

## 7. Caliper Integration and Runtime Proofs

Caliper is an **analysis backend**, not the native execution engine. Its current target handles words, static structure/list layouts and supported control. It does not yet implement full-width BN254 field arithmetic; such a path would need a certified multi-limb implementation. The example below is instead parameterized **word modular multiplication**, kept separate from the cryptographic field examples.

This is the actual emitted producer followed by its complete input-and-witness writer:

""", sample("examples/caliper/modMul.caliper", language="text"), """
It starts with operands/modulus in registers and fills `[a,b,n,product,quotient,remainder]`. Allocation reserves an empty buffer; each `mem.push` initializes one cell. Zero-cost `skip` nodes are retained rather than silently optimized away.

### A Checked Runtime Bound and an Exact Cost

Import `Witgen.Backends.CaliperExamples`, open `Caliper` and `Witgen.Backends.CaliperExamples`, and use these checked declarations:

""", sample("Witgen/Backends/CaliperRuntimeGuide.lean", "theorem modMul_runtime", "end Witgen.Backends.CaliperRuntimeGuide"), r"""
`Triple C tape P code Q T D M` proves terminating execution from every state satisfying `P`, with postcondition `Q` and upper bounds on time, net capacity growth and peak growth. `Exec` carries exact costs. The second theorem uses determinism to establish exact values for every completed run.

For a memory-neutral producer and a fresh output buffer of $n$ words, the writer-composition theorem charges

$$
\begin{aligned}
T_{\mathrm{full}} &= T_{\mathrm{producer}} + C.\mathrm{memAlloc}\\
&\quad + n\,C.\mathrm{allocPerWord} + n\,C.\mathrm{memPush}.
\end{aligned}
$$

This word example costs 15 under `.unit` and 99 under `.cycles`, with net/peak buffer growth 6/6. These are abstract model charges, **not a Rust runtime or measured hardware cycles**. Inputs start in registers: parsing, host conversion, Lean code generation and compilation are outside the clock. Buffer capacity excludes registers; static register endpoints are not liveness peaks.

To analyze another WitGen: fix its input/representation assumptions and source program; prove the feature fallbacks; compile the actual word AST with checked fresh registers and static shapes; prove its execution/value correspondence and cost formula; compose with `withWitness_exec`; finally connect every copied cell to the circuit relation. For size-dependent bounds, prove the parameterized family—not merely a timed or checked instance.

**There is no generic whole-compiler preservation theorem yet.** Current whole-program certificates cover the documented word examples and fixed two-row gated program. Branch outputs with incompatible static shapes are rejected. Runtime-length containers and a general multi-limb field lowering are not implemented. The word execution model covers wrapping and totalized zero division; Nat/circuit correctness needs the stated bounds and positive-modulus hypotheses.

[Compiler API](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/docs/CaliperBackendAPI.md) · [Cost and Circuit Theorems](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/docs/CaliperCostAPI.md)

## 8. Checks and Boundaries

```sh
cd witgen
python3 tools/run_crypto.py       # main BN254 field/GMP examples
python3 tools/run_demo.py         # full suite, custom types and Caliper included
python3 -m unittest discover -s tests -v
cargo test --locked --manifest-path backend/Cargo.toml --test crypto --test errors --test providers
```

The older small-field suite remains for exhaustive bounded regressions and word-lowering tests; it is not the main field example. Its native suite still compares 7,472 cases across 18 variants. The separate custom-type path adds two generated programs and ten exact source/target/native comparisons. Named-argument, duplicate-name, scoping, alias, shadowing, capture and invalid-shape controls accompany the generic structural authoring layer.

**Kernel-checked:** typed finite syntax, operation-to-subprogram/model-related lowering, generic structure representation laws, the circuit/full-buffer results and the specifically scoped Caliper execution/resource theorems. Exact nonempty axiom audits keep the core/crypto policies at `propext` and `Quot.sound`; Caliper additionally permits standard `Classical.choice`. No custom axioms, `sorry`, native-decision proofs or blanket heartbeat increases are used.

**Tested boundary:** elaboration behavior, JSON codecs, Rust printing, rustfmt/rustc, Arkworks/GMP and native execution. The code emitter does not reconstruct code from evaluated outputs. Cryptographic-size arithmetic is implemented and tested; a verified foreign runtime, a general multi-limb Caliper backend, automatic lowering search, arbitrary procedure linking, and replacement of parent Clean's WitnessIR remain separate work.
"""]

output = REPO / "doc/witgen-dsl-design.md"
output.write_text("\n".join(parts))
(PACKAGE / "artifacts").mkdir(exist_ok=True)
(PACKAGE / "artifacts/design-snippets.json").write_text(json.dumps(receipts, indent=2) + "\n")
print(output)
