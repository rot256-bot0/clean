# Clean WitGen DSL

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


[Witgen/Crypto/Program.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Crypto/Program.lean#L19-L26)

```lean
def quadratic {F : Signature Ty} [Has FieldOp F] [Has (StructOp schemaDesc) F] :
    Program F [.scalar, .scalar] .quad :=
  witgen [x, y] do
    let square ← fieldMul x x
    let output ← fieldAdd square y
    let witness ← makeNamedStruct schemaDesc .quad
      fields![square := square, output := output]
    return witness
```


`Has` requests a feature in the program signature; it does not select a backend implementation. `fieldMul` and `fieldAdd` are smart constructors for the arithmetic feature. `makeNamedStruct` is the same reusable operation for every caller-defined schema.

`witgen [x, y] do` elaborates to finite, intrinsically typed `Program` syntax. Ordinary authoring does not expose de Bruijn indices or explicit feature injections. Names and aliases are weakened across bindings; nested regions declare their inputs/captures explicitly. The implemented surface supports `let x ← step`, reference aliases `let x := reference`, and `return reference`. Other statements and ambient reference captures are rejected, not given guessed scoping semantics. This is an implemented authoring subset, not a claim to support every Lean `do` construct.

The ambient-parameter interface is deliberately closed: static scalar values, type-valued families, and restricted direct uses of abstract-target `Has` capabilities are supported. Unknown records, containers, value callbacks, proof carriers and unsolved holes are rejected rather than presumed reference-free. Define schemas and smart builders globally and pass region data as explicit named inputs. Global low-level builders remain trusted; this elaborator check is not a kernel provenance theorem or a sandbox for arbitrary Lean code. [Exact policy and diagnostics](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/docs/StructAuthoringAPI.md#closed-ambient-parameter-interface).

The exact field modulus is:


[backend/src/crypto.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/crypto.rs#L8-L9)

```rust
pub const BN254_MODULUS: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";
```


This is BN254 **Fr**, distinct from its base field Fq. The native representation has four 64-bit limbs. Canonical inputs and output cells use decimal strings at the JSON boundary; no conversion through `u64` or floating point occurs. The parameter's size is not a claim of 254-bit cryptographic security.

## 2. General Structures

A schema names the result sort and its ordered fields. The sort universe and schema family belong to the caller:


[Witgen/Structs.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Structs.lean#L7-L11)

```lean
structure StructDesc (S : Type) where
  name : String
  result : S
  fields : List (String × S)
  names_nodup : (fields.map Prod.fst).Nodup := by decide
```

[Witgen/Structs.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Structs.lean#L40-L44)

```lean
inductive StructOp {S : Type} {Schema : Type}
    (desc : Schema → StructDesc S) : Signature S where
  | make (schema : Schema) : StructOp desc (desc schema).sorts [] (desc schema).result
  | get (schema : Schema) {name : String} {t : S}
      (field : FieldRef (desc schema).fields name t) : StructOp desc [(desc schema).result] [] t
```


There are only two structural operations: make a structure, and get a typed field. Adding `QuadWitness`, a nested envelope, a limb record, or a circuit-specific structure does not add another constructor to this operation family or to the core DSL.

Here are the actual caller-owned schemas for the cryptographic example:


[Witgen/Crypto/Features.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Crypto/Features.lean#L35-L43)

```lean
@[reducible] def schemaDesc : Schema → StructDesc Ty
  | .quad => {
      name := "QuadWitness"
      result := .quad
      fields := [("square", .scalar), ("output", .scalar)] }
  | .envelope => {
      name := "QuadEnvelope"
      result := .envelope
      fields := [("trace", .quad)] }
```


`fields![square := square, output := output]` checks both the names and their declared order. Duplicate field names are forbidden. `getField schemaDesc .envelope "trace" envelope` checks that the field exists and has the requested sort. Field order is explicit; this version does not automatically reorder named arguments.

The semantic representation is not an unchecked bag of constructor/projection callbacks. It includes both inverse laws:


[Witgen/Structs.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Structs.lean#L47-L51)

```lean
structure StructRepr {S : Type} (V : S → Type) (d : StructDesc S) where
  pack : HList V d.sorts → V d.result
  unpack : V d.result → HList V d.sorts
  unpack_pack : ∀ xs, unpack (pack xs) = xs
  pack_unpack : ∀ x, pack (unpack x) = x
```


`structModel_respects` proves the generic representation law for every schema and field. Lists are a separate `ListOp` feature with `empty` and `push`; branching/map/fold are a separate optional control feature. No arithmetic, structure, list, or control vocabulary is mandatory in `Witgen.Core`.

## 3. Custom Types and Features

A circuit can expose its own type and operations first, then lower them to structures. This is more than giving a standard tuple another name. The executable example introduces a native `SplitWitness` and a source `SplitOp`; the target representation of the same abstract sort is an ordered heterogeneous field list:


[Witgen/Custom.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Custom.lean#L23-L30)

```lean
@[reducible] def Native : Ty → Type
  | .nat => Nat
  | .split => SplitWitness

/-- No native SplitWitness survives in the target semantic representation. -/
@[reducible] def Structural : Ty → Type
  | .nat => Nat
  | .split => HList (fun _ : Ty => Nat) (desc .split).sorts
```

[Witgen/Custom.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Custom.lean#L76-L85)

```lean
def splitProgram (base : Nat) : Program SplitOp [.nat] .split :=
  witgen [x] do
    let witness ← split base x
    return witness

def lowProgram (base : Nat) : Program SplitOp [.nat] .nat :=
  witgen [x] do
    let witness ← split base x
    let result ← low witness
    return result
```


The implementation expands the custom feature into Nat arithmetic and generic structure operations. Access to a custom field becomes a checked structural projection:


[Witgen/Custom.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Custom.lean#L88-L103)

```lean
def lowerSplit : Template SplitOp Target
  | _, _, _, .split base, _ =>
    witgen [x] do
      let base ← constant base
      let lo ← remainder x base
      let hi ← quotient x base
      let witness ← makeNamedStruct desc .split fields![low := lo, high := hi]
      return witness
  | _, _, _, .low, _ =>
    witgen [w] do
      let result ← getField desc .split "low" w
      return result
  | _, _, _, .high, _ =>
    witgen [w] do
      let result ← getField desc .split "high" w
      return result
```

[Witgen/Custom.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Custom.lean#L105-L107)

```lean
def Related : (t : Ty) → Native t → Structural t → Prop
  | .nat, x, y => x = y
  | .split, w, fields => h![w.low, w.high] = fields
```


`lowerSplit_law` proves each replacement against the source specification. The generic core theorem then handles every program using that feature:


[Witgen/Custom.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Custom.lean#L144-L150)

```lean
def certifiedLowering : CertifiedLowering nativeModel targetModel Related :=
  .ofTemplate _ _ lowerSplit Related lowerSplit_law

theorem lowerSplit_correct (p : Program SplitOp Γ t) (xs : HList Native Γ)
    (ys : HList Structural Γ) (hr : HList.Rel Related xs ys) :
    Related t (p.eval nativeModel xs) ((p.lower lowerSplit).eval targetModel ys) :=
  Program.eval_lower_related _ _ _ _ lowerSplit_law p xs ys hr
```


The relation preserves both limbs, not merely the low output. Separate theorems establish reconstruction and the low-limb bound. The native demonstration fixes a positive base and includes an input larger than `u64`; the pure Nat model's totalized zero division is not a promise that native division accepts zero.

**Type conversion here changes semantic representation, not abstract sort indices.** A source sort can mean a native circuit structure in one model and a field-list representation in another. Reindexing into a different sort universe is a separate pass not implemented here. A custom feature still needs a lowering proof and a data-only serializer for the selected backend; it is not automatically supported merely because it has a type.

## 4. Proof-Bearing Lowering

The cryptographic example itself begins as a circuit-level `QuadFeature`. Its implementation lowers to field arithmetic and `StructOp`; field operations can then lower to arbitrary-precision Nat arithmetic with explicit reduction:


[Witgen/Crypto/Program.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Crypto/Program.lean#L50-L54)

```lean
def quadraticField : Program FieldSig [.scalar, .scalar] .quad :=
  quadraticFeature.lower quadToField

def quadraticNat (p : Nat) : Program NatSig [.scalar, .scalar] .quad :=
  quadraticField.lower (fieldToNat p)
```


The proof-bearing interface keeps models and representation relations explicit:


[Witgen/Core.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Core.lean#L214-L218)

```lean
structure CertifiedLowering (M : Model F V) (N : Model G W)
    (R : ∀ s, V s → W s → Prop) where
  run : {Γ : List S} → {t : S} → Program F Γ t → Program G Γ t
  correct : ∀ {Γ t} (p : Program F Γ t) xs ys, HList.Rel R xs ys →
    R t (p.eval M xs) ((run p).eval N ys)
```


A `Template` maps a source operation to a **target subprogram**, not just another operation tag. Its law quantifies over related arguments and regions. `Program.eval_lower_related` lifts that law through all continuations and nested regions; certified passes compose without erasing intermediate representation conditions.

For BN254, `fieldToNat_correct` covers arbitrary finite programs over the supplied arithmetic/structure signature at any positive modulus. `quadToField_correct` certifies the preceding custom-feature expansion. Neither theorem asserts that BN254 arithmetic fits in one machine word.

## 5. Native Code and Typed Errors

Both following files are generated from the actual certified ASTs. Each returns a native structure; `populate` writes every required witness cell without overwriting inputs.

### Direct BN254 Backend


[backend/src/generated_crypto/quad_bn254.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated_crypto/quad_bn254.rs#L1-L29)

```rust
// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct QuadWitness {
    pub square: witgen_native::Bn254Scalar,
    pub output: witgen_native::Bn254Scalar,
}

pub fn generate(
    x: witgen_native::Bn254Scalar,
    y: witgen_native::Bn254Scalar,
) -> witgen_native::Result<QuadWitness> {
    let _wg0: witgen_native::Bn254Scalar = witgen_native::bn254_mul(x, x);
    let _wg1: witgen_native::Bn254Scalar = witgen_native::bn254_add(_wg0, y);
    let _wg2: QuadWitness = QuadWitness {
        square: _wg0,
        output: _wg1,
    };
    Ok((_wg2).clone())
}

pub fn populate(cells: &mut [witgen_native::Bn254Scalar; 4]) -> witgen_native::Result<()> {
    let result = generate(cells[0], cells[1])?;
    let _cell0 = result.square;
    let _cell1 = result.output;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
```


### After Field → Nat: GMP Backend


[backend/src/generated_crypto/quad_nat.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated_crypto/quad_nat.rs#L1-L37)

```rust
// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct QuadWitness {
    pub square: rug::Integer,
    pub output: rug::Integer,
}

pub fn generate(x: rug::Integer, y: rug::Integer) -> witgen_native::Result<QuadWitness> {
    let _wg0: rug::Integer = witgen_native::nat_mul(&x, &x);
    let _wg1: rug::Integer = witgen_native::nat_from_str(
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    )?;
    let _wg2: rug::Integer = witgen_native::nat_mod(&_wg0, &_wg1)?;
    let _wg3: rug::Integer = witgen_native::nat_add(&_wg2, &y);
    let _wg4: rug::Integer = witgen_native::nat_from_str(
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    )?;
    let _wg5: rug::Integer = witgen_native::nat_mod(&_wg3, &_wg4)?;
    let _wg6: QuadWitness = QuadWitness {
        square: (_wg2).clone(),
        output: (_wg5).clone(),
    };
    Ok((_wg6).clone())
}

pub fn populate(cells: &mut [witgen_native::Bn254Scalar; 4]) -> witgen_native::Result<()> {
    let result = generate(
        rug::Integer::from(witgen_native::bn254_to_nat(cells[0])),
        rug::Integer::from(witgen_native::bn254_to_nat(cells[1])),
    )?;
    let _cell0 = witgen_native::bn254_from_nat(&result.square)?;
    let _cell1 = witgen_native::bn254_from_nat(&result.output)?;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
```


The same emitter handles the nested `QuadEnvelope` schema and the lowered custom `SplitWitness` without adding special record-operation cases. Structure names and ordered field types travel in the schema metadata.

### Errors Are Values, Not Strings

The shared native API has a concrete error enum and a fixed result alias:


[backend/src/error.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/error.rs#L4-L24)

```rust
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    NonCanonicalField { field: &'static str },
    NegativeNatural,
    DivisionByZero,
    WordOverflow,
    ParseInteger(rug::integer::ParseIntegerError),
    MissingField(&'static str),
    InvalidInputType { expected: &'static str },
    InputArity { expected: usize, actual: usize },
    InputLength { expected: usize, actual: usize },
    NonBooleanCell { slot: usize },
    CircuitAssumptions { circuit: &'static str },
    WitnessLength { expected: usize, actual: usize },
    UnknownProgram(String),
    Json(serde_json::Error),
    Io(io::Error),
}
```


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


[examples/caliper/modMul.caliper](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/examples/caliper/modMul.caliper#L1-L13)

```text
mul  r3, r0, r1
udiv r4, r3, r2
umod r5, r3, r2
skip
skip
mem.alloci b0, 6
mem.push  b0, r0
mem.push  b0, r1
mem.push  b0, r2
mem.push  b0, r3
mem.push  b0, r4
mem.push  b0, r5
skip
```


It starts with operands/modulus in registers and fills `[a,b,n,product,quotient,remainder]`. Allocation reserves an empty buffer; each `mem.push` initializes one cell. Zero-cost `skip` nodes are retained rather than silently optimized away.

### A Checked Runtime Bound and an Exact Cost

Import `Witgen.Backends.CaliperExamples`, open `Caliper` and `Witgen.Backends.CaliperExamples`, and use these checked declarations:


[Witgen/Backends/CaliperRuntimeGuide.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Backends/CaliperRuntimeGuide.lean#L29-L44)

```lean
theorem modMul_runtime (tape : RandomTape 64) (s₀ : State 64) (b : BufId) :
    Triple .cycles tape
      (fun s => s = s₀ ∧ s.WellFormed ∧ s.caps b = 0)
      (modMulCode b)
      (fun s' => OutputPost s₀ b [0, 1, 2] (modMulCells s₀) s' ∧ s'.WellFormed)
      99 6 6 := by
  exact modMul_triple .cycles tape s₀ b

/-- All completed executions have this exact abstract cost and memory usage. -/
theorem modMul_exact_cost (tape : RandomTape 64) (s s' : State 64)
    (b : BufId) (hfresh : s.caps b = 0) (t : Nat) (net peak : Int)
    (h : Exec .cycles tape (modMulCode b) s s' t net peak) :
    t = 99 ∧ net = 6 ∧ peak = 6 := by
  obtain ⟨_, he, _⟩ := modMul_witness_exec s .cycles tape b hfresh
  have hd := h.deterministic he
  exact ⟨hd.2.1.trans modMul_cycles_cost, hd.2.2.1, hd.2.2.2⟩
```


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
