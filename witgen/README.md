# Clean WitGen

Feature-based witness generation on the [Clean fork branch](https://github.com/rot256-bot0/clean/tree/feat/clean-witgen-dsl).
The core remains an open, finite typed IR. The main examples use the **BN254 scalar field**,
generic structures, readable named `do` authoring, and typed native errors.
The package uses Lean 4.32.2; parent Clean's WitnessIR/toolchain remain unchanged.

## Main Example

The actual program in [Crypto/Program.lean](Witgen/Crypto/Program.lean):

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

The direct backend uses four-limb `witgen_native::Bn254Scalar`; the certified Field→Nat
path uses GMP-backed `rug::Integer`. Both generated functions return
`witgen_native::Result<QuadWitness>`, whose error is the concrete
[Error enum](backend/src/error.rs), not `String`.

## Reproduce

Prerequisites: Elan/Lean, Python 3.11+, Rust 1.85+, rustfmt, and system GMP development
libraries. Dependency versions are locked. Run from **this `witgen/` directory**:

```sh
lake update
lake exe cache get
python3 tools/run_crypto.py
python3 tools/run_demo.py
python3 -m unittest discover -s tests -v
cargo test --locked --manifest-path backend/Cargo.toml --test crypto --test errors --test providers
```

Export or evaluate the real cryptographic AST without compiling Mathlib to native code:

```sh
lake build Witgen.Crypto.Export
lake env lean --run MainCrypto.lean demo
lake env lean --run MainCrypto.lean export artifacts/crypto/export
lake env lean --run MainCrypto.lean fixtures artifacts/crypto/reference.json
```

`run_crypto.py` builds the generated `witgen-crypto` binary. It accepts JSONL requests
with `program` set to `quad_bn254`, `quad_nat`, `envelope_bn254`, or `envelope_nat`,
and `inputs` containing two canonical decimal strings. Results contain all four
cells `[x,y,square,output]` as decimal strings. There is no lossy u64/float codec.
Errors retain a diagnostic `error` string plus a stable `error_code` at this boundary.
Rust callers can instead pattern-match error variants and inspect `source()`.

## Structures, Custom Types and Lowering

- [StructAuthoringAPI](docs/StructAuthoringAPI.md): `StructDesc`, generic `StructOp.make/get`,
  checked unique field names, named construction and explicit pack/unpack inverse laws.
  `ListOp` is separate. Neither is a mandatory core operation.
- [Custom.lean](Witgen/Custom.lean): a caller-owned sort universe, native `SplitWitness`
  and `SplitOp`; certified lowering to Nat arithmetic plus generic structural fields.
  The representation changes from the native record to an `HList`, not just a renamed type.
- [CryptoAPI](docs/CryptoAPI.md): circuit-level feature expansion, full-width BN254→Nat
  refinement, complete circuit witnesses, nested `QuadEnvelope`, and exact ABI/codec scope.
- [Code-first design](../doc/witgen-dsl-design.md): actual source and generated Rust,
  including typed errors and the runtime proof walkthrough.

`witgen [...] do` supports operation bindings, reference aliases and returns. Other
statements and undeclared ambient captures are rejected. Ambient parameters are limited
to static scalars, type-valued families and restricted direct abstract-target `Has`
capabilities. Unknown value callbacks/records/containers/proof carriers and unsolved
holes are rejected; schemas/helpers should be global. This is an authoring restriction,
not a kernel provenance theorem or a sandbox for arbitrary low-level builders. Named
fields must currently follow schema order. User-defined features still need a certified lowering and a
supported data-only backend codec; their existence alone is not backend support.
Representation relations may change the meaning of a sort, but current lowering keeps
abstract sort indices fixed. No global DSL enum must be extended to define a new schema.

## Caliper Analysis

```sh
python3 tools/run_caliper.py
```

The optional backend lowers actual word ASTs into Caliper statements, then reserves
and populates every cell of the full witness buffer. The [runtime guide](Witgen/Backends/CaliperRuntimeGuide.lean)
proves both a total-correctness bound and exact abstract cost for word modular
multiplication: `.cycles` time 99, net/peak buffer growth 6/6.

This is **not** a BN254 Caliper backend or a Rust runtime estimate. General multi-limb
field lowering remains future work. Costs exclude parsing, host ABI conversion and
code generation; buffer capacity excludes registers. The backend has generic primitive/
structure laws and scoped whole-program certificates, not a generic whole-compiler
preservation theorem. Dynamic branch-result shapes are rejected.

See [compiler API](docs/CaliperBackendAPI.md), [cost/circuit API](docs/CaliperCostAPI.md),
and [actual assembly snapshots](examples/caliper). Plain `import Witgen` remains
core/demo oriented; import the optional backend explicitly for Caliper analysis.

## Verification and Scope

- Main BN254 suite: four real ASTs, 12 distinct input pairs, 48 full-cell comparisons.
  Ten pairs exceed u64 inputs; unreduced products reach 508 bits. Lean, Arkworks/GMP
  and independent integer arithmetic agree. Noncanonical/negative/malformed inputs fail.
- Custom-type suite: two actual lowered programs and ten source/target/native cases,
  including a high-width split. Generic lowering and reconstruction/range proofs are separate.
- Bounded regression suite: small fields remain only for exhaustive tests and word
  lowering, with 7,472 native comparisons across 18 variants. This does not turn them
  into the main field examples. The separate gated Caliper example has two rows;
  the bounded circuit batch has three.
- Exact nonempty audits cover core/structure/custom proofs, crypto endpoints and Caliper
  endpoints. Core/crypto use standard `propext`/`Quot.sound`; Caliper additionally permits
  standard `Classical.choice`. No custom axioms, `sorry` or native-decision proofs.

The BN254 model is canonical modular arithmetic over `Fin p`. Positivity suffices for
its add/multiply/reduction proofs; there is no formal primality certificate or Lean
algebraic `Field` instance claimed here. The exact known-prime scalar parameter is
matched to the native field. Its 254-bit size is not a 254-bit security claim.

The Lean kernel verifies source/lowering/model/circuit/writer statements, **not** Rust,
GMP/Arkworks, serializers, the code printer or compiler. The latter are tested components.
No general native verification, arbitrary named-subroutine linker, automatic lowering
search or production Clean API migration is claimed. Fresh results and hashes are in
`artifacts/`; `examples/caliper/` is an explicit checked snapshot, never a live symlink.
