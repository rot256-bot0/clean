# BN254 scalar-field API

```sh
lake build Witgen.Crypto.Export
lake env lean --run MainCrypto.lean export DIR
lake env lean --run MainCrypto.lean fixtures FILE
lake env lean --run MainCrypto.lean fixtures      # same JSON array on stdout
lake env lean --run MainCrypto.lean demo
```

## Field and arithmetic model

Namespace: `Witgen.Crypto`.

```lean
def bn254Modulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617
abbrev BN254 := Fin bn254Modulus
```

This is BN254's **scalar** parameter (`Fr`), not its different base-field parameter (`Fq`). Independently verified against the exact `#[modulus = "..."]` in [arkworks 0.4.0 `fields/fr.rs`](https://docs.rs/ark-bn254/0.4.0/src/ark_bn254/fields/fr.rs.html). The parameter has 254 bits; this is not a claim of 254-bit security.

`Residue.ofNat`, `Residue.add`, and `Residue.mul` model canonical modular arithmetic using `Fin p`. Proofs are generic in positive `p`; **primality is not formally checked**, no algebraic `Field` instance is claimed, and no primality axiom is added. The exact known-prime parameter identifies the intended field. The arithmetic theorems also work for positive composite moduli.

## Real feature program and custom types

`Program.lean` defines the circuit-level `QuadFeature.generate`, with a complete `QuadWitness` specification. `quadToField` lowers it to the following feature-polymorphic implementation:

```lean
def quadratic {F : Signature Ty}
    [Has FieldOp F] [Has (StructOp schemaDesc) F] :
    Program F [.scalar, .scalar] .quad :=
  witgen [x, y] do
    let square ← fieldMul x x
    let output ← fieldAdd square y
    let witness ← makeNamedStruct schemaDesc .quad
      fields![square := square, output := output]
    return witness
```

`quadraticField` is the actual lowered circuit-feature AST; `quadraticNat p` applies the certified field-to-Nat template to that AST. An addition/multiplication becomes arbitrary `Nat` addition/multiplication followed by an explicit modulus literal and `Nat.mod`. This is the model for the parent's arbitrary-precision GMP backend, **not a one-u64 lowering**.

`schemaDesc`/`schemaRepr` supply caller-owned descriptors and proved pack/unpack isomorphisms to the sibling's reusable `StructOp`. `schemaDesc` is reducible so `getField` can resolve checked literal field names. No bespoke data-operation enum was added.

`Custom.lean` adds the nested native structure `QuadEnvelope { trace : QuadWitness }`. `envelopeRecord` demonstrates named construction and `getField schemaDesc .envelope "trace"`; `envelopeField` composes it with the real quadratic AST. `envelopeNat` lowers that composed AST. Both nested witness cells retain their full circuit/layout proofs.

## Export contract

`CryptoExport.modules` exports **four** files plus `manifest.json`:

| File | Domain | Complete output paths |
|---|---|---|
| `quad_bn254.json` | `bn254` | `square`, `output` |
| `quad_nat.json` | `nat` | `square`, `output` |
| `envelope_bn254.json` | `bn254` | `trace.square`, `trace.output` |
| `envelope_nat.json` | `nat` | `trace.square`, `trace.output` |

Every module uses:

- Existing JSON AST schema, `version: 1`, function name `generate`, scalar sort JSON string `"scalar"`.
- `input_semantics: "bn254"` and top-level `field_modulus` equal to the exact decimal **string** above.
- `wire_layout.field: "bn254"`, `cells: 4`, `input_slots: [0, 1]`.
- Output slots `square = 2`, `output = 3`; nested modules prefix the paths with `"trace"`. Path names/order derive from the actual descriptors and proved layout.
- Inputs named `x`, `y`, both canonical field representatives. All literals/constants, input values, and expected cells are decimal **strings**; only indices/counts/version are JSON numbers.
- Operations `field.mul`, `field.add`, or `nat.mul`, `nat.const`, `nat.mod`, `nat.add`, together with generic `record.make` and `record.get`. No custom circuit feature remains in exported syntax.

The parent native provider uses four-limb `Bn254Scalar`, `bn254_*` operations and Nat/GMP. The full native pipeline is reproduced by `python3 tools/run_crypto.py`.

## Fixtures and complete-cell semantics

`fixtures FILE` writes a JSON array with **48** cases: four actual exported ASTs on **12 distinct input pairs**. `fixtures` without a path prints the identical array.

```json
{"program":"quad_bn254","inputs":["...","..."],"expected":{"cells":["x","y","square","output"]}}
```

The strings above illustrate the shape; actual fixture strings contain only decimal digits. Ten input pairs have `x > 2^64 - 1`. Inputs include `p-1`, `p-2`, `p/2`, `2^64`, `2^128+123`, `2^200+7`, and `2^253`; unreduced products reach **508 bits**. Two small edge cases remain as controls, not as renamed main examples. There is no field enumeration.

Reference values come from executing the actual field and lowered Nat ASTs. The Nat fixture encoder consumes the **raw** Nat record without modular repair. Every fixture compares every cell and checks the independent gate relation:

```text
cells[0] = x                     cells[1] = y
cells[2] < p                    cells[3] < p
cells[2] = cells[0]^2 mod p
cells[3] = (cells[2] + cells[1]) mod p
```

A separate Python integer oracle verified all exported fixture cells. Kernel tests include correct-output/wrong-internal-square rejection, modulus-boundary multiplication/addition, large literal reduction through the feature AST, and composite-modulus arithmetic.

## Kernel endpoints and trust

- `fieldToNat_law`, `fieldToNat_correct`, `fieldNatLowering`: local arithmetic/structural refinement and compositional preservation for **any** finite program over the signature and positive modulus, including full aggregate returns.
- `quadToField_law`, `quadToField_correct`: custom circuit-feature expansion for any subprogram over `QuadFeature`.
- `QuadCircuit.sound`: generator-independent full-witness relation implies the public quadratic specification.
- `quadFieldWitgen`, `quadNatWitgen`: actual `Circuits.FormalWitgen` packages with fixed ABI adapters and full relation correctness; the Nat package is transported by the certified lowering.
- `QuadCircuit.constraints_iff`: accepting complete buffers correspond exactly to bound inputs plus a full satisfying encoded witness. Input preservation, witness-cell placement, canonical ranges, nonaliasing and all-slot coverage are proved separately.
- `quadNat_raw_canonical`, `quad_nat_raw_buffer`, `quad_full_buffer_agrees`, `quad_nat_buffer_correct`: exact source/target record and full-buffer agreement, with no hidden normalization.
- `envelopeNat_raw_buffer`, `envelope_nat_buffer_correct`, `envelopeOutputPaths_exact`: nested custom-record full-layout correspondence.

`Audit.lean` prints **16 named declarations**. The checked dependency union is only Lean's standard `propext` and `Quot.sound`; several declarations are axiom-free. No custom axioms, `sorry`, native decision shortcut, unsafe code, or heartbeat increases are used.

The Lean kernel verifies the typed AST semantics and writer/circuit correspondence, **not** JSON serialization, Python/Rust emission, rustc, arkworks, GMP, or native codecs. All four actual ASTs have been emitted and run through Arkworks/GMP, with full-cell comparison to Lean and independent integer arithmetic. These executed tests do not make the native boundary kernel-verified. Existing F17/Word/Caliper fixtures are untouched bounded regressions, and their word-cost claims do not apply to BN254 or GMP artifacts.

## Checked commands

```sh
lake build Witgen.Crypto.Tests                  # primary test module target
lake env lean Witgen/Crypto/FieldTests.lean
lake env lean Witgen/Crypto/ProgramTests.lean
lake env lean Witgen/Crypto/CircuitTests.lean
lake env lean Witgen/Crypto/CustomTests.lean
lake env lean Witgen/Crypto/ExportTests.lean
lake env lean Witgen/Crypto/Audit.lean
```

Observed CLI receipts: `{"exported":4}`, `{"fixtures":48}`. `ExportTests` reported `crypto export: 4 ASTs, 48 full-layout decimal-string fixtures`. The exact nonempty audit set was parsed against the source declarations and its standard-axiom whitelist.
