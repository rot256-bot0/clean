# Clean WitGen DSL

Typed, feature-based witness programs in the [Clean fork](https://github.com/rot256-bot0/clean/tree/feat/clean-witgen-dsl).
The generic Core has no mandatory arithmetic, structure, curve or call operations.
This package uses Lean 4.32.2; parent Clean's WitnessIR/toolchain remain unchanged.

## Namespaced, Type-Directed Operations

```lean
witgen [a,b] do
  let aa ← field.Square a
  let product ← field.Mul aa b
  let five ← field.Const f 5
  let out ← field.Add product five
  return out
```

This is the body of [fieldProgram](Witgen/Typed/Examples.lean). Operands have sort
`.field f`; the feature is `FieldOp f`. The library registers BN254 Fr and the
separate secp256k1 base/scalar fields. `field.Mul/Add/Square` infer the functionality
from their operands, while backend/lowering selection remains explicit.
Mixed-field arithmetic and base-as-scalar curve scaling are rejected.

[Public.mixed](Witgen/Typed/Public.lean) demonstrates both field identities with
actual secp point operations. `curve.Inv` means group inverse `−P`. The real source
model is Mathlib's secp256k1 Weierstrass curve; both modulus primes have closed
kernel-checked Lucas certificates. Native curve execution uses Arkworks.

- `curve.ToAffine : Point → Option (Base × Base)` — None at infinity.
- `curve.FromAffine : Base × Base → Option Point` — None off-curve, never an
  implicit invalid-coordinate→identity conversion.
- `curve.X` is an explicitly total convenience view with `X(identity)=0`.

The curve feature could instead receive a certified curve→field implementation
for another backend. That fallback is **not implemented in this revision**.
Scalar representatives act by their canonical natural value; generator-order/
cofactor and modulo-order module-action proofs are not claimed.

## Functional Structures

`struct.Named`, `struct.Get`, and `struct.Set` use generic caller-owned schemas.
`Set` returns an updated value without modifying the old record or other fields.
Typed field membership, distinct names, get/set laws and representation-preserving
updates are proved. Named arguments currently follow schema order. Lists are a
separate optional feature; pairs/options are library-owned too.

The named `witgen [...] do` surface elaborates to finite typed syntax and supports
operation binds, reference aliases and returns. Its fail-closed ambient interface
admits static scalars, type-valued families and restricted abstract-target Has
capabilities—not arbitrary captured records/callbacks/proofs or unsolved holes.
Global low-level AST builders remain trusted; this is not a sandbox.
See [StructAuthoringAPI](docs/StructAuthoringAPI.md).

## Shared Methods and Field → U64

[Methods.lean](Witgen/Methods.lean) provides typed signatures, earlier-only call
references and finite method bodies. Evaluation uses those actual bodies, not
host-function payloads. Generic call/refinement/linkage laws are checked.

The Field→Nat backend stores Add/Mul/Square bodies and retains calls. The **real
Field→U64 backend** has three shared arithmetic bodies and nine thin wrappers for
the three fields. One emitted unit shares them across twelve callers. Multiplication
contains one bounded 256-bit loop; Square calls Mul and Mul calls Add. The caller
never expands that arithmetic at each source operation.

Four-limb carry/borrow, overflow-aware modular addition, multiplication, squaring,
canonical outputs and raw decoding are proved; separate theorems connect the
stored AST bodies to the algorithms. No whole-field Nat/GMP/native field operation
is hidden inside U64 method arithmetic. Input/output codecs and public loop indices
are separate from the word data path. This is a reference double/add implementation,
not optimized Montgomery arithmetic or a constant-time certificate.

- [Field/method API](docs/FieldMethodsAPI.md)
- [U64 arithmetic, bodies and lowering](docs/U64FieldAPI.md)
- [Actual shared generated library](backend/src/generated_methods/shared_u64.rs)
- [secp256k1 feature and affine API](docs/SecpAPI.md)
- [Code-first design](../doc/witgen-dsl-design.md)

## Reproduce

Prerequisites: Elan/Lean, Python 3.11+, Rust 1.85+, rustfmt and system GMP development
libraries. Dependencies are locked. Run from **this `witgen/` directory**:

```sh
lake update
lake exe cache get
python3 tools/run_methods.py
python3 tools/run_demo.py
python3 -m unittest discover -s tests -v
cargo test --locked --manifest-path backend/Cargo.toml --test typed --test crypto --test providers
```

Fresh methods/curve/U64 evidence and source/artifact hashes are written to
`artifacts/methods/verification.json`. The native `witgen-methods` binary accepts
JSONL with `program` and typed `inputs`. Whole field inputs/outputs are decimal
strings; point inputs use SEC1 hex (`00` is identity). Pair values are two-element
JSON arrays. `None` is null; an ordinary `Some` uses its payload, while nested
optional payloads use a single-key `{"some": ...}` tag to keep `Some(None)` distinct
from `None`. No field value is truncated through one u64.

```sh
lake env lean --run MainMethods.lean export artifacts/methods/bundle
lake env lean --run MainU64.lean export artifacts/u64
python3 -B Witgen/U64/check.py  # fresh Std-only U64 import-closure check
```

The new native pipeline executes 408 fixture cases (not all distinct pairs),
including real curve/affine cases and raw U64 field outputs. U64 source checks cover
601 pairs across 14 moduli, testing both algorithms and stored method ASTs. Exact
nonempty audits cover methods/fields/curve, U64 and structural updates. The older
48-case BN254 full-witness, ten-case custom-type and 7,472-case bounded suites remain
regressions; the small fields are not the main example.

## Proof and Analysis Boundaries

Kernel proofs cover the stated feature/method/model/arithmetic/curve/structure
contracts. Serialization, Rust emission/compiler and Arkworks/GMP are tested TCB,
not kernel-verified native execution. Certificate generators propose prime data;
Lean checks the factors and modular-power traces. No custom axioms, native-decision
shortcut or heartbeat/recursion-limit increases are used.

The existing Caliper backend still certifies its documented static word examples.
It has not been extended to a complete cost analysis of the new method library,
curve feature or generated Rust. Its 99-cycle word-ModMul example is not a runtime
bound for U64 field multiplication. Buffer capacity excludes registers.

Remaining separate work includes recursive methods, automatic lowering search,
curve→field lowering, full new-library Caliper/native timing, and production Clean
integration. These are not claimed by the current examples.
