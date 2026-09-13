# Polymorphic WitGen DSL

Typed, feature-based witness programs on the authorized
[`feat/clean-witgen-dsl`](https://github.com/rot256-bot0/clean/tree/feat/clean-witgen-dsl)
branch. This package uses Lean 4.32.2. Parent Clean's WitnessIR/toolchain and the
finite `Program`/`Regions` core are unchanged.

## Interfaces and Specifications

- `FieldOp f`: Const, Add, Sub, Mul, Square, Neg, Inv, Sqrt. Operand types select the field;
  backend selection is separate. `fieldModel` specifies canonical modular arithmetic.
  Inversion maps zero to zero and satisfies the proved nonzero inverse law.
  Square root returns an Option: zero has root zero, nonsquares return none, and
  squares return the smaller canonical representative of their two roots.
- `CurveOp c`: Const, Add, Mul, Inv, Eq, MSM, Generator, Identity, ToAffine,
  FromAffine. `c` contains field identities and the Weierstrass equation.
  `Curve.model` interprets real Mathlib points; secp256k1 is the concrete native instance.
- `CurveLiteral c`: infinity or affine coordinates with a kernel-checked
  nonsingularity proof. `curve.Const` returns a point directly. Native IR validation
  also checks canonical coordinates and the configured equation before emitting code.
- `StructOp desc`: named construction, projection and functional update.
  `struct.Set` preserves the old record and unrelated fields.
- `BranchOp bool`: optional conditional control with explicit capture regions.
  `ValueOp` provides typed pairs, lists and options, including option case analysis.
  Returning Bool does not require Boolean-logic operations.

Reusable examples are capability-polymorphic: `CurvePrograms.mixed` requires
`Has (CurveOp c) F`, the base/scalar `FieldOp` capabilities and `Has ValueOp F`.
Concrete feature bundles are chosen at export/instantiation time.

The named surface supports ordinary operation binds, aliases, `if` and exhaustive
`none`/`some` matches. Branch captures are reified as typed region inputs. Patterns
bind payload variables explicitly, including shadowing. Undeclared ambient
references, incomplete matches and missing capabilities are rejected.

`curve.X` and `curve.Scale` are removed. The example obtains both coordinates
through `ToAffine` and uses `curve.Mul`. Affine roundtrip returns `Some p` for finite
points and `None` at infinity; runtime invalid coordinates return `None`.
`curve.Eq` compares mathematical points. MSM consumes one list of scalar/point pairs
and returns identity for the empty list. Native execution uses Arkworks.

## Shared Methods and Lowering

`Methods.lean` provides finite typed signatures, earlier-only call references and
stored bodies. Evaluation uses those bodies, not host-function payloads. Generic
substitution, refinement, name-uniqueness and linkage laws are checked.

The Nat implementation stores Add/Mul/Square bodies and retains calls. Sub/Neg/Inv/Sqrt
have field-indexed Nat primitives with proved raw-Nat representation preservation;
the emitter implements them with GMP.

The U64 target has three shared arithmetic bodies and nine thin field wrappers.
One emitted library serves twelve callers. Multiplication contains one bounded
256-bit loop; Square calls Mul and Mul calls Add. Four-limb carry/borrow,
overflow-aware addition, multiplication, squaring, canonicality and raw decoding
are proved, with separate stored-body evaluation theorems.

U64 supports Const/Add/Mul/Square. Its partial handler declines Sub/Neg/Inv/Sqrt rather than
inventing a word implementation. `U64.compile` requires an acceptance proof;
`PartialCertifiedLowering` proves preservation for accepted programs. Nested
unsupported operations fail closed. Nat lowering remains total for all eight field
operations. No whole-field Nat/GMP/native-field arithmetic is hidden in U64 bodies.

## Reproduce

Prerequisites: Elan/Lean, Python 3.11+, Rust 1.85+, rustfmt and GMP development
libraries. Dependencies and toolchains are pinned. Run from this directory:

```sh
lake exe cache get
python3 tools/run_demo.py
python3 -m unittest discover -s tests -v
cargo test --locked --manifest-path backend/Cargo.toml
cargo test --locked --manifest-path backend/Cargo.toml --features asm
```

Focused paths:

```sh
python3 tools/run_methods.py
python3 tools/run_extended.py
python3 -B Witgen/U64/check.py
```

- Methods: 449 exact cases, including 25 curve equalities, MSMs, point constants,
  affine conversions and 279 raw U64 field results.
- Extended: 720 exact cases across 39 programs, checking native/GMP Sub/Neg/Inv/Sqrt,
  canonical roots of squares, and both outcomes of named conditionals and option
  matches. Square roots are independently checked with a Cipolla oracle.
- U64 source: 601 pairs across 14 moduli, with 1,803 algorithm and 1,803 stored-body
  checks. The cold command rebuilds the entire local import closure without project
  oleans, using the pinned dependency caches; it records their manifests.
- Existing full-witness BN254, custom types, bounded small-field and Caliper suites
  remain integrated regressions.

Receipts live in `artifacts/{methods,extended}/verification.json`. They bind source,
exported inputs, exact independently enumerated case multisets, raw native results,
and the actual Cargo-reported executable. The methods receipt supports historical
hash validation and artifact/executable mutation controls.

JSON fields use full-width decimal strings. Point inputs use SEC1 hex (`00` is
infinity). Pairs and lists use arrays. Optional payloads preserve `None` separately
from `Some(None)` using a nested-option tag. Native IR descriptors preserve and
validate curve name, fields, moduli and coefficients.

## Proof Scope

Kernel proofs cover the declared models, typed programs, representation relations,
method bodies and arithmetic. Prime certificates for all three field moduli are
checked by Lean. No custom axioms, native-decision shortcuts or raised proof limits
are used. Serialization, Rust emission/compiler, Arkworks and GMP are tested TCB,
not kernel-verified native code. Scalar multiplication uses canonical natural
representatives; generator-order/cofactor/module-action theorems are not claimed.

Curve-to-field lowering is outside this PoC. Caliper remains a U64-level analysis
backend: it has no field/curve implementations. Its documented abstract costs are
not native runtime or hardware timing, and buffer capacity excludes registers.

## Source Guides

- [Code-first design](../doc/witgen-dsl-design.md)
- [Generic curve specification and typed literals](docs/CurveAPI.md)
- [Branching surface and region protocol](docs/BranchAPI.md)
- [Field and method interfaces](docs/FieldMethodsAPI.md)
- [Word arithmetic and shared methods](docs/U64FieldAPI.md)
- [Native metadata and codecs](docs/NativeMethodsAPI.md)
- [Named structures and capture policy](docs/StructAuthoringAPI.md)
