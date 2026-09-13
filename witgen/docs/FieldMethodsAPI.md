# Field and Method Interfaces

## Sorts and Capabilities

`Witgen.Typed.Types` defines library-owned `FieldId`, `CurveId` and `Ty`:

- `.field f` retains mathematical identity through representation changes.
- `.point c` retains curve identity, base/scalar associations and equation.
- `.pair a b`, `.option a`, `.list a` retain component types recursively.
- `.nat`, `.bool`, `.u64`, `.word4` provide library-owned value/scratch sorts.

These are not mandatory core sorts. `Core.lean` remains generic in `S`.
Reusable programs quantify over `F : Signature Ty` and require individual `Has`
capabilities. Concrete feature sums and coherent injections are selected at
instantiation/export time. Operand types infer the field/curve but not a backend.

## Field Specification

`FieldOp f` declares Const, Add, Sub, Mul, Square, Neg, Inv and Sqrt. `fieldModel f` supplies
canonical residue semantics over `Fin (modulus f)`. The namespaced helpers only
construct typed calls. `field.Const f n` specifies its otherwise ambiguous field.

`FieldInverses.lean` proves primality for every registered modulus and supplies
negation, total inverse, inverse-at-zero, additive inverse and nonzero
multiplicative inverse laws. Prime certificate data is proposed by the generator
and kernel-checked; no native decision procedure is used.

`field.Sqrt x` returns `.option (.field f)`, inferred from `x`. It returns
`some 0` at zero, `none` exactly for nonsquares, and the smaller canonical
representative of the two roots otherwise. A plain call needs only
`Has (FieldOp f) F`; matching the result additionally requires `ValueOp`.

```lean
witgen [x] do
  let root ← field.Sqrt x
  let result ← match root with
    | none => field.Const f 0
    | some r => field.Square r
  return result
```

`FieldSqrt.lean` proves the exact optional contract: `sqrt a = some r` iff
`square r = a` and `r.val ≤ (neg r).val`; `sqrt a = none` iff no root exists.
The zero, canonical-root-of-square, uniqueness and Nat representation laws follow
from this contract. The executable Lean model uses Euler's criterion and checks
its bounded Tonelli–Shanks candidate. If a square fails that candidate check,
a complete finite search preserves the semantics. Universal success or a runtime
bound for the accelerator is not claimed; the exported cases separately check
that they use the candidate/Euler path rather than the fallback.

## Generic Shared Methods

`Witgen.Methods` works over any `S` and primitive signature `F`:

- `MethodSig S` contains name, argument sorts and result sort.
- `Ref ms m` intrinsically identifies a signature in the available registry.
- `CallOp ms` contains typed calls; `WithCalls F ms` adds them optionally.
- `Library F ms` stores finite `Program` bodies, with only earlier references and
  a fresh-name proof at each insertion.

`Library.model lib primitive` evaluates the stored bodies, not host callback
payloads. Substitution, refinement, name uniqueness and earlier-only linkage are
proved. `libraryJson_size` proves one emitted definition per entry.

The type-level registry is newest-first; JSON definitions are oldest-first.
Call indices are relative to the newest-first entries available at that site.
Both name and index must select the same entry with the exact signature.

## Implementations

`NatMethods.library f` stores Add/Mul/Square definitions. Its total `handler f`
also supports constants and field-indexed Nat Sub/Neg/Inv/Sqrt primitives. These use
opcodes `nat.field.sub`, `nat.field.neg`, `nat.field.inv` and `nat.field.sqrt`, with explicit
field/modulus metadata. Sqrt returns `Option Nat` and reduces raw internal
representatives before computing its canonical root.
The checked representation relation compares the entire raw Nat value. Packing
never silently normalizes a wrong output. Native emission uses GMP.

`U64.allLibrary` stores three shared word arithmetic bodies and nine field
wrappers. Square calls Mul; Mul calls Add inside one retained 256-step loop.
Field values become four `UInt64` limbs. Raw decoding, canonicality and actual
method-body evaluation are proved.

`U64.lower` is a `PartialHandler`: it supports Const/Add/Mul/Square and explicitly
declines Sub/Neg/Inv/Sqrt. `Program.mapHandler?` traverses every operation and nested region;
unsupported code returns `none`. `PartialCertifiedLowering` proves preservation
conditional on success. `U64.compile p accepted` requires the success proof, so
there is no fallback target program. `u64FieldProgram_correct` connects the actual
accepted caller to source semantics.

## Export and Execution

`typeJson` preserves exact field moduli and structured curve descriptors.
`OpCodec F` returns operation/static metadata. The shared encoder adds references,
argument/result types, regions and continuations. `moduleJson`, `libraryJson` and
`programJson` never need a demo-specific schema.

- `MainMethods.lean export DIR`: field/Nat/U64 and real curve programs/fixtures.
- `MainExtended.lean export DIR`: Sub/Neg/Inv/Sqrt and named if/match programs/fixtures.
- `MainU64.lean export DIR`: shared U64 library and algorithm/body checks.
- `tools/run_methods.py`: exact method/curve case coverage and native replay.
- `tools/run_extended.py`: independently enumerated native/GMP/branch cases.
- `tools/run_demo.py`: aggregate reproduction, including both new runners.

See [CurveAPI](CurveAPI.md), [BranchAPI](BranchAPI.md), [U64FieldAPI](U64FieldAPI.md)
and [NativeMethodsAPI](NativeMethodsAPI.md) for the exact corresponding protocols.
