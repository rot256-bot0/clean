#!/usr/bin/env python3
"""Build the design from verbatim checked source and actual generated methods."""
from pathlib import Path
import hashlib
import json

PACKAGE=Path(__file__).resolve().parents[1]
REPO=PACKAGE.parent
URL='https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/'
receipts=[]


def sample(relative,start=None,end=None,language='lean'):
    source=(PACKAGE/relative).read_text()
    first=source.index(start) if start else 0
    last=source.index(end,first) if end else len(source)
    text=source[first:last].rstrip()
    lo=source[:first].count('\n')+1;hi=lo+text.count('\n')
    receipts.append({'path':'witgen/'+relative,'start':lo,'end':hi,
                     'sha256':hashlib.sha256(text.encode()).hexdigest()})
    return f'[{relative}]({URL}witgen/{relative}#L{lo}-L{hi})\n\n```{language}\n{text}\n```\n'


parts=['''# Polymorphic WitGen DSL

[Source branch](https://github.com/rot256-bot0/clean/tree/feat/clean-witgen-dsl) · [Run instructions](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/README.md)

Features declare typed operations. Models specify their semantics; implementation/instantiation passes choose representations and preserve those semantics. The examples below are compiled Lean source and actual emitted Rust. The generic core has no mandatory field, curve, structure, or control-flow feature.

<details>
<summary>Contents</summary>

- [Fields Are Selected by Types](#1-fields-are-selected-by-types)
- [Generic Elliptic Curves](#2-generic-elliptic-curves)
- [Branching and Structures](#3-branching-and-structures)
- [Shared Methods](#4-shared-methods)
- [Field → Nat](#5-field--nat-gmp-backend)
- [Field → U64](#6-field--u64-shared-word-methods)
- [Caliper Integration and Runtime Proofs](#7-caliper-integration-and-runtime-proofs)

</details>

## 1. Fields Are Selected by Types

`field.Add`, `field.Sub`, `field.Mul`, `field.Square`, `field.Neg`, `field.Inv`, and `field.Sqrt` infer the field identity from their operands. Constants specify the field explicitly.

''',sample('Witgen/Typed/Field.lean','inductive FieldOp','def fieldModel'),'''

### Semantics

`FieldOp` declares signatures; `fieldModel` defines their meaning:

''',sample('Witgen/Typed/Field.lean','def fieldModel','/-- Every field feature'),'''

A field value is `Fin (modulus f)`. The arithmetic definitions use canonical residues:

''',sample('Witgen/Typed/Types.lean','def ofNat','@[simp] theorem square_spec'),
 sample('Witgen/Typed/FieldInverses.lean','def inverseNat','namespace Residue'),
 sample('Witgen/Typed/FieldInverses.lean','def neg','@[simp] theorem inv_val'),'''

Subtraction is modular and requires two operands from the same field:

''',sample('MainExtended.lean','def subProgram','def sqrtProgram'),'''

Inversion is total: `Inv 0 = 0`; for nonzero `x`, `x * Inv x = 1`. Implementations preserve the model under their representation relation.

### Optional Square Roots

`field.Sqrt x` returns `Option` of the same field: `some 0` at zero, `none` for nonsquares, and the smaller canonical representative of the two roots otherwise. The root choice is the same in the Lean model, Arkworks, and the Nat/GMP implementation. Squaring a returned root recovers the input.

''',sample('MainExtended.lean','def sqrtProgram','def sqrtSquareProgram'),
 sample('MainExtended.lean','def sqrtMatchProgram','private def sqrtInputs'),'''

Only matching the result requires `ValueOp`; calling `Sqrt` needs just the field capability. Here the `none` branch explicitly chooses zero; the square-root operation itself does not disguise a nonsquare as zero.

### Authoring Helpers

The helpers construct typed calls:

''',sample('Witgen/Typed/Field.lean','def Const','end Witgen.field'),'''

The operand types select the mathematical field, not Arkworks, GMP, or a U64 implementation. Field identity remains in the IR and method signatures even when representations share the same word layout.

## 2. Generic Elliptic Curves

A curve descriptor associates point types with a base field, scalar field, and Weierstrass equation. secp256k1 is one instance:

''',sample('Witgen/Typed/Types.lean','structure CurveId','inductive Ty'),'''

The feature is indexed by that descriptor:

''',sample('Witgen/Typed/Curve.lean','inductive CurveOp','namespace Curve'),'''

`curve.Mul` takes a scalar and a point. `curve.MSM` takes a list of `(scalar, point)` pairs, avoiding separate length-matching requirements. `curve.Eq` compares mathematical points and returns a Bool.

### Mathematical Specification

The model uses Mathlib's actual nonsingular Weierstrass points, including infinity:

''',sample('Witgen/Typed/Curve.lean','structure Math','abbrev AffinePair'),
 sample('Witgen/Typed/Curve.lean','def mul {','theorem literal_point_spec'),
 sample('Witgen/Typed/Curve.lean','def model {','theorem const_spec'),'''

The empty MSM returns the identity. Scalar multiplication uses the scalar's canonical natural representative. The native secp256k1 implementation uses Arkworks, including its multiscalar multiplication.

### Capability-Polymorphic Programs

A reusable program names the capabilities it needs; it does not fix the entire feature bundle. The concrete `F` is selected when instantiating or exporting the program:

''',sample('Witgen/Typed/CurvePrograms.lean','def mixed {','def roundtrip {'),'''

The first arithmetic operations use `c.scalar`. After `ToAffine`, the coordinate operations use `c.base`. Points from different curve descriptors, or a base-field element supplied as a scalar, are rejected by typing.

### Affine Conversion and Pattern Matching

`ToAffine` returns `None` at infinity and `Some (x, y)` for finite points. `FromAffine` returns an optional point after checking runtime coordinates.

''',sample('Witgen/Typed/CurvePrograms.lean','def roundtrip {','def curveEq {'),'''

This program returns `Some p` for a finite point and `None` for infinity. In the `none` case, the reconstruction branch is skipped. In the `some coordinates` case, the pattern binds the pair used by `FromAffine`.

The match requires `ValueOp`, which supplies option construction and case analysis. It elaborates to two typed regions: one for `none`, and one receiving the `some` payload. Outer variables used by branches are carried as explicit region inputs in the finite AST.

### Point Constants

`curve.Const` takes a statically checked literal and returns a point directly. The literal is tied to the descriptor's equation:

''',sample('Witgen/Typed/Curve.lean','inductive CurveLiteral','def CurveLiteral.point'),
 sample('Witgen/Typed/SecpCurve.lean','def generatorLiteral','theorem discriminant_ne_zero'),
 sample('Witgen/Typed/AffineExamples.lean','def constantGenerator','theorem roundtripProgram_eval'),'''

Invalid coordinates cannot supply the literal's proof. Infinity has its own literal constructor.

## 3. Branching and Structures

### Conditional Branches

Branching requires `BranchOp`. A Bool sort is enough to hold the condition; no separate Boolean-logic feature is required. The condition can be an input or the result of `curve.Eq`.

''',sample('Witgen/Branching/Programs.lean','def conditional {','def matchFallback {'),'''

The surface `if` elaborates to the following feature. Both branches have the same result type and receive the explicitly captured inputs:

''',sample('Witgen/Branching/Basic.lean','inductive BranchOp','@[simp]'),'''

Its model evaluates only the selected region. A `match` can likewise return a non-optional result:

''',sample('Witgen/Branching/Programs.lean','def matchFallback {','def negative {'),'''

Here, `none` selects negation of the fallback, while `some x` selects inversion of `x`. The branch results have the same field type.

### Functional Structures

`struct.Named`, `struct.Get`, and `struct.Set` work with caller-owned schemas:

''',sample('Witgen/Structs.lean','inductive StructOp','/-- Explicit isomorphism'),'''

`Set` returns a new record. The original record and its other fields remain unchanged:

''',sample('Witgen/StructSetTests.lean','def updatePair','example : updatePair'),'''

The generic laws cover get-after-set, other-field preservation, restoration, last-write-wins, and preservation of the representation relation. `StructRepr` supplies pack/unpack inverse laws. Named construction follows the schema; duplicate names and wrong replacement types are rejected.

Custom types can be represented through custom features and lowered to structures. [Checked custom lowering](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Custom.lean).

## 4. Shared Methods

A method has a typed signature and a finite `Program` body. A call stores a typed reference, not a copy of that body:

''',sample('Witgen/Methods.lean','structure MethodSig','inductive Ref'),
 sample('Witgen/Methods.lean','inductive CallOp','abbrev MethodValue'),'''

Definitions can refer to earlier definitions. The interpreter evaluates their stored bodies; refinement and substitution theorems let callers reuse method correctness. Native emission writes definitions once and retains calls, including when several callers share one library.

`field.Square` has a dedicated specification and a certified `Mul x x` fallback. A native backend may use an optimized square; the U64 library's Square method calls Mul.

## 5. Field → Nat: GMP Backend

The same source is instantiated for field, Nat-method, and U64-method representations:

''',sample('Witgen/Typed/Examples.lean','def fieldProgram','def fieldProgramNat'),'''

Nat method bodies unpack, perform arbitrary-precision arithmetic and explicit modular reduction, and repack. Pack/unpack do not normalize incorrect results.

Actual emitted secp-scalar multiplication and squaring methods:

''',sample('backend/src/generated_methods/module_5.rs','// method 1:','// program:',language='rust'),'''

The caller retains method calls:

''',sample('backend/src/generated_methods/module_5.rs','pub fn run(','fn decode_0',language='rust'),'''

`NatField<2>` preserves field identity. GMP is an implementation choice; the refinement compares the entire raw result, without an extra modulo operation in the relation.

## 6. Field → U64: Shared Word Methods

A field element becomes four U64 limbs. The arithmetic library contains three shared Add/Mul/Square bodies and nine thin wrappers for the three registered field identities. Multiple callers use one emitted copy of this library.

Actual secp-scalar caller:

''',sample('backend/src/generated_methods/shared_u64.rs','pub fn program_11(','fn program_11_decode_0',language='rust'),'''

The multiplication body is stored once as a bounded loop. Its Add operations remain calls:

''',sample('backend/src/generated_methods/shared_u64.rs','// method 1:','// method 3:',language='rust'),'''

The 256-bit Horner/double-add loop uses word carry/borrow operations. Modular addition handles carry beyond the fourth limb. Its correctness theorem applies to every positive modulus below $2^{256}$ and canonical inputs.

`Word4.Add_correct`, `Mul_correct`, and `Square_correct` prove raw decoding and canonicality. Separate theorems connect the stored method bodies to those algorithms. `U64.certified` proves preservation for successfully instantiated callers, with acceptance checked before obtaining a target program.

## 7. Caliper Integration and Runtime Proofs

Caliper consumes only the U64-level program. Higher-level operations are lowered by implementation/instantiation passes before this backend; Caliper itself has no field or curve implementations.

The parameterized word modular-multiplication example has checked total-correctness and exact-cost declarations:

''',sample('Witgen/Backends/CaliperRuntimeGuide.lean','theorem modMul_runtime','end Witgen.Backends.CaliperRuntimeGuide'),r'''

Its `.cycles` charge is 99, with net/peak buffer-capacity growth 6/6. This is not a Rust runtime or measured hardware timing. `Exec` carries exact values; `Triple` supplies terminating executions with upper bounds.

For a memory-neutral producer and a fresh $n$-word output buffer:

$$
\begin{aligned}
T_{\mathrm{full}} &= T_{\mathrm{producer}} + C.\mathrm{memAlloc}\\
&\quad + n\,C.\mathrm{allocPerWord} + n\,C.\mathrm{memPush}.
\end{aligned}
$$

The charge includes buffer reservation and initialization. Parsing and code generation are outside this example's clock; buffer capacity excludes registers.
''']

output=REPO/'doc/witgen-dsl-design.md'
output.write_text('\n'.join(parts).rstrip()+'\n')
(PACKAGE/'artifacts').mkdir(exist_ok=True)
(PACKAGE/'artifacts/design-snippets.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(output)
