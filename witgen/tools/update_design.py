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


parts=['''# Clean WitGen DSL

[Source branch](https://github.com/rot256-bot0/clean/tree/feat/clean-witgen-dsl) · [Run instructions](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/README.md)

The examples below are compiled source and actual emitted code. Features have typed operations and fixed semantics; certified transformations choose their implementations. Shared method bodies remain separate from their callers. The generic core has no mandatory field, structure, curve, or method-call feature.

<details>
<summary>Contents</summary>

- [Fields Are Selected by Types](#1-fields-are-selected-by-types)
- [A secp256k1 Feature](#2-a-secp256k1-feature)
- [Functional Structures](#3-functional-structures)
- [Shared Methods](#4-shared-methods)
- [Field → Nat](#5-field--nat-gmp-backend)
- [Field → U64](#6-field--u64-shared-word-methods)
- [Caliper Integration and Runtime Proofs](#7-caliper-integration-and-runtime-proofs)


</details>

## 1. Fields Are Selected by Types

`field.Mul`, `field.Add`, and `field.Square` infer the field identity from their operands. The field ID appears in both the sort and the requested feature:

''',sample('Witgen/Typed/Field.lean','inductive FieldOp','def fieldModel'),'''

### Semantics

`FieldOp` declares the operation signatures. Its specification is the model below, independent of the backend implementation:

''',sample('Witgen/Typed/Field.lean','def fieldModel','/-- Every field feature'),'''

A field value is `Fin (modulus f)`. The residue definitions specify canonical modular arithmetic directly:

''',sample('Witgen/Typed/Types.lean','def ofNat','@[simp] theorem square_spec'),'''

Each certified implementation/instantiation pass must preserve this model under its representation relation.

### Authoring Helpers

These helpers construct typed calls; they do not define the operations' semantics:

''',sample('Witgen/Typed/Field.lean','def Const','end Witgen.field'),'''

This is compile-time selection of a **mathematical functionality**, not automatic selection of Arkworks, GMP, or U64 implementation. Constants without operands name their field explicitly. A scalar-field value is not accepted where a base-field value is required, even when both physical representations contain four words.

The library registers BN254 Fr plus the distinct secp256k1 base and scalar fields. Their identities survive the IR, method signatures, and JSON metadata. This is a library-owned field family, not a field enumeration built into the generic core; adding another family still requires its semantics, codecs and implementations.

Here is the actual mixed-field example. The scalar arithmetic feeds point scaling, while base arithmetic consumes a coordinate of the computed point:

''',sample('Witgen/Typed/Public.lean','def mixed :','theorem mixed_eq'),'''

The declared input types determine which `FieldOp f` instance each operation requires. `curve.Scale` only accepts the secp scalar sort. Tests reject base-as-scalar and cross-field arithmetic rather than guessing a coercion. `curve.X` is an explicitly total coordinate view with `X(identity)=0`; use optional affine conversion when the presence of affine coordinates matters.

`witgen [...] do` elaborates into the unchanged finite typed AST. Named bindings, checked named fields and reference aliases are supported. Its ambient-parameter interface is deliberately restricted: unknown callbacks, records, proof carriers and unresolved holes are rejected; global low-level builders remain trusted. This is not a sandbox or a kernel provenance theorem. [Exact authoring policy](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/docs/StructAuthoringAPI.md#closed-ambient-parameter-interface).

## 2. A secp256k1 Feature

The curve operations are one optional functionality, separate from field arithmetic:

''',sample('Witgen/Typed/SecpFeature.lean','inductive SecpOp','namespace Secp'),'''

`curve.Inv P` is the **group inverse** `−P`, not multiplicative field inversion. The source model uses Mathlib's actual Weierstrass curve with equation $y^2=x^3+7$, not a discrete-log or synthetic point representation. Both secp moduli have closed kernel-checked Lucas primality certificates. Scalar multiplication acts by the scalar's canonical natural representative; the implementation reuses Mathlib's binary scalar multiplication.

### Affine Coordinates

Affine coordinates are a pair of **base-field** elements. Optionality makes the exceptional cases explicit:

- `curve.ToAffine : Point → Option (Base × Base)` returns `None` at infinity.
- `curve.FromAffine : Base × Base → Option Point` returns `None` off the curve, including `(0,0)`.
- Invalid affine coordinates are never silently converted into the identity point.

The actual roundtrip is a finite program using an optional bind and a closed region:

''',sample('Witgen/Typed/AffineExamples.lean','def roundtripProgram','def generatorRoundtrip'),'''

`affine_roundtrip` and `fromAffine_isSome_iff` connect this API to the real curve equation. Concrete tests cover the generator, twice the generator, its inverse, high-width scalar multiplication and infinity.

### Native Implementation or Lowering

The native backend implements this feature with **Arkworks secp256k1**. That keeps the source point operations abstract and permits the backend's optimized implementation.

A backend without curve support would instead need a certified **curve → field** implementation; those field operations could then use the **Field → U64** path below. The current revision implements the Arkworks curve backend and the field lowerings, **not** a curve-to-field or curve-to-U64 lowering. It does not claim a proof of the generator order/cofactor or a modulo-order module action law.

## 3. Functional Structures

`struct.Named`, `struct.Get`, and `struct.Set` operate on caller-owned schemas. There is no separate operation constructor for each record type. `StructOp.set` takes the old record and one typed replacement field and returns a new record:

''',sample('Witgen/Structs.lean','inductive StructOp','/-- Explicit isomorphism'),'''

Updating a structure is **functional**, not a mutable store. Other fields and the original record remain available unchanged:

''',sample('Witgen/StructSetTests.lean','def updatePair','example : updatePair'),'''

The generic laws prove get-after-set, preservation of other fields, restoring an existing field, last-write-wins, and preservation of the representation relation. `StructRepr` still requires both pack/unpack inverse laws. Duplicate field names and wrong replacement sorts are rejected. Named construction follows the schema's declared field order.

A backend can implement this with a copy/update or a layout transformation. The Caliper backend changes the returned register layout without writing the old record's registers. Lists and optional/pair values remain separate optional library features.

Custom circuit types can still be exposed through custom features and lowered to structures. The checked `SplitWitness` example changes the native record carrier to a field `HList`; arithmetic stays in the lowered AST, not in a hidden boundary adapter. [Custom lowering source](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Custom.lean).

## 4. Shared Methods

A method has a typed signature and a finite `Program` body. A call contains a typed reference, **not** the body or a host function:

''',sample('Witgen/Methods.lean','structure MethodSig','inductive Ref'),
 sample('Witgen/Methods.lean','inductive CallOp','abbrev MethodValue'),'''

A definition may refer only to earlier definitions. Names are unique; missing, forward, duplicate, wrong-name/index, and mismatched-signature calls are rejected. The library interpreter evaluates the stored AST bodies. Generic refinement and call-substitution theorems let a caller use each method's correctness result without expanding its proof at every call site.

This version deliberately supports **acyclic methods**, not recursion or an arbitrary dynamic linker. Native emission writes each definition once and retains calls. It also supports a shared library with multiple callers, so importing another caller does not duplicate the arithmetic bodies.

`field.Square` has its own operation/specification and a certified fallback to `field.Mul x x`. A native field backend can use its square implementation; the U64 method library implements Square by calling its existing Mul method.

## 5. Field → Nat: GMP Backend

Use the same source program for the direct field backend, the Nat-method backend and the U64-method backend:

''',sample('Witgen/Typed/Examples.lean','def fieldProgram','def fieldProgramNat'),'''

The Nat method bodies unpack the scalar representation, perform arbitrary-precision arithmetic and **explicit** modular reduction, then repack it. Pack/unpack are raw layout operations and do not secretly normalize a wrong result.

Actual emitted secp-scalar multiplication and squaring methods:

''',sample('backend/src/generated_methods/module_5.rs','// method 1:','// program:',language='rust'),'''

The generated caller retains three method calls rather than inserting their bodies:

''',sample('backend/src/generated_methods/module_5.rs','pub fn run(','fn decode_0',language='rust'),'''

Field identity remains part of `NatField<2>`; the choice of GMP is a backend decision. The exact source-to-Nat relation includes the entire raw value, not equality only after another modular reduction.

## 6. Field → U64: Shared Word Methods

This is now an actual **four-limb U64 implementation**, including secp256k1 moduli near $2^{256}$. It is not a renamed field intrinsic or a Nat/GMP calculation hidden in a call.

The library contains:

- **Three generic arithmetic bodies:** Add, Mul and Square, with an explicit four-word modulus argument.
- **Nine thin field wrappers:** the three operations for each registered field identity.
- **One copy of that library** shared by the nine single-operation callers and three composed callers in the emitted unit.

The actual secp-scalar caller is small:

''',sample('backend/src/generated_methods/shared_u64.rs','pub fn program_11(','fn program_11_decode_0',language='rust'),'''

`method_11`, `method_10`, and `method_9` are the scalar-field Square/Mul/Add wrappers. The multiplication implementation itself is stored once as a bounded loop. Its two Add call sites remain calls:

''',sample('backend/src/generated_methods/shared_u64.rs','// method 1:','// method 3:',language='rust'),'''

The reference multiplier uses a descending 256-bit Horner/double-add loop. Add uses word carry/borrow operations and handles the carry beyond the fourth limb; it does **not** assume the sum fits in 256 bits. Its conditional modulus subtraction is proved correct for every positive modulus below $2^{256}$ and canonical inputs. Dropping the high carry is an executed negative control.

`Word4.Add_correct`, `Mul_correct` and `Square_correct` prove raw decoding equals the required modular result and remains canonical. Separate theorems prove that the stored method ASTs evaluate to these word algorithms. `U64.certified` then supplies the actual Field→U64 refinement for callers; `caller_correct` is not a collection of hand-selected numerical equalities.

The native U64 method bodies use only word primitives, layouts, calls and the bounded loop. Nat values are used as proof/reference values and public loop indices; input parsing and decimal output serialization are outside the word-arithmetic body. The native emitter rejects unbounded external Nat interfaces in U64 mode. Raw `fromWord` wrappers do not repair outputs with a hidden modulo.

This is an inspectable **reference implementation**, not optimized Montgomery arithmetic and not a constant-time certificate. The loop evaluates both modular-add alternatives before selection. No native-speed claim follows from these correctness proofs.

## 7. Caliper Integration and Runtime Proofs

Caliper consumes only the U64-level program. Higher-level operations are lowered by implementation/instantiation passes before reaching this backend; Caliper itself has no field or curve implementations.

The parameterized word modular-multiplication example has checked total-correctness and exact-cost declarations:

''',sample('Witgen/Backends/CaliperRuntimeGuide.lean','theorem modMul_runtime','end Witgen.Backends.CaliperRuntimeGuide'),r'''

Its `.cycles` charge is 99 with net/peak buffer-capacity growth 6/6. This is **not a Rust runtime or measured hardware timing**. `Exec` carries exact values; `Triple` supplies terminating executions with upper bounds.

For a memory-neutral producer and a fresh $n$-word output buffer, reserve and initialization are both charged:

$$
\begin{aligned}
T_{\mathrm{full}} &= T_{\mathrm{producer}} + C.\mathrm{memAlloc}\\
&\quad + n\,C.\mathrm{allocPerWord} + n\,C.\mathrm{memPush}.
\end{aligned}
$$

Input parsing, representation conversion and code generation are outside that example's clock; buffer capacity excludes registers.


''']

output=REPO/'doc/witgen-dsl-design.md'
output.write_text('\n'.join(parts).rstrip() + '\n')
(PACKAGE/'artifacts').mkdir(exist_ok=True)
(PACKAGE/'artifacts/design-snippets.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(output)
