# Clean WitGen DSL

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


[Witgen/Typed/Field.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Field.lean#L6-L10)

```lean
inductive FieldOp (f : FieldId) : Signature Ty where
  | const (n : Nat) : FieldOp f [] [] (.field f)
  | add : FieldOp f [.field f, .field f] [] (.field f)
  | mul : FieldOp f [.field f, .field f] [] (.field f)
  | square : FieldOp f [.field f] [] (.field f)
```



### Semantics

`FieldOp` declares the operation signatures. Its specification is the model below, independent of the backend implementation:


[Witgen/Typed/Field.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Field.lean#L12-L17)

```lean
def fieldModel (f : FieldId) : Model (FieldOp f) FieldVal where
  eval := fun op args _ => match op, args with
    | .const n, .nil => Residue.ofNat (modulus_pos f) n
    | .add, .cons a (.cons b .nil) => Residue.add a b
    | .mul, .cons a (.cons b .nil) => Residue.mul a b
    | .square, .cons a .nil => Residue.square a
```



A field value is `Fin (modulus f)`. The residue definitions specify canonical modular arithmetic directly:


[Witgen/Typed/Types.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Types.lean#L34-L38)

```lean
def ofNat {p : Nat} (hp : 0 < p) (n : Nat) : Fin p := ⟨n % p, Nat.mod_lt n hp⟩
def add {p : Nat} (a b : Fin p) : Fin p := ofNat (Nat.zero_lt_of_lt a.isLt) (a.val + b.val)
def mul {p : Nat} (a b : Fin p) : Fin p := ofNat (Nat.zero_lt_of_lt a.isLt) (a.val * b.val)
/-- Dedicated square semantics, not an alias at the operation boundary. -/
def square {p : Nat} (a : Fin p) : Fin p := ofNat (Nat.zero_lt_of_lt a.isLt) (a.val ^ 2)
```



Each certified implementation/instantiation pass must preserve this model under its representation relation.

### Authoring Helpers

These helpers construct typed calls; they do not define the operations' semantics:


[Witgen/Typed/Field.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Field.lean#L79-L89)

```lean
def Const (f : FieldId) [Has (FieldOp f) F] (n : Nat) :
    Step F Γ (.field f) := call (FieldOp.const (f := f) n) .nil .nil

def Add [Has (FieldOp f) F] (a b : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.add (f := f)) h![a, b] .nil

def Mul [Has (FieldOp f) F] (a b : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.mul (f := f)) h![a, b] .nil

def Square [Has (FieldOp f) F] (a : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.square (f := f)) h![a] .nil
```



This is compile-time selection of a **mathematical functionality**, not automatic selection of Arkworks, GMP, or U64 implementation. Constants without operands name their field explicitly. A scalar-field value is not accepted where a base-field value is required, even when both physical representations contain four words.

The library registers BN254 Fr plus the distinct secp256k1 base and scalar fields. Their identities survive the IR, method signatures, and JSON metadata. This is a library-owned field family, not a field enumeration built into the generic core; adding another family still requires its semantics, codecs and implementations.

Here is the actual mixed-field example. The scalar arithmetic feeds point scaling, while base arithmetic consumes a coordinate of the computed point:


[Witgen/Typed/Public.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Public.lean#L21-L37)

```lean
def mixed : Program Secp.Feature
    [.field secp256k1.Scalar, .field secp256k1.Scalar, .field secp256k1.Base]
    (.field secp256k1.Base) :=
  witgen [s, t, b] do
    let ss ← field.Square s
    let st ← field.Mul ss t
    let alpha ← field.Add st s
    let g ← curve.Generator
    let p ← curve.Scale alpha g
    let minusG ← curve.Inv g
    let q ← curve.Add p minusG
    let x ← curve.X q
    let gx ← curve.X g
    let bb ← field.Square b
    let bx ← field.Mul bb x
    let output ← field.Add bx gx
    return output
```



The declared input types determine which `FieldOp f` instance each operation requires. `curve.Scale` only accepts the secp scalar sort. Tests reject base-as-scalar and cross-field arithmetic rather than guessing a coercion. `curve.X` is an explicitly total coordinate view with `X(identity)=0`; use optional affine conversion when the presence of affine coordinates matters.

`witgen [...] do` elaborates into the unchanged finite typed AST. Named bindings, checked named fields and reference aliases are supported. Its ambient-parameter interface is deliberately restricted: unknown callbacks, records, proof carriers and unresolved holes are rejected; global low-level builders remain trusted. This is not a sandbox or a kernel provenance theorem. [Exact authoring policy](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/docs/StructAuthoringAPI.md#closed-ambient-parameter-interface).

## 2. A secp256k1 Feature

The curve operations are one optional functionality, separate from field arithmetic:


[Witgen/Typed/SecpFeature.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/SecpFeature.lean#L6-L14)

```lean
inductive SecpOp : Signature Ty where
  | add : SecpOp [.point, .point] [] .point
  | scale : SecpOp [.field secpScalar, .point] [] .point
  | inv : SecpOp [.point] [] .point
  | generator : SecpOp [] [] .point
  | identity : SecpOp [] [] .point
  | x : SecpOp [.point] [] (.field secpBase)
  | toAffine : SecpOp [.point] [] (.option (.pair (.field secpBase) (.field secpBase)))
  | fromAffine : SecpOp [.pair (.field secpBase) (.field secpBase)] [] (.option .point)
```



`curve.Inv P` is the **group inverse** `−P`, not multiplicative field inversion. The source model uses Mathlib's actual Weierstrass curve with equation $y^2=x^3+7$, not a discrete-log or synthetic point representation. Both secp moduli have closed kernel-checked Lucas primality certificates. Scalar multiplication acts by the scalar's canonical natural representative; the implementation reuses Mathlib's binary scalar multiplication.

### Affine Coordinates

Affine coordinates are a pair of **base-field** elements. Optionality makes the exceptional cases explicit:

- `curve.ToAffine : Point → Option (Base × Base)` returns `None` at infinity.
- `curve.FromAffine : Base × Base → Option Point` returns `None` off the curve, including `(0,0)`.
- Invalid affine coordinates are never silently converted into the identity point.

The actual roundtrip is a finite program using an optional bind and a closed region:


[Witgen/Typed/AffineExamples.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/AffineExamples.lean#L13-L19)

```lean
def roundtripProgram : Program AffineFeature [.point] (.option .point) :=
  witgen [p] do
    let xy ← curve.ToAffine p
    let q ← value.Bind xy (witgen [coords] do
      let out ← curve.FromAffine coords
      return out)
    return q
```



`affine_roundtrip` and `fromAffine_isSome_iff` connect this API to the real curve equation. Concrete tests cover the generator, twice the generator, its inverse, high-width scalar multiplication and infinity.

### Native Implementation or Lowering

The native backend implements this feature with **Arkworks secp256k1**. That keeps the source point operations abstract and permits the backend's optimized implementation.

A backend without curve support would instead need a certified **curve → field** implementation; those field operations could then use the **Field → U64** path below. The current revision implements the Arkworks curve backend and the field lowerings, **not** a curve-to-field or curve-to-U64 lowering. It does not claim a proof of the generator order/cofactor or a modulo-order module action law.

## 3. Functional Structures

`struct.Named`, `struct.Get`, and `struct.Set` operate on caller-owned schemas. There is no separate operation constructor for each record type. `StructOp.set` takes the old record and one typed replacement field and returns a new record:


[Witgen/Structs.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Structs.lean#L94-L101)

```lean
inductive StructOp {S : Type} {Schema : Type}
    (desc : Schema → StructDesc S) : Signature S where
  | make (schema : Schema) : StructOp desc (desc schema).sorts [] (desc schema).result
  | get (schema : Schema) {name : String} {t : S}
      (field : FieldRef (desc schema).fields name t) : StructOp desc [(desc schema).result] [] t
  | set (schema : Schema) {name : String} {t : S}
      (field : FieldRef (desc schema).fields name t) :
      StructOp desc [(desc schema).result, t] [] (desc schema).result
```



Updating a structure is **functional**, not a mutable store. Other fields and the original record remain available unchanged:


[Witgen/StructSetTests.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/StructSetTests.lean#L7-L18)

```lean
def updatePair : Program (StructOp desc) [.pair, .number] .pair :=
  witgen [old, value] do
    let fresh ← struct.Set desc .pair "right" old value
    return fresh

def oldAndNew : Program (StructOp desc) [.pair, .number] .pair :=
  witgen [old, value] do
    let fresh ← struct.Set desc .pair "right" old value
    let before ← struct.Get desc .pair "right" old
    let after ← struct.Get desc .pair "right" fresh
    let result ← struct.Named desc .pair fields![left := before, right := after]
    return result
```



The generic laws prove get-after-set, preservation of other fields, restoring an existing field, last-write-wins, and preservation of the representation relation. `StructRepr` still requires both pack/unpack inverse laws. Duplicate field names and wrong replacement sorts are rejected. Named construction follows the schema's declared field order.

A backend can implement this with a copy/update or a layout transformation. The Caliper backend changes the returned register layout without writing the old record's registers. Lists and optional/pair values remain separate optional library features.

Custom circuit types can still be exposed through custom features and lowered to structures. The checked `SplitWitness` example changes the native record carrier to a field `HList`; arithmetic stays in the lowered AST, not in a hidden boundary adapter. [Custom lowering source](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Custom.lean).

## 4. Shared Methods

A method has a typed signature and a finite `Program` body. A call contains a typed reference, **not** the body or a host function:


[Witgen/Methods.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Methods.lean#L8-L12)

```lean
structure MethodSig (S : Type) where
  name : String
  args : List S
  result : S
  deriving DecidableEq, Repr
```

[Witgen/Methods.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Methods.lean#L46-L56)

```lean
inductive CallOp {S : Type} (ms : List (MethodSig S)) : Signature S where
  | call (ref : Ref ms m) : CallOp ms m.args [] m.result

abbrev WithCalls (F : Signature S) (ms : List (MethodSig S)) : Signature S :=
  SigSum F (CallOp ms)

inductive Library {S : Type} (F : Signature S) : List (MethodSig S) → Type where
  | nil : Library F []
  | cons (prior : Library F ms) (sig : MethodSig S)
      (fresh : sig.name ∉ ms.map MethodSig.name)
      (body : Program (WithCalls F ms) sig.args sig.result) : Library F (sig :: ms)
```



A definition may refer only to earlier definitions. Names are unique; missing, forward, duplicate, wrong-name/index, and mismatched-signature calls are rejected. The library interpreter evaluates the stored AST bodies. Generic refinement and call-substitution theorems let a caller use each method's correctness result without expanding its proof at every call site.

This version deliberately supports **acyclic methods**, not recursion or an arbitrary dynamic linker. Native emission writes each definition once and retains calls. It also supports a shared library with multiple callers, so importing another caller does not duplicate the arithmetic bodies.

`field.Square` has its own operation/specification and a certified fallback to `field.Mul x x`. A native field backend can use its square implementation; the U64 method library implements Square by calling its existing Mul method.

## 5. Field → Nat: GMP Backend

Use the same source program for the direct field backend, the Nat-method backend and the U64-method backend:


[Witgen/Typed/Examples.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Examples.lean#L7-L13)

```lean
def fieldProgram (f : FieldId) : Program (FieldOp f) [.field f, .field f] (.field f) :=
  witgen [a,b] do
    let aa ← field.Square a
    let product ← field.Mul aa b
    let five ← field.Const f 5
    let out ← field.Add product five
    return out
```



The Nat method bodies unpack the scalar representation, perform arbitrary-precision arithmetic and **explicit** modular reduction, then repack it. Pack/unpack are raw layout operations and do not secretly normalize a wrong result.

Actual emitted secp-scalar multiplication and squaring methods:


[backend/src/generated_methods/module_5.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated_methods/module_5.rs#L20-L41)

```rust
// method 1: "field.2.mul.nat"
fn method_1(
    a0: typed::NatField<2>,
    a1: typed::NatField<2>,
) -> witgen_native::Result<typed::NatField<2>> {
    let v5: rug::Integer = (a0.clone()).0;
    let v6: rug::Integer = (a1.clone()).0;
    let v7: rug::Integer = v5.clone() * v6.clone();
    let v8: rug::Integer = v7.clone()
        % rug::Integer::from_str_radix(
            "115792089237316195423570985008687907852837564279074904382605163141518161494337",
            10,
        )?;
    let v9: typed::NatField<2> = typed::NatField::<2>(v8.clone());
    Ok(v9.clone())
}

// method 2: "field.2.square.nat"
fn method_2(a0: typed::NatField<2>) -> witgen_native::Result<typed::NatField<2>> {
    let v10: typed::NatField<2> = method_1(a0.clone(), a0.clone())?;
    Ok(v10.clone())
}
```



The generated caller retains three method calls rather than inserting their bodies:


[backend/src/generated_methods/module_5.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated_methods/module_5.rs#L44-L59)

```rust
pub fn run(
    a0: typed::NatField<2>,
    a1: typed::NatField<2>,
) -> witgen_native::Result<typed::NatField<2>> {
    let v11: typed::NatField<2> = method_2(a0.clone())?;
    let v12: typed::NatField<2> = method_1(v11.clone(), a1.clone())?;
    let v13: typed::NatField<2> = typed::NatField::<2>(
        rug::Integer::from_str_radix("5", 10)?
            % rug::Integer::from_str_radix(
                "115792089237316195423570985008687907852837564279074904382605163141518161494337",
                10,
            )?,
    );
    let v14: typed::NatField<2> = method_0(v12.clone(), v13.clone())?;
    Ok(v14.clone())
}
```



Field identity remains part of `NatField<2>`; the choice of GMP is a backend decision. The exact source-to-Nat relation includes the entire raw value, not equality only after another modular reduction.

## 6. Field → U64: Shared Word Methods

This is now an actual **four-limb U64 implementation**, including secp256k1 moduli near $2^{256}$. It is not a renamed field intrinsic or a Nat/GMP calculation hidden in a call.

The library contains:

- **Three generic arithmetic bodies:** Add, Mul and Square, with an explicit four-word modulus argument.
- **Nine thin field wrappers:** the three operations for each registered field identity.
- **One copy of that library** shared by the nine single-operation callers and three composed callers in the emitted unit.

The actual secp-scalar caller is small:


[backend/src/generated_methods/shared_u64.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated_methods/shared_u64.rs#L558-L567)

```rust
pub fn program_11(
    a0: typed::WordField<2>,
    a1: typed::WordField<2>,
) -> witgen_native::Result<typed::WordField<2>> {
    let v102: typed::WordField<2> = method_11(a0.clone())?;
    let v103: typed::WordField<2> = method_10(v102.clone(), a1.clone())?;
    let v104: typed::WordField<2> = typed::WordField::<2>([5u64, 0u64, 0u64, 0u64]);
    let v105: typed::WordField<2> = method_9(v103.clone(), v104.clone())?;
    Ok(v105.clone())
}
```



`method_11`, `method_10`, and `method_9` are the scalar-field Square/Mul/Add wrappers. The multiplication implementation itself is stored once as a bounded loop. Its two Add call sites remain calls:


[backend/src/generated_methods/shared_u64.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated_methods/shared_u64.rs#L50-L81)

```rust
// method 1: "u64.field.mul"
fn method_1(
    a0: typed::Word4,
    a1: typed::Word4,
    a2: typed::Word4,
) -> witgen_native::Result<typed::Word4> {
    let v34: typed::Word4 = [0u64, 0u64, 0u64, 0u64];
    let v41: typed::Word4 = {
        let mut acc36: typed::Word4 = v34.clone();
        for index35 in (0..256usize).rev() {
            acc36 = {
                let v37: typed::Word4 = method_0(a0.clone(), acc36.clone(), acc36.clone())?;
                let v38: typed::Word4 = method_0(a0.clone(), v37.clone(), a2.clone())?;
                let v39: bool = typed::bit_at(a1.clone(), index35.clone());
                let v40: typed::Word4 = if v39.clone() {
                    v38.clone()
                } else {
                    v37.clone()
                };
                v40.clone()
            };
        }
        acc36
    };
    Ok(v41.clone())
}

// method 2: "u64.field.square"
fn method_2(a0: typed::Word4, a1: typed::Word4) -> witgen_native::Result<typed::Word4> {
    let v42: typed::Word4 = method_1(a0.clone(), a1.clone(), a1.clone())?;
    Ok(v42.clone())
}
```



The reference multiplier uses a descending 256-bit Horner/double-add loop. Add uses word carry/borrow operations and handles the carry beyond the fourth limb; it does **not** assume the sum fits in 256 bits. Its conditional modulus subtraction is proved correct for every positive modulus below $2^{256}$ and canonical inputs. Dropping the high carry is an executed negative control.

`Word4.Add_correct`, `Mul_correct` and `Square_correct` prove raw decoding equals the required modular result and remains canonical. Separate theorems prove that the stored method ASTs evaluate to these word algorithms. `U64.certified` then supplies the actual Field→U64 refinement for callers; `caller_correct` is not a collection of hand-selected numerical equalities.

The native U64 method bodies use only word primitives, layouts, calls and the bounded loop. Nat values are used as proof/reference values and public loop indices; input parsing and decimal output serialization are outside the word-arithmetic body. The native emitter rejects unbounded external Nat interfaces in U64 mode. Raw `fromWord` wrappers do not repair outputs with a hidden modulo.

This is an inspectable **reference implementation**, not optimized Montgomery arithmetic and not a constant-time certificate. The loop evaluates both modular-add alternatives before selection. No native-speed claim follows from these correctness proofs.

## 7. Caliper Integration and Runtime Proofs

Caliper consumes only the U64-level program. Higher-level operations are lowered by implementation/instantiation passes before reaching this backend; Caliper itself has no field or curve implementations.

The parameterized word modular-multiplication example has checked total-correctness and exact-cost declarations:


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



Its `.cycles` charge is 99 with net/peak buffer-capacity growth 6/6. This is **not a Rust runtime or measured hardware timing**. `Exec` carries exact values; `Triple` supplies terminating executions with upper bounds.

For a memory-neutral producer and a fresh $n$-word output buffer, reserve and initialization are both charged:

$$
\begin{aligned}
T_{\mathrm{full}} &= T_{\mathrm{producer}} + C.\mathrm{memAlloc}\\
&\quad + n\,C.\mathrm{allocPerWord} + n\,C.\mathrm{memPush}.
\end{aligned}
$$

Input parsing, representation conversion and code generation are outside that example's clock; buffer capacity excludes registers.
