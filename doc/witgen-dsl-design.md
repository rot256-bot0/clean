# Clean WitGen DSL

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

`field.Add`, `field.Mul`, `field.Square`, `field.Neg`, and `field.Inv` infer the field identity from their operands. Constants specify the field explicitly.


[Witgen/Typed/Field.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Field.lean#L6-L12)

```lean
inductive FieldOp (f : FieldId) : Signature Ty where
  | const (n : Nat) : FieldOp f [] [] (.field f)
  | add : FieldOp f [.field f, .field f] [] (.field f)
  | mul : FieldOp f [.field f, .field f] [] (.field f)
  | square : FieldOp f [.field f] [] (.field f)
  | neg : FieldOp f [.field f] [] (.field f)
  | inv : FieldOp f [.field f] [] (.field f)
```



### Semantics

`FieldOp` declares signatures; `fieldModel` defines their meaning:


[Witgen/Typed/Field.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Field.lean#L14-L21)

```lean
def fieldModel (f : FieldId) : Model (FieldOp f) FieldVal where
  eval := fun op args _ => match op, args with
    | .const n, .nil => Residue.ofNat (modulus_pos f) n
    | .add, .cons a (.cons b .nil) => Residue.add a b
    | .mul, .cons a (.cons b .nil) => Residue.mul a b
    | .square, .cons a .nil => Residue.square a
    | .neg, .cons a .nil => Residue.neg a
    | .inv, .cons a .nil => Residue.inv a
```



A field value is `Fin (modulus f)`. The arithmetic definitions use canonical residues:


[Witgen/Typed/Types.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Types.lean#L51-L55)

```lean
def ofNat {p : Nat} (hp : 0 < p) (n : Nat) : Fin p := ⟨n % p, Nat.mod_lt n hp⟩
def add {p : Nat} (a b : Fin p) : Fin p := ofNat (Nat.zero_lt_of_lt a.isLt) (a.val + b.val)
def mul {p : Nat} (a b : Fin p) : Fin p := ofNat (Nat.zero_lt_of_lt a.isLt) (a.val * b.val)
/-- Dedicated square semantics, not an alias at the operation boundary. -/
def square {p : Nat} (a : Fin p) : Fin p := ofNat (Nat.zero_lt_of_lt a.isLt) (a.val ^ 2)
```

[Witgen/Typed/FieldInverses.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/FieldInverses.lean#L15-L15)

```lean
def inverseNat (p a : Nat) : Nat := ((a : ZMod p)⁻¹).val
```

[Witgen/Typed/FieldInverses.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/FieldInverses.lean#L19-L24)

```lean
def neg {p : Nat} (a : Fin p) : Fin p :=
  ofNat (Nat.zero_lt_of_lt a.isLt) (p - a.val)

def inv {p : Nat} (a : Fin p) : Fin p :=
  letI : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt a.isLt)⟩
  ⟨inverseNat p a.val, ZMod.val_lt _⟩
```



Inversion is total: `Inv 0 = 0`; for nonzero `x`, `x * Inv x = 1`. Implementations preserve the model under their representation relation.

### Authoring Helpers

The helpers construct typed calls:


[Witgen/Typed/Field.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Field.lean#L87-L103)

```lean
def Const (f : FieldId) [Has (FieldOp f) F] (n : Nat) :
    Step F Γ (.field f) := call (FieldOp.const (f := f) n) .nil .nil

def Add [Has (FieldOp f) F] (a b : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.add (f := f)) h![a, b] .nil

def Mul [Has (FieldOp f) F] (a b : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.mul (f := f)) h![a, b] .nil

def Square [Has (FieldOp f) F] (a : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.square (f := f)) h![a] .nil

def Neg [Has (FieldOp f) F] (a : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.neg (f := f)) h![a] .nil

def Inv [Has (FieldOp f) F] (a : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.inv (f := f)) h![a] .nil
```



The operand types select the mathematical field, not Arkworks, GMP, or a U64 implementation. Field identity remains in the IR and method signatures even when representations share the same word layout.

## 2. Generic Elliptic Curves

A curve descriptor associates point types with a base field, scalar field, and Weierstrass equation. secp256k1 is one instance:


[Witgen/Typed/Types.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Types.lean#L26-L38)

```lean
structure CurveId where
  name : String
  base : FieldId
  scalar : FieldId
  a1 : FieldValue base := ⟨0, modulus_pos base⟩
  a2 : FieldValue base := ⟨0, modulus_pos base⟩
  a3 : FieldValue base := ⟨0, modulus_pos base⟩
  a4 : FieldValue base := ⟨0, modulus_pos base⟩
  a6 : FieldValue base := ⟨0, modulus_pos base⟩
  deriving DecidableEq, Repr

abbrev secp256k1 : CurveId :=
  { name := "secp256k1", base := secpBase, scalar := secpScalar, a6 := ⟨7, by decide⟩ }
```



The feature is indexed by that descriptor:


[Witgen/Typed/Curve.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Curve.lean#L32-L42)

```lean
inductive CurveOp (c : CurveId) : Signature Ty where
  | const (literal : CurveLiteral c) : CurveOp c [] [] (.point c)
  | add : CurveOp c [.point c, .point c] [] (.point c)
  | mul : CurveOp c [.field c.scalar, .point c] [] (.point c)
  | inv : CurveOp c [.point c] [] (.point c)
  | eq : CurveOp c [.point c, .point c] [] .bool
  | msm : CurveOp c [.list (.pair (.field c.scalar) (.point c))] [] (.point c)
  | generator : CurveOp c [] [] (.point c)
  | identity : CurveOp c [] [] (.point c)
  | toAffine : CurveOp c [.point c] [] (.option (.pair (.field c.base) (.field c.base)))
  | fromAffine : CurveOp c [.pair (.field c.base) (.field c.base)] [] (.option (.point c))
```



`curve.Mul` takes a scalar and a point. `curve.MSM` takes a list of `(scalar, point)` pairs, avoiding separate length-matching requirements. `curve.Eq` compares mathematical points and returns a Bool.

### Mathematical Specification

The model uses Mathlib's actual nonsingular Weierstrass points, including infinity:


[Witgen/Typed/Curve.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Curve.lean#L50-L61)

```lean
structure Math (c : CurveId) where
  basePrime : Fact (modulus c.base).Prime
  nonsingular : c.equation.Δ ≠ 0
  generator : c.equation.Point

abbrev Math.equation {c : CurveId} (_M : Math c) := c.equation

abbrev Math.Point {c : CurveId} (M : Math c) := M.equation.Point

instance {c : CurveId} (M : Math c) : AddCommGroup M.Point :=
  letI := M.basePrime
  inferInstanceAs (AddCommGroup M.equation.Point)
```

[Witgen/Typed/Curve.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Curve.lean#L67-L70)

```lean
def mul {c : CurveId} (M : Math c) (s : FieldValue c.scalar) (p : M.Point) : M.Point := s.val • p
def eq {c : CurveId} (M : Math c) (p q : M.Point) : Bool := decide (p = q)
def msm {c : CurveId} (M : Math c) (terms : List (FieldValue c.scalar × M.Point)) : M.Point :=
  (terms.map (fun (s,p) => s.val • p)).sum
```

[Witgen/Typed/Curve.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Curve.lean#L125-L138)

```lean
def model {c : CurveId} (M : Math c) : Model (CurveOp c) (Val M) where
  eval := fun op args _ =>
    letI := M.basePrime
    match op, args with
    | .const literal, .nil => literal.point
    | .add, .cons p (.cons q .nil) => p + q
    | .mul, .cons s (.cons p .nil) => mul M s p
    | .inv, .cons p .nil => -p
    | .eq, .cons p (.cons q .nil) => eq M p q
    | .msm, .cons terms .nil => msm M terms
    | .generator, .nil => M.generator
    | .identity, .nil => 0
    | .toAffine, .cons p .nil => toAffine M p
    | .fromAffine, .cons xy .nil => fromAffine M xy
```



The empty MSM returns the identity. Scalar multiplication uses the scalar's canonical natural representative. The native secp256k1 implementation uses Arkworks, including its multiscalar multiplication.

### Capability-Polymorphic Programs

A reusable program names the capabilities it needs; it does not fix the entire feature bundle. The concrete `F` is selected when instantiating or exporting the program:


[Witgen/Typed/CurvePrograms.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/CurvePrograms.lean#L8-L29)

```lean
def mixed {F : Signature Ty} (c : CurveId) [Has (CurveOp c) F]
    [Has (FieldOp c.scalar) F] [Has (FieldOp c.base) F] [Has ValueOp F] :
    Program F [.field c.scalar, .field c.scalar] (.option (.field c.base)) :=
  witgen [s,t] do
    let ss ← field.Square s
    let st ← field.Mul ss t
    let alpha ← field.Add st s
    let g ← curve.Generator c
    let p ← curve.Mul alpha g
    let minusG ← curve.Inv g
    let q ← curve.Add p minusG
    let xy ← curve.ToAffine q
    let result ← match xy with
      | none => value.None (.field c.base)
      | some coordinates =>
        let x ← value.Fst coordinates
        let y ← value.Snd coordinates
        let xx ← field.Square x
        let xxy ← field.Mul xx y
        let out ← field.Add xxy x
        value.Some out
    return result
```



The first arithmetic operations use `c.scalar`. After `ToAffine`, the coordinate operations use `c.base`. Points from different curve descriptors, or a base-field element supplied as a scalar, are rejected by typing.

### Affine Conversion and Pattern Matching

`ToAffine` returns `None` at infinity and `Some (x, y)` for finite points. `FromAffine` returns an optional point after checking runtime coordinates.


[Witgen/Typed/CurvePrograms.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/CurvePrograms.lean#L31-L38)

```lean
def roundtrip {F : Signature Ty} (c : CurveId) [Has (CurveOp c) F] [Has ValueOp F] :
    Program F [.point c] (.option (.point c)) :=
  witgen [p] do
    let xy ← curve.ToAffine p
    let out ← match xy with
      | none => value.None (.point c)
      | some coordinates => curve.FromAffine c coordinates
    return out
```



This program returns `Some p` for a finite point and `None` for infinity. In the `none` case, the reconstruction branch is skipped. In the `some coordinates` case, the pattern binds the pair used by `FromAffine`.

The match requires `ValueOp`, which supplies option construction and case analysis. It elaborates to two typed regions: one for `none`, and one receiving the `some` payload. Outer variables used by branches are carried as explicit region inputs in the finite AST.

### Point Constants

`curve.Const` takes a statically checked literal and returns a point directly. The literal is tied to the descriptor's equation:


[Witgen/Typed/Curve.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/Curve.lean#L18-L21)

```lean
inductive CurveLiteral (c : CurveId) where
  | infinity
  | affine (x y : FieldValue c.base)
      (valid : c.equation.Nonsingular (x.val : ZMod (modulus c.base)) (y.val : ZMod (modulus c.base)))
```

[Witgen/Typed/SecpCurve.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/SecpCurve.lean#L30-L32)

```lean
def generatorLiteral : CurveLiteral secp256k1 :=
  .affine (Residue.ofNat (modulus_pos secpBase) generatorX)
    (Residue.ofNat (modulus_pos secpBase) generatorY) generator_nonsingular
```

[Witgen/Typed/AffineExamples.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Typed/AffineExamples.lean#L34-L42)

```lean
def constantGenerator : Program (CurveOp secp256k1) [] (.point secp256k1) :=
  witgen [] do
    let p ← curve.Const secp256k1 generatorLiteral
    return p

def constantIdentity : Program (CurveOp secp256k1) [] (.point secp256k1) :=
  witgen [] do
    let p ← curve.Const secp256k1 .infinity
    return p
```



Invalid coordinates cannot supply the literal's proof. Infinity has its own literal constructor.

## 3. Branching and Structures

### Conditional Branches

Branching requires `BranchOp`. A Bool sort is enough to hold the condition; no separate Boolean-logic feature is required. The condition can be an input or the result of `curve.Eq`.


[Witgen/Branching/Programs.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Branching/Programs.lean#L22-L27)

```lean
def conditional {F : Signature Ty} (f : FieldId)
    [Has (FieldOp f) F] [Has (BranchOp Ty.bool) F] :
    Program F [.bool, .field f, .field f] (.field f) :=
  witgen [flag,a,b] do
    let out ← if flag then field.Mul a b else field.Add a b
    return out
```



The surface `if` elaborates to the following feature. Both branches have the same result type and receive the explicitly captured inputs:


[Witgen/Branching/Basic.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Branching/Basic.lean#L7-L17)

```lean
inductive BranchOp {S : Type} (bool : S) : Signature S where
  | branch (captures : List S) (result : S) :
      BranchOp bool (bool :: captures)
        [⟨captures, result⟩, ⟨captures, result⟩] result

/-- Region functions are selected, not eagerly evaluated branch values. -/
def BranchOp.model {S : Type} {bool : S} (V : S → Type)
    (toBool : V bool → Bool) : Model (BranchOp bool) V where
  eval := fun op args regions => match op, args, regions with
    | .branch _ _, .cons condition captures, .cons yes (.cons no .nil) =>
        if toBool condition then yes captures else no captures
```



Its model evaluates only the selected region. A `match` can likewise return a non-optional result:


[Witgen/Branching/Programs.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Branching/Programs.lean#L29-L36)

```lean
def matchFallback {F : Signature Ty} (f : FieldId)
    [Has (FieldOp f) F] [Has ValueOp F] :
    Program F [.option (.field f), .field f] (.field f) :=
  witgen [input,fallback] do
    let out ← match input with
      | none => field.Neg fallback
      | some x => field.Inv x
    return out
```



Here, `none` selects negation of the fallback, while `some x` selects inversion of `x`. The branch results have the same field type.

### Functional Structures

`struct.Named`, `struct.Get`, and `struct.Set` work with caller-owned schemas:


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



`Set` returns a new record. The original record and its other fields remain unchanged:


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



The generic laws cover get-after-set, other-field preservation, restoration, last-write-wins, and preservation of the representation relation. `StructRepr` supplies pack/unpack inverse laws. Named construction follows the schema; duplicate names and wrong replacement types are rejected.

Custom types can be represented through custom features and lowered to structures. [Checked custom lowering](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Custom.lean).

## 4. Shared Methods

A method has a typed signature and a finite `Program` body. A call stores a typed reference, not a copy of that body:


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



Definitions can refer to earlier definitions. The interpreter evaluates their stored bodies; refinement and substitution theorems let callers reuse method correctness. Native emission writes definitions once and retains calls, including when several callers share one library.

`field.Square` has a dedicated specification and a certified `Mul x x` fallback. A native backend may use an optimized square; the U64 library's Square method calls Mul.

## 5. Field → Nat: GMP Backend

The same source is instantiated for field, Nat-method, and U64-method representations:


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



Nat method bodies unpack, perform arbitrary-precision arithmetic and explicit modular reduction, and repack. Pack/unpack do not normalize incorrect results.

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



The caller retains method calls:


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



`NatField<2>` preserves field identity. GMP is an implementation choice; the refinement compares the entire raw result, without an extra modulo operation in the relation.

## 6. Field → U64: Shared Word Methods

A field element becomes four U64 limbs. The arithmetic library contains three shared Add/Mul/Square bodies and nine thin wrappers for the three registered field identities. Multiple callers use one emitted copy of this library.

Actual secp-scalar caller:


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



The multiplication body is stored once as a bounded loop. Its Add operations remain calls:


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



The 256-bit Horner/double-add loop uses word carry/borrow operations. Modular addition handles carry beyond the fourth limb. Its correctness theorem applies to every positive modulus below $2^{256}$ and canonical inputs.

`Word4.Add_correct`, `Mul_correct`, and `Square_correct` prove raw decoding and canonicality. Separate theorems connect the stored method bodies to those algorithms. `U64.certified` proves preservation for successfully instantiated callers, with acceptance checked before obtaining a target program.

## 7. Caliper Integration and Runtime Proofs

Caliper consumes only the U64-level program. Higher-level operations are lowered by implementation/instantiation passes before this backend; Caliper itself has no field or curve implementations.

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



Its `.cycles` charge is 99, with net/peak buffer-capacity growth 6/6. This is not a Rust runtime or measured hardware timing. `Exec` carries exact values; `Triple` supplies terminating executions with upper bounds.

For a memory-neutral producer and a fresh $n$-word output buffer:

$$
\begin{aligned}
T_{\mathrm{full}} &= T_{\mathrm{producer}} + C.\mathrm{memAlloc}\\
&\quad + n\,C.\mathrm{allocPerWord} + n\,C.\mathrm{memPush}.
\end{aligned}
$$

The charge includes buffer reservation and initialization. Parsing and code generation are outside this example's clock; buffer capacity excludes registers.
