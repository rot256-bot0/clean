# Clean WitGen DSL

**Implementation reference.** Code blocks below are copied from the fork branch, not invented APIs. The new package is in `witgen/`; parent Clean's current circuit API/toolchain remain unchanged while this replacement is developed.

[Branch](https://github.com/rot256-bot0/clean/tree/feat/clean-witgen-dsl) · [Run instructions](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/README.md)

<details>
<summary>Contents</summary>

- [The Same Program, Different Targets](#1-the-same-program-different-targets)
- [Actual Rust Output](#2-actual-rust-output)
- [The Small Typed Core](#3-the-small-typed-core)
- [Proof-Bearing Lowering](#4-proof-bearing-lowering)
- [Map, Branch, and Records](#5-map-branch-and-records)
- [Circuits and Witness Cells](#6-circuits-and-witness-cells)
- [Verification and Limits](#7-verification-and-limits)

</details>

## 1. The Same Program, Different Targets

The source requests field arithmetic and record construction. `Has` chooses a typed feature embedding, not a native implementation.


[Witgen/Demo.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Demo.lean#L157-L164)

```lean
def quadratic {F : Signature Ty} [Has FieldOp F] [Has DataOp F] :
    Program F [.scalar, .scalar] .quad :=
  .let_ (Has.inject FieldOp.mul) (.cons .zero (.cons .zero .nil)) .nil <|
  .let_ (Has.inject FieldOp.add) (.cons .zero (.cons (.succ (.succ .zero)) .nil)) .nil <|
  .let_ (Has.inject DataOp.quad) (.cons (.succ .zero) (.cons .zero .nil)) .nil <|
  .ret .zero

def quadraticField : Program FieldSig [.scalar, .scalar] .quad := quadratic
```

The two arithmetic passes operate on that same AST:


[Witgen/Pipeline.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Pipeline.lean#L347-L351)

```lean
def quadraticNat : Program NatSig [.scalar, .scalar] .quad :=
  quadraticField.lower fieldToNat

def quadraticWord : Program WordSig [.scalar, .scalar] .quad :=
  quadraticNat.mapHandler natToWord
```

Field operations become target subprograms, including explicit modular reduction:


[Witgen/Pipeline.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Pipeline.lean#L134-L150)

```lean
def fieldScalarToNat : Template FieldOp NatSig
  | _, _, _, .const n, _ => emit (.inl (.const (n % 17))) .nil
  | _, _, _, .add, _ =>
      .let_ (.inl .add) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
      .let_ (.inl (.const 17)) .nil .nil <|
      .let_ (.inl .mod) (.cons (.succ .zero) (.cons .zero .nil)) .nil <| .ret .zero
  | _, _, _, .mul, _ =>
      .let_ (.inl .mul) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
      .let_ (.inl (.const 17)) .nil .nil <|
      .let_ (.inl .mod) (.cons (.succ .zero) (.cons .zero .nil)) .nil <| .ret .zero
  | _, _, _, .eq, _ => emit (.inl .eq) .nil

def fieldToNat : Template FieldSig NatSig
  | _, _, _, .inl op, regions => fieldScalarToNat op regions
  | _, _, _, .inr op, regions => emit (.inr op) regions

/-- Syntax only: no preservation assertion for arbitrary unbounded Nat programs. -/
```


The backend receives different remaining features:

- Source Field17 program → arkworks field operations.
- Field → Nat lowering → GMP-backed `rug::Integer` operations.
- Field → Nat → bounded UInt64 lowering → word operations.

All three use the same circuit and full witness layout. The word theorem is conditional on representability; this is not arbitrary bignum arithmetic squeezed into one word.

## 2. Actual Rust Output

Each example returns a native record, then the generated `populate` adapter writes its fields into the reserved witness cells. Input cells stay unchanged. The code is generated from the AST above, not transcribed from its evaluated result.

### Direct Field Backend


[backend/src/generated/quadratic_field.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated/quadratic_field.rs#L1-L26)

```rust
// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: witgen_native::F17,
    pub output: witgen_native::F17,
}

pub fn generate(x: witgen_native::F17, y: witgen_native::F17) -> Result<Quad, String> {
    let _wg0: witgen_native::F17 = witgen_native::f17_mul(x, x);
    let _wg1: witgen_native::F17 = witgen_native::f17_add(_wg0, y);
    let _wg2: Quad = Quad {
        square: _wg0,
        output: _wg1,
    };
    Ok((_wg2).clone())
}

pub fn populate(cells: &mut [witgen_native::F17; 4]) -> Result<(), String> {
    let result = generate(cells[0], cells[1])?;
    let _cell0 = result.square;
    let _cell1 = result.output;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
```


### After Field → Nat: GMP Backend


[backend/src/generated/quadratic_nat.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated/quadratic_nat.rs#L1-L33)

```rust
// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: rug::Integer,
    pub output: rug::Integer,
}

pub fn generate(x: rug::Integer, y: rug::Integer) -> Result<Quad, String> {
    let _wg0: rug::Integer = witgen_native::nat_mul(&x, &x);
    let _wg1: rug::Integer = witgen_native::nat_from_str("17")?;
    let _wg2: rug::Integer = witgen_native::nat_mod(&_wg0, &_wg1)?;
    let _wg3: rug::Integer = witgen_native::nat_add(&_wg2, &y);
    let _wg4: rug::Integer = witgen_native::nat_from_str("17")?;
    let _wg5: rug::Integer = witgen_native::nat_mod(&_wg3, &_wg4)?;
    let _wg6: Quad = Quad {
        square: (_wg2).clone(),
        output: (_wg5).clone(),
    };
    Ok((_wg6).clone())
}

pub fn populate(cells: &mut [witgen_native::F17; 4]) -> Result<(), String> {
    let result = generate(
        rug::Integer::from(witgen_native::f17_to_u64(cells[0])),
        rug::Integer::from(witgen_native::f17_to_u64(cells[1])),
    )?;
    let _cell0 = witgen_native::f17_from_nat(&result.square)?;
    let _cell1 = witgen_native::f17_from_nat(&result.output)?;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
```


### After Field → Nat → UInt64


[backend/src/generated/quadratic_word.rs](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated/quadratic_word.rs#L1-L33)

```rust
// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: u64,
    pub output: u64,
}

pub fn generate(x: u64, y: u64) -> Result<Quad, String> {
    let _wg0: u64 = witgen_native::word_mul(x, x);
    let _wg1: u64 = 17_u64;
    let _wg2: u64 = witgen_native::word_mod(_wg0, _wg1)?;
    let _wg3: u64 = witgen_native::word_add(_wg2, y);
    let _wg4: u64 = 17_u64;
    let _wg5: u64 = witgen_native::word_mod(_wg3, _wg4)?;
    let _wg6: Quad = Quad {
        square: _wg2,
        output: _wg5,
    };
    Ok((_wg6).clone())
}

pub fn populate(cells: &mut [witgen_native::F17; 4]) -> Result<(), String> {
    let result = generate(
        witgen_native::f17_to_u64(cells[0]),
        witgen_native::f17_to_u64(cells[1]),
    )?;
    let _cell0 = witgen_native::f17_from_u64(result.square)?;
    let _cell1 = witgen_native::f17_from_u64(result.output)?;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
```


For inputs `3,4`, every path fills `[3,4,9,13]`. The square is an actual witness cell, not an unexported local. A source-local `let` becomes a witness only through the explicit result/layout binding.

## 3. The Small Typed Core

The sort universe and feature signature are parameters. Records, words, lists, and control are in optional libraries, not kernel constructors. Return values are typed references; continuations and regions are finite syntax.


[Witgen/Core.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Core.lean#L7-L19)

```lean
structure RegionShape (S : Type) where
  inputs : List S
  output : S

abbrev Signature (S : Type) := List S → List (RegionShape S) → S → Type

inductive HList {S : Type} (V : S → Type) : List S → Type where
  | nil : HList V []
  | cons : V s → HList V ss → HList V (s :: ss)

inductive Var {S : Type} : List S → S → Type where
  | zero : Var (s :: Γ) s
  | succ : Var Γ s → Var (t :: Γ) s
```

[Witgen/Core.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Core.lean#L42-L50)

```lean
mutual
  inductive Program {S : Type} (F : Signature S) : List S → S → Type where
    | ret : Var Γ t → Program F Γ t
    | let_ : F args shapes s → HList (Var Γ) args → Regions F shapes →
        Program F (s :: Γ) t → Program F Γ t
  inductive Regions {S : Type} (F : Signature S) : List (RegionShape S) → Type where
    | nil : Regions F []
    | cons : Program F sh.inputs sh.output → Regions F rest → Regions F (sh :: rest)
end
```


Regions have explicit input contexts. Captures are passed as arguments, not hidden host closures. The optional demo library introduces actual record sorts and preserves their names/field order through Rust emission:


[Witgen/Demo.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Demo.lean#L9-L40)

```lean
inductive Ty where
  | scalar | bool | quad | modmul | list (element : Ty)
  deriving Repr, DecidableEq

/-- Native record identity and ordered named fields are library-owned metadata. -/
def Ty.recordName : Ty → Option String
  | .quad => some "Quad"
  | .modmul => some "ModMul"
  | _ => none

def Ty.recordFields : Ty → List (String × Ty)
  | .quad => [("square", .scalar), ("output", .scalar)]
  | .modmul => [("product", .scalar), ("quotient", .scalar), ("remainder", .scalar)]
  | _ => []

structure Quad (α : Type) where
  square : α
  output : α
  deriving Repr, DecidableEq

structure ModMul (α : Type) where
  product : α
  quotient : α
  remainder : α
  deriving Repr, DecidableEq

@[reducible] def Val (α : Type) : Ty → Type
  | .scalar => α
  | .bool => Bool
  | .quad => Quad α
  | .modmul => ModMul α
  | .list t => List (Val α t)
```


## 4. Proof-Bearing Lowering

A template supplies a target **subprogram** for each source operation. `Template.Respects` proves that subprogram implements the original feature semantics, uniformly over related region bodies. The generic theorem lifts the local proof through the caller and its continuation.


[Witgen/Core.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Core.lean#L296-L317)

```lean
abbrev Template (F G : Signature S) :=
  {args : List S} → {shapes : List (RegionShape S)} → {s : S} →
    F args shapes s → Regions G shapes → Program G args s

mutual
  def Program.lower (template : Template F G) : Program F Γ t → Program G Γ t
    | .ret r => .ret r
    | .let_ op args regions next =>
      ((template op (regions.lower template)).subst (fun r => r.get args)).bind
        (next.lower template)
  def Regions.lower (template : Template F G) : Regions F shapes → Regions G shapes
    | .nil => .nil
    | .cons body rest => .cons (body.lower template) (rest.lower template)
end

/-- Higher-order template contract. A source operation can become many target
operations, with arbitrary target internals but the same typed formal interface. -/
def Template.Respects (M : Model F V) (N : Model G W)
    (template : Template F G) (R : ∀ s, V s → W s → Prop) : Prop :=
  ∀ {args shapes s} (op : F args shapes s) xs ys fs (regions : Regions G shapes),
    HList.Rel R xs ys → HList.Rel (BodyRel R) fs (regions.eval N) →
    R s (M.eval op xs fs) ((template op regions).eval N ys)
```

[Witgen/Core.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Core.lean#L214-L218)

```lean
structure CertifiedLowering (M : Model F V) (N : Model G W)
    (R : ∀ s, V s → W s → Prop) where
  run : {Γ : List S} → {t : S} → Program F Γ t → Program G Γ t
  correct : ∀ {Γ t} (p : Program F Γ t) xs ys, HList.Rel R xs ys →
    R t (p.eval M xs) ((run p).eval N ys)
```

Manual composition preserves the intermediate representation relation. No automatic lowering planner is required.


[Witgen/Core.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Core.lean#L245-L258)

```lean
def CertifiedLowering.comp
    (a : CertifiedLowering M N R) (b : CertifiedLowering N P Q) :
    CertifiedLowering M P (RelComp R Q) where
  run := fun p => b.run (a.run p)
  correct := by
    intro Γ t p xs zs hr
    obtain ⟨ys, hxy, hyz⟩ := HList.relComp_factor R Q xs zs hr
    exact ⟨(a.run p).eval N ys, a.correct p xs ys hxy, b.correct (a.run p) ys zs hyz⟩

theorem CertifiedLowering.comp_correct
    (a : CertifiedLowering M N R) (b : CertifiedLowering N P Q)
    (p : Program F Γ t) xs zs (hr : HList.Rel (RelComp R Q) xs zs) :
    RelComp R Q t (p.eval M xs) (((a.comp b).run p).eval P zs) :=
  (a.comp b).correct p xs zs hr
```


## 5. Map, Branch, and Records

Map may remain available to the Rust backend, or be lowered on the Lean side to Fold plus list construction. The body remains typed code with explicit captures.


[Witgen/Pipeline.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Pipeline.lean#L414-L435)

```lean
def mapBodyToFold {F : Signature Ty} {captures : List Ty} {input output : Ty}
    (body : Program (Library F) (input :: captures) output) :
    Program (Library F) (input :: .list output :: captures) (.list output) :=
  (body.subst (RefSubst.lift (fun r => .succ r))).bind <|
    .let_ (.inr (.inl (.push output)))
      (.cons (.succ (.succ .zero)) (.cons .zero .nil)) .nil (.ret .zero)

def mapBlock {F : Signature Ty} {captures : List Ty} {input output : Ty}
    (body : Program (Library F) (input :: captures) output) :
    Program (Library F) (.list input :: captures) (.list output) :=
  .let_ (.inr (.inl (.empty output))) .nil .nil <|
  .let_ (.inr (.inr (.fold captures input (.list output))))
    (.cons (.succ .zero) (.cons .zero
      ((refs captures).map (fun r => .succ (.succ r)))))
    (.cons (mapBodyToFold body) .nil) (.ret .zero)

def mapToFold (F : Signature Ty) : Template (Library F) (Library F)
  | _, _, _, .inl op, regions => emit (.inl op) regions
  | _, _, _, .inr (.inl op), regions => emit (.inr (.inl op)) regions
  | _, _, _, .inr (.inr (.branch caps t)), regions => emit (.inr (.inr (.branch caps t))) regions
  | _, _, _, .inr (.inr (.fold caps a b)), regions => emit (.inr (.inr (.fold caps a b))) regions
  | _, _, _, .inr (.inr (.map _ _ _)), .cons body .nil => mapBlock body
```

The fixed-size gated circuit maps a branch-producing record body over three inputs:


[Witgen/Batch.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Batch.lean#L31-L43)

```lean
def gatedQuad {F : Signature Ty} [Has FieldOp F] [Has DataOp F] [Has Control F] :
    Program F [.scalar, .bool, .scalar] .quad :=
  .let_ (Has.inject (Control.branch [.scalar, .scalar] .quad))
    (.cons (.succ .zero) (.cons .zero (.cons (.succ (.succ .zero)) .nil)))
    (.cons quadratic (.cons zeroQuad .nil)) (.ret .zero)

def gatedBatch {F : Signature Ty} [Has FieldOp F] [Has DataOp F] [Has Control F] :
    Program F Context (.list .quad) :=
  .let_ (Has.inject (Control.map [.bool, .scalar] .scalar .quad))
    (.cons (.succ .zero) (.cons .zero (.cons (.succ (.succ .zero)) .nil)))
    (.cons gatedQuad .nil) (.ret .zero)

def gatedBatchField : Program FieldSig Context (.list .quad) := gatedBatch
```


The generated Rust uses real `if` and `for` constructs. Both branches return three records; disabled execution writes all six zeros. A short return is rejected before indexing or writing, not padded with fabricated values.

- [Direct batch Rust](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated/batch_field.rs)
- [Map → Fold → Field → Nat → UInt64 Rust](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/backend/src/generated/batch_fold_word.rs)

## 6. Circuits and Witness Cells

The circuit relation is independent of generator choice. A generator proves the **full** relation, including internal cells, rather than only the public output spec. Feature-relative completeness also fixes the boundary adapters: arbitrary host computation cannot be existentially hidden in a newly chosen encoder/decoder.


[Witgen/Circuits.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Circuits.lean#L11-L46)

```lean
structure Circuit (Input Witness Output : Type) where
  Assumptions : Input → Prop
  Relation : Input → Witness → Prop
  output : Witness → Output
  Spec : Input → Output → Prop
  sound : ∀ i w, Assumptions i → Relation i w → Spec i (output w)

section Generic
variable {Input Witness Output : Type}

/-- Feature-independent existence of a full satisfying witness. -/
def Circuit.MathematicallyComplete (C : Circuit Input Witness Output) : Prop :=
  ∀ i, C.Assumptions i → ∃ w, C.Relation i w

/-- Actual typed syntax, explicit semantic adapters, and the full relation proof.
Adapters belong to the semantic boundary; no claim is made that an arbitrary
adapter is a cost-free codec or implementable by the declared features. -/
structure FormalWitgen (C : Circuit Input Witness Output)
    {S : Type} {F : Signature S} {V : S → Type}
    (M : Model F V) (Γ : List S) (t : S) where
  program : Program F Γ t
  encodeInput : Input → HList V Γ
  decodeWitness : V t → Witness
  correct : ∀ i, C.Assumptions i →
    C.Relation i (decodeWitness (program.eval M (encodeInput i)))

/-- Completeness relative to exact features/model AND a fixed boundary ABI.
The adapters are parameters, not existential witnesses: otherwise arbitrary
host computation in an encoder/decoder could masquerade as an empty-feature
implementation. Native admission must separately implement this fixed ABI. -/
def CompleteOver (C : Circuit Input Witness Output)
    {S : Type} {F : Signature S} {V : S → Type} (M : Model F V)
    {Γ : List S} {t : S}
    (encodeInput : Input → HList V Γ) (decodeWitness : V t → Witness) : Prop :=
  ∃ p : Program F Γ t, ∀ i, C.Assumptions i →
    C.Relation i (decodeWitness (p.eval M (encodeInput i)))
```

The compiled field generator is the actual program stored in the certificate:


[Witgen/Integration.lean](https://github.com/rot256-bot0/clean/blob/feat/clean-witgen-dsl/witgen/Witgen/Integration.lean#L25-L35)

```lean
def quadraticFieldWitgen :
    FormalWitgen Quadratic.circuit fieldModel [.scalar, .scalar] .quad where
  program := quadraticField
  encodeInput := quadFieldInput
  decodeWitness := quadFieldOutput
  correct := by
    intro i _
    change Quadratic.Relation i
      (quadFieldOutput (quadraticField.eval fieldModel (quadFieldInput i)))
    rw [quadraticField_generates]
    exact Quadratic.gen_correct i
```


Layouts are fixed and proved complete. Native encoders validate every output before any store. The three circuit families are:

- Quadratic over field17: input cells `0,1`; square/output cells `2,3`.
- Modular multiplication over field257: inputs `0,1,2`; product/quotient/remainder `3,4,5`.
- Gated batch: inputs `0..4`; three square/output pairs `5..10`.

The modular multiplication pattern uses `a*b = q*n+r` and `r<n`; the example is not full RSA signature verification. The GMP path additionally executes raw modular multiplication on 4096-bit inputs without claiming those values fit the small field257 circuit.

## 7. Verification and Limits

The native comparison suite checks the actual Lean reference interpreter against emitted Rust and separately checks every circuit cell: **7,472 cases across18 variants**. Wrong-slot, missing-cell, bad-length, noncanonical-input and dirty-disabled-buffer controls are included. An exact named axiom audit rejects empty/missing reports and permits only the documented standard foundations.

```sh
cd witgen
python3 tools/run_demo.py
python3 -m unittest discover -s tests -v
```

**Proved:** typed scope, feature/subprogram lowering, composed semantics, full circuit witnesses and the pure vector writer.

**Tested TCB:** JSON encoding/checking, Rust printing, rustfmt/rustc, arkworks/GMP and native execution. Native division rejects zero; equivalence is claimed on the declared nonzero-divisor domains.

**Current limits:** pure semantics, explicit-input regions, fixed abstract sort indices with representation changes through model relations, and no general bignum-to-word pass or arbitrary dynamic type/procedure registry. Parent Clean's current WitnessIR has not been replaced by this package yet.
