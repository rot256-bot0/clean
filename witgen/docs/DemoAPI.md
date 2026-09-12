# Demo library API (compiled)

Namespace `Witgen.Demo`; imports `Witgen.Demo` and `Witgen.Pipeline`.
The Core stays generic. This optional library supplies:

```lean
inductive Ty | scalar | bool | quad | modmul | list (element : Ty)
structure Quad (α : Type) where
  square : α
  output : α
structure ModMul (α : Type) where
  product : α
  quotient : α
  remainder : α
-- Val α : Ty → Type; records above and ordinary List (Val α element)
-- Scalar representations: Arithmetic.Field17, Nat, UInt64.
```

Finite feature signatures `FieldOp`, `NatOp`, `WordOp`, `DataOp`, `Control`.
Scalar operations: `const (n : Nat)`, `add`, `mul`, `eq`; Nat/Word also `div`, `mod`.
`DataOp`: `quad`, `square`, `output`, `modmul`, `product`, `quotient`,
`remainder`, `empty (element : Ty)`, `push (element : Ty)`.
`Control`: `branch (captures : List Ty) (result : Ty)`,
`map (captures : List Ty) (input output : Ty)`,
`fold (captures : List Ty) (element accumulator : Ty)`.

```lean
abbrev FieldSig := SigSum FieldOp (SigSum DataOp Control)
abbrev NatSig := SigSum NatOp (SigSum DataOp Control)
abbrev WordSig := SigSum WordOp (SigSum DataOp Control)
fieldModel : Model FieldSig (Val Arithmetic.Field17)
natModel : Model NatSig (Val Nat)
wordModel : Model WordSig (Val UInt64)
```

`FieldOp.info`, `NatOp.info`, `WordOp.info`, `DataOp.info`, `Control.info`,
and `fieldInfo`, `natInfo`, `wordInfo` return `OpInfo`:
`tag : String`, `literal : Option Nat`, `field : Option Nat`.
The parent emits JSON; `literal` belongs in static `value`, `field` in static `field`.
Tags match NativeSchema.md. `Ty.quad` emits record `Quad` with ordered fields
`[square: scalar, output: scalar]`; `Ty.modmul` emits `ModMul` with
`[product: scalar, quotient: scalar, remainder: scalar]`.
`Ty.recordName : Ty → Option String` and `Ty.recordFields : Ty → List (String × Ty)`
expose these record names and ordered named fields directly to the serializer.
`list.push` arguments are `[list, element]` and append at the end.

## Region calling convention (fixed)

Contexts and reference indices are newest-first. Captures are explicit and ordered:

- Branch arguments `[bool] ++ captures`; two regions, each `captures → result`.
- Map arguments `[list input] ++ captures`; one region `[input] ++ captures → output`.
- Fold arguments `[list element, accumulator] ++ captures`; one region
  `[element, accumulator] ++ captures → accumulator`.

Regions are closed syntax and never capture ambient variables implicitly.
The branch model evaluates exactly the selected region; map preserves input order;
fold is left-to-right. Native traversal visits *all* region ASTs, not evaluated outputs.

## Programs and transformations

`quadratic` is feature-polymorphic using `Has FieldOp F` and `Has DataOp F`:
inputs `[scalar,scalar] = [x,c]`; output `quad`; computes `square=x*x`,
`output=square+c`. `quadraticField : Program FieldSig [scalar,scalar] quad`.
`quadraticNat` is actual `Program.lower fieldToNat quadraticField`.
`quadraticWord` is actual `Program.mapHandler natToWord quadraticNat`.
`fieldToNat : Template FieldSig NatSig` expands each field add/mul into
primitive Nat add/mul, constant 17, and mod; literals are normalized modulo 17.
`natToWord : Handler NatSig WordSig` performs an actual AST transformation,
including nested regions. It has **no generic unbounded preservation claim**.
`fieldToWord : Template FieldSig WordSig` is the corresponding word macro.
Pipeline proves its local contract and proves syntactic commutation with the
Field→Nat→Word route. Field inputs are canonical residues and every intermediate
primitive sum/product is bounded. The endpoint is specialized to lowered field programs.

`modMulNat : Program NatSig [scalar,scalar,scalar] modmul` has inputs `[a,b,n]`;
it emits primitive product, division, modulo and a first-class full witness record.
`modMulWord := modMulNat.mapHandler natToWord`.
Correspondence requires `FitsU64 a`, `FitsU64 b`, `FitsU64 n`,
`FitsU64 (a*b)` and `0<n`, or sufficient hypotheses
`SmallModulus n`, `a<n`, `b<n`. It compares every record field, not just remainder.

## Generic map elimination and conditional examples

```lean
abbrev Library (F : Signature Ty) := SigSum F (SigSum DataOp Control)
libraryModel (M : Model F (Val α)) : Model (Library F) (Val α)
mapToFold (F : Signature Ty) : Template (Library F) (Library F)

mapToFold_correct (M : Model F (Val α))
  (p : Program (Library F) Γ t) (xs : HList (Val α) Γ) :
  (p.lower (mapToFold F)).eval (libraryModel M) xs =
    p.eval (libraryModel M) xs
```

`mapBodyToFold body` inserts the accumulator behind the element via typed
`Program.subst`, then `Program.bind`s the **original body** to a `list.push`.
`mapBlock body` emits `list.empty` and `control.fold` with the adapted body.
The body, element/output sorts, scalar representation, and capture context are
arbitrary; the proof is not specialized to doubling or quadratic arithmetic.
`mapToFold_law : Template.Respects ...` is lifted by Core's `eval_lower_related`.
The target signature still *permits* map, but the pass replaces every occurrence
of this library's map constructor. Example syntax tests verify its absence.

`batchQuadraticField` inputs are `[list scalar,scalar] = [xs,c]`, output `list quad`.
`conditionalBatchField` inputs are `[bool,list scalar,scalar] = [enabled,xs,c]`;
true returns the batch; false returns an empty record list.
All captures—including the list and c at the branch—are explicit inputs.

Available actual transformed ASTs:

- `batchQuadraticFoldField`, `batchQuadraticNat`, `batchQuadraticWord`.
- `conditionalBatchNat`, `conditionalBatchWord` (retain map).
- `conditionalBatchFoldField`, `conditionalBatchFoldNat`, `conditionalBatchFoldWord`
  (map→fold followed by arithmetic lowering).

`conditionalBatchFoldWord_correct b xs c` proves the complete resulting list of
records against the source quadratic specification for every list of Field17
inputs, both branch choices, and every c. Empty lists, order, captured records,
and captured nested lists are covered by tests.

## Exact proof endpoints

Every name below is in `Witgen.Demo`:

| Name | Contract |
|---|---|
| `fieldToNat_law`, `fieldToWord_law` | Local `Template.Respects` contracts, including related higher-order regions |
| `fieldToNat_correct p xs` | `Val.map Field17.toNat (p.eval fieldModel xs)` equals lowered Nat evaluation on mapped inputs |
| `fieldToWord_correct p xs` | Same, using `fieldWord x := UInt64.ofNat x.toNat` |
| `lower_commutes p` | `(p.lower fieldToNat).mapHandler natToWord = p.lower fieldToWord` **as syntax**, for all p |
| `natToWord_fieldImage_correct p xs` | Word evaluation decoded by `Val.map UInt64.toNat` equals Nat evaluation, restricted to actual lowered Field17 programs and canonical inputs |
| `quadraticNat_eval x c` | Exact Nat record `⟨x*x%17, (x*x%17+c)%17⟩`, for all Nat x,c |
| `quadraticNat_correct x c` | Complete record corresponding to source Field17 x,c |
| `quadraticWord_eval x c` | Complete word record corresponding to source Field17 x,c |
| `quadraticWord_correct x c` | Decoded word record equals canonical field result record |
| `quadraticWord_bounded x c hx hc` | Actual word pipeline equals Nat pipeline when `x<17` and `c<17` |
| `modMulNat_eval a b n` | Exact full record `⟨a*b, a*b/n, a*b%n⟩` |
| `modMulNat_satisfies a b n hn` | `Arithmetic.MulModRel` for actual Nat AST with `0<n` |
| `modMulWord_correct ha hb hn hp hpos` | Full-record equality for exact input/product representability and positive modulus |
| `modMulWord_small_correct hn ha hb` | Same under `0<n≤2^32`, `a<n`, `b<n` |
| `modMulWord_small_satisfies hn ha hb` | Actual word AST satisfies the unchanged full Nat witness relation |
| `mapToFold_correct M p xs` | Generic same-model preservation, including nested regions |
| `conditionalBatchFoldWord_correct b xs c` | Branch→map→fold→Field→Nat→Word complete record-list endpoint |

`ModMul.toArithmetic : ModMul Nat → Arithmetic.MulModWitness` connects the optional
record type to the arithmetic relation. `Val.map f` maps all scalar slots of
records and nested lists and leaves Bool unchanged. `Graph f t x y` is
`Val.map f x = y`; inputs are related using `graph_env`.

Generic syntax helpers in Pipeline, without Core modifications:
`mapHandler_subst`, `mapHandler_bind`, `lower_natural`, `regions_lower_natural`.
They prove handler/template naturality structurally; no output-only shortcut.

## Native traversal

`nativeOps info program : List OpInfo` and `nativeRegionOps info regions` are
preorder metadata traversals. They include *every* branch body, not just the
selected region. Use `fieldInfo`, `natInfo`, `wordInfo` according to the stage.
These helpers intentionally do not erase/reconstruct the typed AST: the parent
serializer must still emit the sorts, actual reference indices and full regions
from `Program.let_` / `Regions.cons` as specified in CoreAPI and NativeSchema.

Field constants normalize modulo 17; Nat constants are mathematical integers;
Word constants use `UInt64.ofNat` (wrapping). Argument indices determine record
field values in the declared order, independent of binder chronology.

## Limits and trust

- No generic unbounded Nat→Word preservation claim. Tests reject both arbitrary
  overflowing Nat addition and a modular multiplication whose product does not fit.
- Modular-mul certification requires positive modulus. Lean Nat/UInt64 division
  is total at zero; a native provider can reject/trap there instead. Only stated
  positive-modulus endpoints justify using that provider.
- All proofs concern pure Lean values. Effects, exceptions, evaluation costs,
  allocation, machine resources, foreign libraries, serialization, Rust emission,
  compiler optimizations, and FFI behavior are not kernel-proved.
- The RSA-inspired slice is product/quotient/remainder modular multiplication,
  not RSA-4096 signature verification or production limb/carry arithmetization.
- No added dependencies, custom axioms, proof placeholders, `native_decide`,
  unsafe shortcuts, or heartbeat/recursion-limit increases.

## Test-first receipts

This document was written before implementation so native serialization could
start against the fixed type/op/calling convention. The six vertical tracer
RED/GREEN runs were executed locally. Excerpts of actual RED output:

```text
1. error: object file '.../Witgen/Demo.olean' of module Witgen.Demo does not exist
2. error: object file '.../Witgen/Pipeline.olean' of module Witgen.Pipeline does not exist
3. error(lean.unknownIdentifier): Unknown identifier `modMulWord_correct`
   error(lean.unknownIdentifier): Unknown identifier `modMulNat.eval`
4. error(lean.unknownIdentifier): Unknown identifier `mapToFold_correct`
   error(lean.unknownIdentifier): Unknown identifier `batchQuadraticField.eval`
5. The identifier `nativeOps` is unknown
   error(lean.unknownIdentifier): Unknown identifier `quadraticWord_bounded`
6. error(lean.unknownIdentifier): Unknown constant `Witgen.Demo.Ty.recordName`
   error(lean.unknownIdentifier): Unknown constant `Witgen.Demo.Ty.recordFields`
```

Each tracer's `lake build Witgen.Demo` or `lake build Witgen.Pipeline` followed by
`lake env lean -DwarningAsError=true Witgen/DemoTests.lean` subsequently exited 0.
The first returned `{ square := 1, output := 4 }`; subsequent slices checked the
actual expanded arithmetic, three-cell modular witness, map→fold, and metadata.
The final executable tests also include exhaustive small-domain comparisons,
modulus `2^32`, 256-bit Nat operands, both branch choices, empty and ordered lists,
record/list captures, field equality/constants, and overflow negative controls.

The final build/axiom receipt follows; output is a filtered excerpt, not fabricated
native-backend output.

```sh
lake build Witgen.Demo Witgen.Pipeline Witgen.DemoTests Witgen.CoreTests Witgen.ArithmeticTests
lake env lean -DwarningAsError=true Witgen/Demo.lean
lake env lean -DwarningAsError=true Witgen/Pipeline.lean
lake env lean -DwarningAsError=true Witgen/DemoTests.lean
```

Exit code: `0`. Actual output excerpt:

```text
Build completed successfully (8 jobs).
quadratic: 289 Field17/Nat/UInt64 full-record checks passed
modmul: 1785 Nat/UInt64 full-record checks passed
modmul boundary 2^32: { product := 18446744065119617025, quotient := 4294967294, remainder := 1 }
large Nat: 256-bit operands satisfy the full product/quotient/remainder relation
["control.branch", "list.empty", "control.fold", "word.mul", "word.const", "word.mod", "word.add", "word.const",
 "word.mod", "record.make", "list.push", "list.empty"]
'Witgen.Demo.fieldToNat_correct' depends on axioms: [propext, Quot.sound]
'Witgen.Demo.fieldToWord_correct' depends on axioms: [propext, Quot.sound]
'Witgen.Demo.lower_commutes' depends on axioms: [propext, Quot.sound]
'Witgen.Demo.natToWord_fieldImage_correct' depends on axioms: [propext, Quot.sound]
'Witgen.Demo.quadraticWord_bounded' depends on axioms: [propext, Quot.sound]
'Witgen.Demo.modMulWord_correct' depends on axioms: [propext]
'Witgen.Demo.modMulWord_small_satisfies' depends on axioms: [propext]
'Witgen.Demo.mapToFold_correct' depends on axioms: [propext, Quot.sound]
'Witgen.Demo.conditionalBatchFoldWord_correct' depends on axioms: [propext, Quot.sound]
{ square := 1, output := 4 }
```

Only Lean's standard `propext` and `Quot.sound` appear in the listed pipeline
axiom dependencies; modular-mul endpoints need only `propext`.
