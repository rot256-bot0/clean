# Structural feature / named authoring API

Implemented and kernel-checked coordination contract.
Imports: `Witgen.Structs`, `Witgen.Authoring` (both depend only on the generic core / Lean).
Namespace: `Witgen`.

```lean
structure StructDesc (S : Type) where
  name : String
  result : S
  fields : List (String × S)
  names_nodup : (fields.map Prod.fst).Nodup := by decide
-- d.sorts : List S := d.fields.map Prod.snd

inductive FieldRef : List (String × S) → String → S → Type
  | here : FieldRef ((name, t) :: rest) name t
  | there : FieldRef rest name t → FieldRef (field :: rest) name t
-- FieldRef.ref : FieldRef fields name t → Var (fields.map Prod.snd) t
-- NamedField fields name t: class with field `ref : FieldRef fields name t`
-- recursive instances provide checked literal-name lookup.

inductive StructOp {S : Type} {Schema : Type}
    (desc : Schema → StructDesc S) : Signature S
  | make (schema : Schema) : StructOp desc (desc schema).sorts [] (desc schema).result
  | get (schema : Schema) {name : String} {t : S}
      (field : FieldRef (desc schema).fields name t) :
      StructOp desc [(desc schema).result] [] t

structure StructRepr (V : S → Type) (d : StructDesc S) where
  pack : HList V d.sorts → V d.result
  unpack : V d.result → HList V d.sorts
  unpack_pack : ∀ xs, unpack (pack xs) = xs
  pack_unpack : ∀ x, pack (unpack x) = x
-- structModel (repr : ∀ k, StructRepr V (desc k)) : Model (StructOp desc) V
```

Caller supplies *any* `S`, schema key type, descriptor family and proved native-record/field-list isomorphisms. No Demo sorts, record-specific operation tags, or changes to Core are needed. Ordered fields are checked by the dependent argument list; names are checked by `NamedField` resolution. Duplicate names are forbidden by `names_nodup`. For anonymous constructor notation supply the fourth argument `by decide`; record notation fills this default automatically. Mark descriptor families `@[reducible] def` (and semantic value families too) so literal field-name instance search can reduce them.

`Witgen.Authoring` also provides named construction:
`makeNamedStruct desc schema (args : NamedArgs (Var Γ) (desc schema).fields) : Step F Γ (desc schema).result`.
Write `fields![square := square, output := output]`; both names **and order** are checked against the schema, not discarded. `getField desc schema "output" result` performs checked literal-name projection.

For real examples use smart arithmetic wrappers (`fieldMul x x`, `fieldAdd x c`, `fieldConst n`) returning `Step F Γ .scalar`. Demo now exports those names; Crypto should define its own versions with its field feature. Their implementation is `call FieldOp.mul h![x, y] .nil`. Main example style:

```lean
witgen [x, c] do
  let square ← fieldMul x x
  let output ← fieldAdd square c
  let result ← makeNamedStruct myDesc .myRecord
    fields![square := square, output := output]
  return result
```

Authoring returns the existing finite `Program`, not semantic closures. Low-level generic wrapper interface:

```lean
-- `call op args regions : Step F Γ t` injects op using Has.
-- `h![a, b, c]` constructs a typed heterogeneous argument list.
-- `makeStruct desc schema args : Step F Γ (desc schema).result`
-- `getField desc schema "name" value : Step F Γ t`
-- getField requires [NamedField (desc schema).fields "name" t].
-- A Step is only a temporary elaboration object; witgen consumes it into Program.let_.

def example {F : Signature MySort}
    [Has MyArithmetic F] [Has (StructOp myDesc) F] :
    Program F [.scalar, .scalar] .myRecord :=
  witgen [x, c] do
    let square ← call MyArithmetic.mul h![x, x] .nil
    let output ← call MyArithmetic.add h![square, c] .nil
    let result ← makeStruct myDesc .myRecord h![square, output]
    return result
```

`witgen [names...] do` names inputs in declared context order. Supported statements: named `let x ← step`, reference-alias `let x := reference`, and `return reference`; input references are automatically weakened through every operation binding. Nested closed regions use another `witgen [...] do` whose inputs explicitly list captures; pass them through `call`'s `Regions` argument. Pure non-reference lets and other unsupported do statements are rejected, rather than given guessed weakening semantics. Smart wrappers hide `.nil` and region-list plumbing. No `.succ`, `.cons`, or `Has.inject` belongs in author examples.

### Closed ambient-parameter interface

The elaborator uses a **fail-closed whitelist**, not a search for `Var` in type syntax. Every used ambient local (including dependencies in its type and let value) must fit one of these forms after reduction:

- Static scalar data: `Nat`, `Int`, `Bool`, `String`, `Char`, `PUnit`/`Unit`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `USize`, or `Fin n`. Reducible aliases are supported. This preserves static base/modulus arguments and ordinary host computations over them outside the block.
- Types and type-valued families, such as `S : Type`, `V : S → Type`, or `F : Signature S`. This does **not** admit a value `x : S` or a callback `Unit → S` whose carrier is abstract.
- `Has G F` dictionaries with a **bare abstract destination signature parameter** `F`, used only as direct instance arguments of fully applied global functions returning `Step` or `Program`. This preserves the feature-polymorphic smart wrappers and programs above. `Has` is not a reference-free marker: inspecting its fields as ambient data, aliasing/composing ambient dictionaries, or supplying an ambient dictionary with a concrete/let-defined destination is unsupported. Define a polymorphic program first, then instantiate its capabilities outside `witgen`.

Everything else is rejected, even if it happens to contain no references: ambient records/containers, values of abstract carriers, runtime callbacks, `Var`/`Step`/`Program` values, arbitrary typeclasses, and proof values (including `Nonempty`/`Exists`). Local sort/schema values and descriptor callbacks are not additional whitelist entries; define descriptors and helpers globally. The `implicit witgen capture 'name'` diagnostic conservatively covers these unsupported locals as well as actual references. A numeric let derived from an outer reference is still rejected through dependency traversal. All expression holes in the block and its used dependencies must be solved **before** entering the block; otherwise later assignments could evade validation.

Same-sorted outer references cannot silently become inner references after input reordering: use the inner block's own named inputs. Exact-diagnostic `#guard_msgs` tests cover aliased function results, boxed references, unknown carriers, class/proof carriers, local dependencies, and nested regions with definitionally identical contexts; positive controls check explicit reordering and the supported parameter forms.

This is an elaborator interface restriction, **not a kernel provenance theorem or a sandbox for arbitrary Lean code**. Global smart wrappers/AST builders remain trusted authoring code; the check does not inspect their implementations or prevent deliberate raw-reference construction or decoding numeric indices. The finite `Program` in `Witgen/Core.lean`, its scoping indices, and all existing semantic/proof contracts are unchanged.

Serialization is implemented and tested for a caller-defined sort universe:

```lean
Export.structTypeJson (encodeType : S → Lean.Json) (desc : StructDesc S) : Lean.Json
Export.programJsonWith (encodeType : S → Lean.Json)
  (info : Export.Info F) (program : Program F Γ t) : Lean.Json
Export.moduleJsonWith (encodeType : S → Lean.Json)
  (info : Export.Info F) (name domain : String) (inputNames : List String)
  (program : Program F Γ t) (layout : Option Lean.Json := none)
  (semanticInputs : String := "nat") : Except String Lean.Json
```

`Demo.structInfo` is itself generic in S/Schema/desc and returns `Demo.OpInfo`; it handles any `StructOp desc` with no schema dispatch. `Export.Info` is now generic in S as well. Use these for Crypto/custom exporters. `Export.moduleJson` remains the old Demo-only compatibility entry point.

Serialization coordination: generic structural operations use existing `record.make` and `record.get` tags; `get` exposes `field.ref.index`. Record type metadata must come from `StructDesc.name/fields`, preserving names and order. Scalar numeric representation/domain remains caller-owned. Demo's lists are a separate `ListOp` feature, never constructors of StructOp.


## Verified extension and integration seams

`Witgen.Custom` defines **its own** `Ty`, native `SplitWitness`, and `SplitOp`. `lowerSplit` expands a split operation into integer quotient/remainder and `StructOp.make`; custom projections become `StructOp.get`. The target record carrier is an `HList` of fields, not the native `SplitWitness`. `Related` states the complete representation relation. `lowerSplit_correct` instantiates `Program.eval_lower_related`; `certifiedLowering` is an actual `CertifiedLowering`. `splitProgram_satisfies` and `lowered_satisfies` establish reconstruction and low-limb bounds.

```sh
lake build Witgen.StructTests Witgen.AuthoringTests Witgen.AuthoringControlTests Witgen.CustomTests
lake env lean --run Main.lean custom-export /tmp/witgen-struct-custom
lake env lean --run Main.lean custom-fixtures /tmp/witgen-struct-custom/fixtures.json
```

Executed: 24 custom source/target/reconstruction evaluations, 578 same-sort branch/alias/capture evaluations, two exported custom modules (`custom_split`, `custom_low`), ten fixtures. The standard export/fixtures remain **18 / 7472**, untouched by the separate custom command. The custom JSON uses only existing `nat.*`, `record.make`, `record.get` tags. Parent owns native replay; no Rust verification is claimed here.

Caliper guide additions: `Witgen.Backends.CaliperRuntimeGuide.modMul_runtime` and `modMul_exact_cost` prove the parameterized **word** example's 99 abstract cycles / net 6 / peak 6. This is not a BN254 Caliper backend. Existing quadratic/regression theorems remain.

### Parent audit-inventory updates

`Witgen/Audit.lean`: 20 → **27** entries; no removed theorem. Added:

- `Witgen.StructRepr.get_pack`
- `Witgen.structModel_respects`
- `Witgen.Step.eval_bind`
- `Witgen.Custom.lowerSplit_law`
- `Witgen.Custom.lowerSplit_correct`
- `Witgen.Custom.splitProgram_satisfies`
- `Witgen.Custom.lowered_satisfies`

`Witgen/Backends/CaliperAudit.lean`: 82 → **88** entries. Replace `Witgen.Backends.Caliper.compileData_correct` with `Witgen.Backends.Caliper.compileAggregate_correct`; add:

- `Witgen.Backends.Caliper.read_env`
- `Witgen.Backends.Caliper.locSchema_respects`
- `Witgen.Backends.Caliper.compileStruct_correct`
- `Witgen.Backends.Caliper.compileList_correct`
- `Witgen.Backends.CaliperRuntimeGuide.modMul_runtime`
- `Witgen.Backends.CaliperRuntimeGuide.modMul_exact_cost`

All 30 non-Crypto `Witgen/*` Lean modules, `Main.lean`, and `MainCaliper.lean` checked successfully. Both axiom inventories ran; dependencies remain within `propext`, `Quot.sound`, and existing Caliper `Classical.choice`. Core source is unchanged. The Python independent inventories have been updated to match.

The supporting API documents use `StructOp schemaDesc` + `ListOp`, combined by `AggregateSig`, with `schemaRepr`, `aggregateModel`, and `aggregate_respects`. CoreAPI's separate bounded test feature is `FixtureOp`. Caliper's remaining sort-specific code is the declared **static layout representation/join**, not record-operation dispatch. It is not a universal arbitrary-schema whole-compiler certificate.
