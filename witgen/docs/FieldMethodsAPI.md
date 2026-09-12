# Field/method integration seam (stable names)

Implemented API for `Witgen/Typed/**`, `Witgen/Methods.lean`, and the typed export entry points. Native execution and the shared U64 bundle are reproduced by `python3 tools/run_methods.py`.

## Shared sorts — `import Witgen.Typed.Types`

Namespace `Witgen.Typed`:

```lean
abbrev FieldId := Fin 3
def bn254Fr : FieldId := 0
def secpBase : FieldId := 1
def secpScalar : FieldId := 2
inductive Ty where
  | field (id : FieldId)
  | nat | bool | u64 | word4 | point
  | pair (left right : Ty) | option (element : Ty)
  deriving DecidableEq, Repr

def modulus : FieldId → Nat
theorem modulus_pos (f : FieldId) : 0 < modulus f
abbrev FieldValue (f : FieldId) := Fin (modulus f)
```

`Ty.field id` survives lowering: representation changes in the model, not the logical sort. U64 may use `Ty.u64`, `Ty.word4`, `Ty.nat`, `Ty.bool` for scratch values. `point` is specifically the secp256k1 curve point sort; it is not a field element.

## Generic methods — `import Witgen.Methods`

Namespace `Witgen.Methods`, generic in *any* core sort `S` and primitive signature `F : Signature S`:

```lean
structure MethodSig (S : Type) where
  name : String
  args : List S
  result : S
-- Intrinsic reference to an earlier signature (de Bruijn registry index).
inductive Ref : List (MethodSig S) → MethodSig S → Type
  | zero : Ref (m :: ms) m
  | succ : Ref ms m → Ref (n :: ms) m
inductive CallOp (ms : List (MethodSig S)) : Signature S
  | call (ref : Ref ms m) : CallOp ms m.args [] m.result
abbrev WithCalls (F : Signature S) (ms : List (MethodSig S)) := SigSum F (CallOp ms)
inductive Library (F : Signature S) : List (MethodSig S) → Type
  | nil : Library F []
  | cons (prior : Library F ms) (sig : MethodSig S)
      (fresh : sig.name ∉ ms.map MethodSig.name)
      (body : Program (WithCalls F ms) sig.args sig.result) : Library F (sig :: ms)
```

Bodies may use only earlier method refs, hence cannot recurse. Signatures, argument/result sorts, fresh names, and link availability are kernel checked. `Library.model (lib : Library F ms) (primitive : Model F V) : Model (WithCalls F ms) V` evaluates stored AST bodies, never a supplied per-method host oracle. `Ref.index` and `Ref.signature` expose export identity. `Library` has newest-first type index, export is oldest-first.

**U64 registration:** supply a primitive signature and model over `Ty`; construct a finite `Program (WithCalls U64Op prior) args result`. A call-free U64 AST is lifted with `Program.mapHandler Sum.inl`. Register using `Library.cons`. No inlining of bodies into callers is required. Suggested names include field identity: `field.1.mul.u64`, `field.2.square.u64`.

## Field feature — `import Witgen.Typed.Field`

`FieldOp (f : FieldId) : Signature Ty` has `.const n`, `.add`, `.mul`, `.square`. All input/result field sorts are `.field f`. Public `Witgen.field.Add/Mul/Square` infer `f` from `Var Γ (.field f)` arguments and require `Has (FieldOp f) F`. `Witgen.field.Const (f : FieldId) (n : Nat)` makes ambiguous constant identity explicit.

A lowering is a core `Handler`/`CertifiedLowering` mapping each field operation to a `CallOp` for the corresponding registered body; constants may also be methods (or primitive constants). `Square` remains one caller operation and has independent arithmetic spec plus proof of Mul(x,x) fallback.

## Codec — `import Witgen.Typed.Export`

`Witgen.Typed.typeJson : Ty → Lean.Json` emits field sorts as `{"field":<id>,"modulus":"<decimal>"}`; primitive nonfield sorts use stable string names, while point/pair/option use structural metadata. New generic metadata is `Witgen.Methods.OpCodec F := ∀ {args shapes result}, F args shapes result → Lean.Json`; each primitive returns an object with `op` and `static` (e.g. `{ "op":"u64.adcWord", "static":{} }`). The shared encoder attaches typed args/result, refs, regions, continuation. Call metadata contains `op:"method.call"`, `static:{name,index}`; method definitions are emitted once separately.

Primary exports: `Methods.programJson`, `Methods.libraryJson`, `Methods.moduleJson` accept explicit `encodeType : S → Json` and primitive `OpCodec F`. U64 supplies its primitive codec; typed call and registry export are generic. A call's `static.index` is a de Bruijn index into the **newest-first available library at that call site**. Definitions are emitted oldest-first: validate method-body indices against the reversed earlier-definition prefix, and caller indices against the reversed complete list. `static.name` must identify the same entry; argument/result metadata must match its signature.

## Reference lowering now available

`Witgen.Typed.NatMethods` is a complete `FieldOp f` → named Nat-method lowering, with `library f`, `handler f`, `lowering f`, `codec`. Add/Mul bodies explicitly unpack typed field values, execute Nat arithmetic and modulus, and repack; Square is a retained call to an earlier Mul method with aliased arguments. `handler_respects` and the resulting `CertifiedLowering.correct` connect AST body evaluation to Fin modular semantics. This is the reference path, not a substitute for the independent actual U64 implementation.

`Witgen.Typed.Examples.fieldProgram (f : FieldId)` is the shared source fixture (`Square(a); Mul(aa,b); Const f 5; Add(product,five)`), usable directly by U64 lowering. `fieldProgramNatJson` emits it through the Nat library. Executed `lake env lean --run MainTyped.lean nat`: caller has 3 retained method calls plus a typed literal, exactly 3 definitions; Square's definition calls earlier Mul with duplicated references. Fixture: `Witgen/Typed/fixtures/field_scalar_nat_methods.json`.

Additional generic proofs: `Library.ref_unique` identifies equal-name typed links, and `libraryJson_size` proves definitions emitted exactly once per registry entry.

## Pair/option extension (new user requirement)

Shared `Ty` includes `pair` and `option` recursively. The models, including U64.Val, interpret them as products and options; the codecs preserve their component types and field identities using `{ "pair": [typeJson a, typeJson b] }` and `{ "option": typeJson a }`.

`Witgen.Typed.SecpOp.toAffine` has arguments `[.point]`, result `.option (.pair (.field secpBase) (.field secpBase))`; `fromAffine` has arguments `[.pair (.field secpBase) (.field secpBase)]`, result `.option .point`. Public builders are `Witgen.curve.ToAffine` and `Witgen.curve.FromAffine`. `None` denotes infinity for ToAffine, and off-curve input for FromAffine; these are distinct operations, never silent invalid→infinity coercion. `Witgen.Typed.ValueOp` supplies generic pair/option construction/projection as an optional feature; no core feature added.

## U64 integration checked

`Witgen.Typed.U64Integration` imports `Witgen.U64.Lowering`. `u64FieldProgram f` lowers the shared source to named U64 methods, and `u64FieldProgram_correct` proves raw four-limb decoding equals the source Fin result. Runtime tests cover all three field IDs at inputs (3,4) and (p−1,p−1). No output normalization or substitute evaluator is used.

The word arithmetic and actual stored method bodies are checked independently of the native emitter. Native execution is covered by the parent methods runner.

## Verification and primary entry points

- `timeout 120s lake build Witgen.Typed.Audit` passes, including all field/method/affine/concrete secp tests.
- `Audit.lean` checks proof dependencies: only standard Lean `propext`, `Classical.choice`, `Quot.sound`; no compiler-trust or custom axioms.
- `import Witgen.Typed.Field`: inferred field API and certified Square fallback.
- `import Witgen.Methods`: core-generic acyclic registry, evaluator, substitution/refinement/link uniqueness, JSON exporter.
- `import Witgen.Typed.Examples`: generic source and named Nat lowering fixtures.
- `import Witgen.Typed.Secp`: concrete prime-certified curve, mixed base/scalar program, affine conversions.
- `MainTyped.lean` modes: default mixed source, `nat`, `u64`, `affine`, `from-affine`. `MainMethods.lean export DIR` emits the complete primary bundle and actual Lean fixtures; golden JSON is also in `Witgen/Typed/fixtures/`.
- `MainTyped.lean u64` exports the actual shared U64 lowering. The generated `field_scalar_u64_methods.json` has12 unique definitions,3 caller method calls plus a field literal, and one retained256-step loop. A programmatic pass validated every call's name/index/type against earlier definitions; no source field arithmetic operations remain.

## Final rebuild status

The typed/U64 modules build against functional Structs Set and the existing authoring guard. `python3 tools/run_methods.py` exports actual bodies, checks exact proof inventories, compiles native/Nat/U64 implementations and compares raw outputs with Lean and independent arithmetic. The native curve implementation uses Arkworks; curve→field lowering and full Caliper cost analysis of these methods are separate work, not implied by the arithmetic refinement.

## Coordination

Implementation checkpoint: `lake build Witgen.Methods Witgen.Typed.Field Witgen.Typed.Export Witgen.Typed.MethodTests` passes. `Library.model`, `Library.call_head`, `call_substitution`, `Library.names_unique`, `Library.earlier_only`, `Library.eval_related`, `Library.caller_refinement`, `programJson`, `libraryJson`, `moduleJson`, and `withCallsCodec` now exist with these signatures. `moduleJson encodeType codec lib name inputNames program` returns `Except String Json`; methods are dependency-order JSON definitions. U64 may import these now.

See `docs/U64FieldAPI.md` for the concrete word bodies and `docs/SecpAPI.md` for curve semantics. Method references and bodies are finite typed data; choosing a native implementation is separate from inferring field functionality from the input types.
