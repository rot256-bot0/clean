# Witgen core API / serialization seam

The initial version of this document preceded implementation. The interfaces below now compile on Lean 4.32.2 + Std.

## Imports and syntax

```lean
import Witgen.Core
open Witgen
```

`S : Type` is caller-defined. There are **no scalar, arithmetic, Boolean, aggregate, or control constructors in the kernel**. Universes are deliberately limited to `Type` (universe zero).

```lean
structure RegionShape (S : Type) where
  inputs : List S
  output : S
abbrev Signature (S : Type) := List S → List (RegionShape S) → S → Type

-- Intrinsically typed, newest-first de Bruijn references:
Var.zero : Var (s :: Γ) s
Var.succ : Var Γ s → Var (t :: Γ) s
-- Typed heterogeneous lists:
HList.nil : HList V []
HList.cons : V s → HList V ss → HList V (s :: ss)

Program.ret : Var Γ t → Program F Γ t
Program.let_ : F args shapes s → HList (Var Γ) args → Regions F shapes →
  Program F (s :: Γ) t → Program F Γ t
Regions.nil : Regions F []
Regions.cons : Program F sh.inputs sh.output → Regions F rest → Regions F (sh :: rest)
```

IR is finite inductive syntax. A `let_` continuation is another AST, **not** a Lean function. Regions see exactly their declared input context; ambient captures must become explicit inputs supplied by the owning operation. Extension operation constructors must contain reifiable static data, not executable semantic values/functions. The open `Signature` alias does not itself enforce a codec or forbid a poorly designed extension from hiding a function in its payload; all supplied fixtures use data-only constructors.

`Var.index` produces the de Bruijn index. `r.get env` looks up a typed value/reference. `HList.map` transforms heterogeneous lists pointwise.

## Semantics and embeddings

```lean
abbrev Body (V : S → Type) (sh : RegionShape S) := HList V sh.inputs → V sh.output
structure Model (F : Signature S) (V : S → Type) where
  eval : {args : List S} → {shapes : List (RegionShape S)} → {s : S} →
    F args shapes s → HList V args → HList (Body V) shapes → V s
```

Use `p.eval model env` and `regions.eval model`. Semantic body functions are created **by interpreting ASTs**; they are never IR fields. A feature model chooses which bodies to call.

`SigSum F G`, `Model.sum`, and `Has.inject` compose independent extensions. `Has` also requires injectivity. Identity/direct-left/direct-right instances exist; nested embeddings can be explicitly composed. Duplicate occurrences of the same feature should use explicit handlers to select a side.

```lean
abbrev Handler (F G : Signature S) :=
  {args : List S} → {shapes : List (RegionShape S)} → {s : S} →
    F args shapes s → G args shapes s
```

`Handler.id`, `Handler.comp`, `p.mapHandler h`, and `regions.mapHandler h` provide shape-preserving relabeling. It is only the simple specialization; **macro lowering below emits arbitrary target let chains**.

## Reference substitution, syntax bind, and macro lowering

```lean
abbrev RefSubst (Γ Δ : List S) := {s : S} → Var Γ s → Var Δ s
Program.subst (σ : RefSubst Γ Δ) (p : Program F Γ t) : Program F Δ t
Program.bind (p : Program F Γ s) (next : Program F (s :: Γ) t) : Program F Γ t

abbrev Template (F G : Signature S) :=
  {args : List S} → {shapes : List (RegionShape S)} → {s : S} →
    F args shapes s → Regions G shapes → Program G args s
Program.lower (template : Template F G) (p : Program F Γ t) : Program G Γ t
```

`p.subst σ` supports typed renaming, reordering, weakening, and duplication. It fixes each introduced binder using `RefSubst.lift`; closed region inputs are unaffected. `RefSubst.replaceHead` replaces a computed result binder. `p.bind next` retains the source continuation, inserting each extra let below its result binder.

`lower` recursively lowers regions, builds the target subprogram over the operation's formal argument context, substitutes its actual typed argument references, and binds its result to the recursively lowered **source** continuation. Template internals may contain arbitrary finite target operations and regions; only their formal input/result/region interfaces retain the source abstract sort indices.

The executable `Witgen.CoreTests.mulTemplate` expands modular multiplication into:

```lean
.let_ .mul (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
.let_ (.lit modulus) .nil .nil <|
.let_ .mod (.cons (.succ .zero) (.cons .zero .nil)) .nil <|
.ret .zero
```

`CoreTests.lowered_correct a b` proves the two-source-operation continuation computes `(a * b % 13) * a % 11` for every Nat input pair. `unreducedTemplate_rejected` proves that dropping the modulo cannot satisfy the unchanged local contract.

## Proof contracts and composition

`HList.Rel R xs ys` relates typed environments of the same shape. `BodyRel R sh f g` requires related outputs for **every pair of related input environments**.

* `Model.Respects M N h R`: local relabeling law, assuming related argument and semantic-body lists.
* `Template.Respects M N template R`: local macro law, assuming related arguments and related source semantic bodies versus the interpretations of actual target region ASTs.
* `Program.eval_subst M p σ env env' h`: substituted evaluation equals original evaluation if every substituted reference has the same value.
* `Program.eval_bind M p next env`: `(p.bind next).eval M env = next.eval M (.cons (p.eval M env) env)`.
* `Program.eval_mapHandler_related h M N R law p xs ys hr`: lifts the handler law through all instructions and nested regions.
* `Program.eval_lower_related template M N R law p xs ys hr`: the corresponding **operation-to-subprogram** preservation theorem, including higher-order bodies.
* `Regions.eval_mapHandler_related` / `Regions.eval_lower_related`: mutually proved body-list endpoints.

`CertifiedLowering M N R` contains `run` and its whole-program `correct` proof. Construct it with `.ofHandler M N h R law` or `.ofTemplate M N template R law`. Compose with `a.comp b`; `CertifiedLowering.comp_correct a b p xs zs hr` proves the composed result relation:

```lean
RelComp R Q s x z := ∃ y, R s x y ∧ Q s y z
```

Intermediate representation conditions are **retained**, not erased. The models may use different denotations of the same abstract sort. Certificates are total over environments satisfying their stated relation: this API does not supply program-specific overflow analysis or discharge arithmetic/range obligations automatically.

## Optional control/aggregate fixture

Import `Witgen.CoreTests`; namespace `Witgen.CoreTests.Optional`. This library fixture is deliberately outside the kernel.

`Ty`, `Val`, `MapRecord`, `FixtureOp`, and `Control` define numbers, lists, records, Boolean selection, and a left fold as independent extensions. `mapped` implements a doubling map via fold, returning a **first-class record** containing transformed values and an ordered visitation trace. `map_correct xs` proves both fields for every list, including empty lists.

`branch_true yes no` and `branch_false yes no` are definitional equalities to exactly the selected body's interpretation. The model calls only that body. Concrete tests return:

```text
true:  { values := [6, 2, 8], visits := [3, 1, 4] }
false: { values := [18, 16], visits := [9, 8] }
```

Further tests run `lower` through branch → fold → scalar-body nesting and run relabeling over the same structure. This is pure semantics, not a general effect/cost model or a proof about compiler optimization.

## Native serialization/emission seam

Traverse syntax, **not evaluation**:

1. `Program.ret ref`: record the result sort and resolve `ref.index` in the current newest-first typed environment. A record return is an ordinary reference with an extension-owned record sort.
2. `Program.let_ op args regions next`: record the op tag/static payload, declared argument sorts, ordered typed reference indices, region shapes, and result sort.
3. Recursively traverse **every** `Regions.cons body rest`, including unselected branch bodies, each with a fresh environment exactly matching `shape.inputs`.
4. Traverse `next` after binding the operation result at index zero.

The parent backend may pattern-match `@Program.let_` to expose implicit indices. Its sort/op codec must reject unsupported extensions exhaustively. A wire AST should carry argument/result sorts, every region's input/result sorts, all argument indices, nested ASTs, and the continuation/return. Generic byte encoding, an untrusted decoder, codec round-trip proofs, and foreign runtime correctness are outside this lane.

## Reproduction and trust

```sh
lake build Witgen.Core Witgen.CoreTests
lake env lean -DwarningAsError=true Witgen/CoreTests.lean
```

`artifacts/core-01-{red,green}.txt` through `core-04-{red,green}.txt` retain actual test-first receipts: scoped execution; embeddings/substitution/relational proof; macro expansion; optional control/records. RED failures are missing interfaces, not deliberately inserted false production proofs. `artifacts/core-final.txt` records the final command/output.

Key `#print axioms` results:

| Endpoint | Axioms |
|---|---|
| `Program.eval_subst`, `Program.eval_bind` | `propext`, `Quot.sound` |
| `Program.eval_mapHandler_related`, `Program.eval_lower_related` | `propext`, `Quot.sound` |
| `CertifiedLowering.comp_correct` | none |
| `CoreTests.lowered_correct`, `CoreTests.composed_lowering_correct` | `propext`, `Quot.sound` |
| `CoreTests.Optional.branch_true`, `branch_false` | none |
| `CoreTests.Optional.map_correct` | `propext` |
| `CoreTests.unreducedTemplate_rejected` | none |

No custom axioms, proof placeholders, `native_decide`, or unsafe proof shortcuts. Only the owned core/test targets are certified here; the parent owns arithmetic, native emission, and end-to-end buffer correspondence.

## Deliberate limits

Universe zero; explicit-input closed regions; one typed result per op (aggregate sorts supply multi-field results); no sort-index-changing translation; no recursion/effects/exceptions; no automatic range analysis; no verified codec/native backend. The control fixture specializes map to doubling rather than providing a general container library. Arbitrary extensions must uphold the data-only payload/serialization contract.
