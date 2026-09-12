# Branching API

Parent owns `Witgen/Branching/**`, `MainBranching.lean`, branch runner/fixture tests and the artifact section. This is an optional generic feature over arbitrary library sorts, not a Core constructor or a Bool-operations feature.

```lean
inductive BranchOp {S : Type} (bool : S) : Signature S where
  | branch (captures : List S) (result : S) :
      BranchOp bool (bool :: captures)
        [⟨captures, result⟩, ⟨captures, result⟩] result
```

`control.If cond captures yes no` is a smart constructor. `captures` is an `HList (Var Γ) capturedSorts`; `yes` and `no` are closed `Program F capturedSorts result` bodies. They receive precisely the declared captures. Both branches have the same result type. Only the selected branch is evaluated. The model decodes the Bool-sort value and selects one of its region functions.

```lean
let out ← control.If condition h![x,y]
  (witgen [x,y] do
    let product ← field.Mul x y
    return product)
  (witgen [x,y] do
    let sum ← field.Add x y
    return sum)
```

## Native v2 seam

Tag: `control.if`. Static metadata: exactly `{}`.
Input types: `[bool] ++ captures`; two regions with `arg_types = captures` and the same result type as the operation. No extra region captures are allowed. Emission is a Rust `if` expression whose bodies are emitted inside the corresponding arm, not eagerly computed arguments.

Parent will export `branch_field` with inputs `[bool, field bn254, field bn254]`, result `field bn254`, true→multiply, false→add; the existing field metadata format applies. MainBranching computes references from actual Lean AST evaluation. This native specimen needs no changes to the Caliper backend.
