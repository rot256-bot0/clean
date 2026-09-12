# Executed Scope

Work remains on the authorized `feat/clean-witgen-dsl` branch in `rot256-bot0/clean`.
No Codex, main/master edits, dependency-source changes or upstream pushes.
Parent Clean's WitnessIR remains unchanged.

## Typed Functionality and Structures

- Field identity is part of `.field id` and `FieldOp id`. Namespaced Add/Mul/Square
  infer it from operands; constants name the field. Base/scalar mixing is rejected.
- Generic `struct.Named/Get/Set` operates on caller-owned schemas. Set is functional;
  update, other-field, representation and original-value laws are checked.
- Named do authoring keeps its fail-closed ambient-parameter policy; no relaxation
  of the previous scoping fix is part of this work.

## Methods and Field Lowerings

- Optional typed method signatures/references and acyclic libraries contain actual
  finite Program bodies. Calls evaluate those bodies, not host callbacks.
- Field→Nat stores explicit arithmetic/reduction bodies and keeps calls.
- Field→U64 is a real four-limb implementation with carry/borrow, overflow-aware
  modular addition and bounded multiplication/squaring. Three generic arithmetic
  bodies are shared, with nine field wrappers and twelve emitted callers.
- U64 bodies contain word operations, layouts, calls and one bounded loop. Big-integer
  parsing/serialization and proof/reference calculations are outside the data path.

## secp256k1

- Distinct base/scalar fields have closed kernel-checked Lucas primality certificates.
- Real Mathlib curve model; point Add/Scale/Inv and typed coordinate operations.
- ToAffine returns None at infinity; FromAffine returns None off-curve.
- Native curve implementation uses Arkworks. Curve→field/U64 lowering is a separate
  possible implementation of this feature, not an implemented path here.
- Generator order/cofactor/module-action and constant-time claims are not made.

## Verification and Publication

The standard runner includes real native/Nat/U64 method and curve cases, exact
nonempty axiom inventories, call-linkage/definition-sharing checks and hashes.
Independent source/native review and a Claude review precede final publication.
The design quotes actual source/generated methods and has no backend-error essay.
Publication is an explicit snapshot update followed by exact remote readback.

Existing bounded and BN254 full-witness regressions are retained. No full new-library
Caliper or hardware timing theorem is claimed by the correctness results.

Required attribution:
`Co-authored-by: Mathias Hall-Andersen <mathias@hall-andersen.dk>`.
