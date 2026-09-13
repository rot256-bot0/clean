# Executed Scope

Authorized branch: `feat/clean-witgen-dsl` in `rot256-bot0/clean`.
No Codex, main/master edits, dependency-source changes or upstream pushes.
The finite Core and parent Clean integration remain unchanged.

## Implemented

- Generic structures with functional Set and preservation laws.
- Field-indexed Const/Add/Sub/Mul/Square/Neg/Inv/Sqrt with model semantics and named helpers.
- Kernel-checked primality for BN254 scalar and secp256k1 base/scalar moduli.
- Generic curve descriptors/equations and `CurveOp c`, real Mathlib point models,
  Mul/Eq/MSM, statically checked point constants and explicit affine optionality.
- Capability-polymorphic programs; removed primitive X and renamed Scale to Mul.
- Named if/match elaboration to finite typed regions, explicit captures,
  payload shadowing and fail-closed ambient/capability/exhaustiveness controls.
- Typed earlier-only method libraries and emit-once shared U64 bodies/callers.
- Total Nat field lowering; partial U64 lowering with checked acceptance,
  no fallback and no hidden whole-field arithmetic.
- Real Arkworks/GMP native execution, strict curve metadata and recursive codecs,
  exact independent case coverage and Cargo-reported executable receipts.

## Verification

Required: full Python/Rust regressions, typed/extended/structure/core/crypto/Caliper
axiom inventories, cold local U64 closure, source/native/oracle comparisons,
independent frozen-source review, and live publication/readback.

Methods cover 449 cases; the extended runner covers 720. Existing full-witness,
custom-type and bounded regressions remain in the standard runner.

## Publication

Code-first artifact includes actual field/curve specifications, Has-polymorphic
programs, checked constants, if/match behavior, structures and shared methods.
No final checks/boundaries section or error-API discussion. Caliper is described as
U64-only, with no field/curve implementation inside it. The artifact is updated
once at the end, at the existing URL, after verification.
