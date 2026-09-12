# Executable scope

Build a runnable standalone demonstration, not a replacement of the production Clean API or an RSA signature-verifier submission.

1. Typed open-feature IR with explicit scoped regions, first-class native records, optional branch/map, and proven handler/substitution composition.
2. Scalar pipeline: finite-field operations -> mathematical Nat/bignum operations -> UInt64 operations under explicit representability/nonoverflow hypotheses. No claim to lower arbitrary unbounded bignums to one word.
3. Two circuit families: quadratic witnesses (square plus output); RSA-inspired modular multiplication (product, quotient, remainder, and their relation/range obligations). Include batched/conditional examples to exercise control.
4. Certified generator indexed by exact circuit and feature environment; different generators for one unchanged relation. Explicit witness-slot writes with a correspondence proof and negative controls.
5. Rust backend supporting native field operations via arkworks, integer operations via GMP-backed rug, and u64 operations. Emit the same source directly and after Lean-side lowering; compare generated code and executed cell buffers.
6. Prove the semantic transformations and circuit/writer properties in Lean without custom axioms/sorries/native_decide. Execute generated Rust and compare it with Lean on exhaustive small domains and representative large integers where supported. Record the native emitter/compiler/library trust boundary honestly.
7. Claude reviews code/proofs/emission, not just the prose design.

RSA inspiration: https://zk.golf/llms.txt and zksecurity/zk-golf-challenges revision fb9e89a5de99022a53089f0d11a18331c4c321a3, Solution/RSASSAPKCS1v15_SHA256_4096_65537/MulMod.lean lines 14-22 and 176-203. Core pattern: product = quotient * modulus + remainder, remainder < modulus, with all circuit-required intermediates exposed. Full RSA-4096 padding/exponentiation and production limb/carry arithmetization are outside the initial slice.

Toolchain available: Lean 4.32.2; rustc/cargo 1.85.1; system GMP 6.3.0. Rust crate versions must be checked for compatibility and locked.

Ownership while agents run: Core agent owns Witgen/Core.lean, Witgen/CoreTests.lean, docs/CoreAPI.md. Arithmetic agent owns Witgen/Arithmetic.lean, Witgen/ArithmeticTests.lean. Parent owns examples, circuit integration, backend, harness, packaging and review. Do not overwrite another lane's files.
