# Executed Scope and Continuation

This package is developed on `feat/clean-witgen-dsl` in the authorized
`rot256-bot0/clean` fork. Parent Clean's current WitnessIR and Lean toolchain remain
unchanged; no production circuit API replacement or RSA signature-verifier
submission is claimed.

## Feature DSL and Native Execution

- Typed open-feature IR with explicit scoped regions and optional record/list/control
  vocabulary. Feature-to-subprogram lowering and composition have semantic proofs.
- Field → Nat → UInt64 lowering under explicit representation/no-overflow domains;
  arbitrary unbounded big integers are not represented in one machine word.
- Generator-independent quadratic, bounded modular-multiplication and fixed three-row
  gated circuit relations, full satisfying witnesses, and fixed ABI/cell layouts.
- Actual AST-driven Rust emission with arkworks, GMP/rug and UInt64 implementations,
  exhaustive small-domain comparisons and raw 4096-bit integer arithmetic examples.
- Foreign serialization/emission/compilers/libraries are tested TCB, not kernel proofs.

RSA inspiration: `zksecurity/zk-golf-challenges` revision
`fb9e89a5de99022a53089f0d11a18331c4c321a3`,
`Solution/RSASSAPKCS1v15_SHA256_4096_65537/MulMod.lean`.
Full RSA padding/exponentiation and production limb/carry circuits remain outside scope.

## Caliper Continuation

1. Recover and directly recheck the actual WordSig → Caliper compiler: fresh registers,
   static map/fold unrolling, branch joins and explicit incompatible-shape rejection.
2. Verify generic reserve-then-push writer and complete producer/writer execution,
   frame, well-formedness, time/net/peak and actual-buffer circuit correspondence.
3. Export actual assembly and reference-interpreter observations; require nonempty
   exact axiom coverage, standard foundations only and fresh source-bound receipts.
4. Include Caliper verification in the full native/demo runner. Keep `import Witgen`
   core-only; Caliper remains an optional analysis import, never Rust's engine.
5. Publish a code-first integration/runtime-proof walkthrough backed by
   `CaliperRuntimeGuide.lean`, distinguishing exact `Exec` from bounded `Triple`.
6. Independently review the compiler/proofs and final harness/documentation; run all
   package tests, regenerate examples, then commit with the required coauthor and
   push only the fork branch. Explicitly update/read back the existing publication.

Universal whole-program Caliper certificates cover quadratic, bounded ModMul and
**two-row** gated word semantics, not an arbitrary-compiler theorem or the separate
three-row batch circuit. Circuit-domain assumptions, register-vs-buffer footprint,
input ABI exclusions and abstract cost model are stated in the runtime walkthrough.
Runtime-sized containers, generic compiler preservation, general bignum lowering and
production Clean integration are future work, not completion claims for this slice.

Toolchain is pinned by `lean-toolchain`, `lake-manifest.json` and Cargo.lock.
No Codex, master edits, dependency-source changes, custom axioms, `sorry`,
`native_decide` or heartbeat increases. Author attribution:
`Co-authored-by: Mathias Hall-Andersen <mathias@hall-andersen.dk>`.
