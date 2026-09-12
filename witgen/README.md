# Clean WitGen

Feature-based witness-generation development on a Clean fork branch. The core is Lean4.32.2 + Std, with native Rust and a pinned Caliper backend dependency. This package is isolated from the parent Clean4.33.1 build; it does not yet replace `Clean/Circuit/WitnessIR.lean`.

## Run

Prerequisites: Lean/Elan, Python 3, Rust 1.85+, rustfmt, and system GMP 6.3 development libraries. Dependencies are locked; the Rust crate uses arkworks 0.6 and integer-only rug 1.30.

```sh
lake update
lake exe cache get
python3 tools/run_demo.py
python3 -m unittest discover -s tests -v
cargo test --locked --manifest-path backend/Cargo.toml --test providers
```

```sh
# Export ACTUAL typed Lean programs and their declared cell layouts.
lake exe witgen export artifacts/export
python3 tools/build_native.py artifacts/export
cargo build --locked --manifest-path backend/Cargo.toml --bin witgen-native

# Reference interpreter / explicit writer.
lake exe witgen demo
# [3,4,9,13]
```

The native executable accepts one JSON request per stdin line:

```json
{"program":"quadratic_field","inputs":["3","4"]}
{"program":"quadratic_nat","inputs":["3","4"]}
{"program":"quadratic_word","inputs":["3","4"]}
{"program":"modmul_nat","inputs":["15","15","16"]}
{"program":"batch_fold_word","inputs":[false,["3","4","16"],"4"]}
```

All quadratic modes produce cells `[3,4,9,13]`. Modmul produces `[15,15,16,225,14,1]`. The disabled batch writes every reserved cell: `[0,3,4,16,4,0,0,0,0,0,0]`.

## Inspect the Code Difference

```text
backend/src/generated/quadratic_field.rs    arkworks field operations
backend/src/generated/quadratic_nat.rs      GMP-backed Integer operations
backend/src/generated/quadratic_word.rs     u64 operations after Lean lowering
backend/src/generated/batch_field.rs        native map/branch over records
backend/src/generated/batch_fold_word.rs    map→fold and Field→Nat→Word
```

Each file contains real Rust record definitions and an explicit `populate` function. The writer reads input cells, calls the record-returning generator once, validates the output shape/encoding, and writes the exact reserved slots. A local generator `let` is not automatically a circuit witness.

## The Actual Lean Interfaces

```lean
-- Core has no built-in arithmetic, record, list or control feature.
abbrev Signature (S : Type) :=
  List S → List (RegionShape S) → S → Type

Program F Γ t
Template F G -- each source op becomes a typed TARGET SUBPROGRAM
CertifiedLowering sourceModel targetModel valueRelation

-- Programs, not host closures:
quadraticField : Program FieldSig [.scalar, .scalar] .quad
quadraticNat   := quadraticField.lower fieldToNat
quadraticWord  := quadraticNat.mapHandler natToWord
```

See [Core.lean](Witgen/Core.lean), [Demo.lean](Witgen/Demo.lean), and [Pipeline.lean](Witgen/Pipeline.lean). The native serializer traverses those ASTs; it does not evaluate them to invent source code.

```lean
-- Generator-independent circuit relation and soundness.
Circuit Input Witness Output

-- Actual program + exact model + fixed input/output boundary.
FormalWitgen circuit model Γ resultSort
CompleteOver circuit model encodeInput decodeWitness
```

The fixed ABI matters: arbitrary host adapters cannot silently be chosen as part of a feature-only completeness claim. `CircuitTests.Generic.no_hidden_arithmetic` rejects increment implemented by an empty-feature identity program with the fixed identity boundary.

## Proof Endpoints

- `Program.eval_lower_related`: operation-to-subprogram refinement, including typed regions.
- `CertifiedLowering.comp_correct`: composition preserves the representation relation.
- `Demo.fieldToNat_law`, `fieldToWord_law`: local arithmetic implementations realize their specs.
- `Demo.lower_commutes`, `natToWord_fieldImage_correct`: the actual two-step field pipeline.
- `Demo.mapToFold_correct`: generic map-to-fold preservation, retaining the body.
- `Integration.quadraticField_buffer`, `quadraticWord_buffer`: complete quadratic witness buffers.
- `Integration.modMulWord_buffer`: full modular-multiplication buffer, not only remainder equality.
- `Batch.certified_buffer`, `foldWord_generate_eq_source`, `disabled_populates_all`: complete fixed-shape batch results, including the disabled branch.

Source, reference outputs, native results, hashes and axiom reports are retained in `artifacts/` by the runner. The source range gates and writer are independently checked, and native output is also compared with separately written arithmetic checks.

## Caliper Integration and Runtime Proofs

```sh
# Build, directly recheck proofs/tests, audit axioms and export actual Stmt/run results.
python3 tools/run_caliper.py

# Export only, without a large native Mathlib build:
lake build Witgen.Backends.CaliperExamples
lake env lean --run MainCaliper.lean export artifacts/caliper
```

The full `tools/run_demo.py` entry point also runs the Caliper checks. Plain
`lake build` / `import Witgen` intentionally retains the core-only dependency
boundary; import `Witgen.Backends.CaliperExamples` for this optional backend.

- [Runtime walkthrough](../doc/witgen-dsl-design.md#7-caliper-integration-and-runtime-proofs): checked compilation, full writer, `Exec` versus `Triple`, and a runnable proof example.
- [Compiler API](docs/CaliperBackendAPI.md): static layouts, freshness checks and explicit branch-shape rejection.
- [Cost/circuit API](docs/CaliperCostAPI.md): complete buffer correspondence, cost formulas, frames and precise input domains.
- [Checked runtime example](Witgen/Backends/CaliperRuntimeGuide.lean): quadratic `.cycles` total-correctness bound and exact cost, both `90 / 4 / 4` for time/net/peak buffer growth.
- [Generated assembly and observations](examples/caliper): real checked compiler outputs plus witness population, exported by `Caliper.Stmt.renderString` and `Caliper.run`.

Costs include allocation **and** every population push. `.cycles` is an abstract
Caliper table, not measured hardware cycles or a Rust runtime bound. Inputs start
in registers; input parsing, host conversion and Lean code generation are outside
the bound. Memory counts reserved buffer words, not register liveness.

Whole-program proofs currently cover quadratic, bounded modular multiplication,
and a **two-row** fixed gated word program (both branches). The first two additionally
connect the actual buffer to the circuit constraints under their canonical/bounded
input hypotheses. The gated certificate is not for the separate three-row batch
circuit. There is no generic whole-compiler preservation theorem or general dynamic
list ABI; a new source program still needs a preservation/cost proof.

Fresh evidence is written to `artifacts/caliper/`: assembly, `runtime.json`, exact
axiom audit, direct-check logs, source hashes and `verification.json`. Failure removes
the previous verification receipt. Checked-in `examples/caliper/` is an explicit
snapshot, not a live symlink.

## Examples and Scope

1. **Quadratic, field17:** square and output are both witness cells. Three feature/model implementations share one unchanged circuit.
2. **Modular multiplication, field257:** operands below a positive modulus at most16; product, quotient and remainder are constrained, with explicit ranges and no-wrap proofs.
3. **Fixed three-row gated batch:** first-class record list, explicit captures, map/branch, map→fold lowering, all11 cells populated. Wrong result lengths and stale disabled cells are rejected.
4. **Unbounded Nat arithmetic:** the GMP backend also executes the actual modular-mul program on4096-bit values, returning a native big-integer record. This raw arithmetic demonstration does not claim to be a field257 circuit execution.

The modular quotient/remainder pattern is inspired by [zk.golf's RSA challenge](https://zk.golf/llms.txt), specifically `MulMod.lean` at challenge revision `fb9e89a5de99022a53089f0d11a18331c4c321a3`. No challenge library is imported. Full RSA padding, signature verification and production limb/carry arithmetization are outside this slice.

## Verified Versus Trusted

**Kernel-checked:** typed scope, local realization/lowering laws, composed program semantics, circuit soundness, complete logical witnesses, fixed cell layouts, pure vector population and negative controls. Core endpoints use only standard `propext` and `Quot.sound`. The separate Caliper compiler/writer/`Exec`/`Triple`/runtime-guide audit additionally permits standard `Classical.choice`; neither audit permits custom axioms or native-decision proofs.

**Tested TCB:** Lean JSON serialization, Python JSON checking/Rust printing, rustfmt/rustc, arkworks, GMP/rug, native execution and the comparison harness. No claim that foreign code, printing or machine execution is kernel-verified.

JSON fidelity is spot-checked and differentially tested, not proved by a general round-trip theorem. Same-sorted argument order is part of this tested boundary. The axiom gate separately requires a report for every named declaration in `Witgen/Audit.lean`; missing reports cannot pass vacuously.

**Deliberate limits:** pure semantics (not a general IO/effect/cost model); explicit-input closed regions; one result sort per op with aggregate values; a caller-provided sort universe; representations may change through model relations but sort indices remain fixed. Extension payloads/codecs must be data-only. The demo has fixed record sorts rather than a general deriving handler or arbitrary named-subroutine linker. No automatic lowering search or general range inference.

**Nat→u64 is conditional.** It is proved for the image of the field lowering and for explicitly bounded modular multiplication. It is not an implementation of arbitrary unbounded natural arithmetic in one machine word.

Native division/remainder deliberately reject zero divisors. Lean's pure arithmetic models totalize them; native/model equivalence is claimed only on the declared nonzero-divisor domains. For example, raw modular multiplication with modulus zero returns an error, not a witness.
