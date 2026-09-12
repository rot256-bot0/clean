# Executed Scope

Development remains on the authorized `feat/clean-witgen-dsl` branch in
`rot256-bot0/clean`. Parent Clean's WitnessIR and toolchain remain unchanged.
No Codex, main/master edits, dependency-source changes or upstream pushes.

## Authoring and Generic Structures

- `witgen [...] do` supports named operation bindings, reference aliases and returns,
  elaborating into the unchanged finite typed Core AST. Undeclared ambient captures
  and unsupported statement forms fail explicitly.
- `StructDesc`/`StructOp` provide caller-owned schemas, unique field names, generic
  construction and typed named projection. Named construction checks schema order.
- `StructRepr` includes pack/unpack inverse laws. `ListOp` is separate; no concrete
  computational feature is mandatory in Core.
- `Witgen.Custom` gives a separate caller-owned type/feature family and a certified
  native-record→structural-field-list lowering, with actual Rust/GMP export/execution.

## Main Cryptographic Examples

- BN254 scalar Fr, represented by four native limbs and modeled as canonical residues
  modulo its exact scalar prime. Decimal strings preserve full-width input/output.
- Circuit-feature→Field/StructOp→Nat lowering is proved compositionally. Direct
  Arkworks and lowered GMP execute the same actual AST-derived full witness.
- Both ordinary and nested custom structures retain the internal square and public
  result, exact buffer slots and unchanged input bindings.
- The arithmetic proofs require a positive modulus, not a formal primality proof.
  No Lean algebraic Field instance or 254-bit security claim is made.
- Small fields remain bounded exhaustive regression fixtures, not the main example.

## Native Errors and Verification

- Shared `Error` enum and fixed `Result<T>` alias; structured domains/lengths/arity,
  standard `Display`/`Error`, and original parse/JSON/I/O sources.
- Providers and generated APIs propagate typed errors; only the CLI formats the
  diagnostic string and adds a stable error code.
- Full-width canonicality/reduction, typed errors, generic structure metadata and
  source/reference/native correspondence have executable tests. Fresh runners retain
  exact case/axiom inventories, command receipts and hashes.
- Foreign libraries, serializers, emitter and compiler are tested TCB, not kernel proofs.

## Caliper and Publication

- Existing compiler certificates survive the generic-structure migration. The public
  runtime walkthrough now uses parameterized word modular multiplication, with exact
  abstract cycles 99 and net/peak buffer-capacity growth 6/6.
- This is not a full-width BN254 Caliper backend, generic compiler-preservation theorem,
  or Rust/hardware timing claim. General multi-limb lowering remains future work.
- Code-first documentation is regenerated from exact Lean/Rust/Caliper source excerpts.
  Full tests and immutable independent reviews precede the coauthored commit/push.
  Publication updates are explicit snapshots with exact remote readback.

Required commit attribution:
`Co-authored-by: Mathias Hall-Andersen <mathias@hall-andersen.dk>`.
