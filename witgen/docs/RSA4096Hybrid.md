# RSA-4096 Hybrid Witness Generation

```sh
# From witgen/, with its pinned Lean 4.32.2 dependencies available:
python3 -B tools/run_rsa4096.py --output artifacts/rsa4096
```

The runner executes the finite typed Lean program on three public RSA-4096
fixtures, writes every auxiliary cell, compares the complete result with an
independent source-derived integer implementation, and checks its constraint
relation and interleaved allocation schedule. It writes `verification.json`
only after all gates pass, including the unchanged-source check. A failed run
removes the previous PASS receipt.

## Entry Points

- [`Program.lean`](../Witgen/Examples/RSA4096/Program.lean):
  `witnessProgram`, capability-polymorphic over bignum, field, bridge, vector,
  value and conditional features.
- [`Arithmetic.lean`](../Witgen/Examples/RSA4096/Arithmetic.lean):
  quotient/residue selection, field convolutions, interpolation-window products,
  range-bit generation, signed field carries, and final radix repacking.
- [`Compare.lean`](../Witgen/Examples/RSA4096/Compare.lean):
  the complete signature-less-than-modulus witness prefix.
- [`MainRSA.lean`](../MainRSA.lean): strict decimal-string CLI and actual AST export.

```sh
lake build Witgen.Examples.RSA4096.ProgramTests
lake env lean --run MainRSA.lean export rsa4096_hybrid.json
lake env lean --run MainRSA.lean run inputs.json witness.json
```

`inputs.json` contains three canonical decimal strings named `modulus`,
`signature`, and `digest`. The modulus has exactly 4096 bits; the signature fits
4096 bits and the digest fits 256 bits. The runner supplies these requests from
fixed-width big-endian public fixtures under `tests/data/rsa4096/`.
The adapter only packs bytes into integers: it does not compute a quotient,
RSA exponentiation, padding, limb, carry, or auxiliary cell.

The output is `{"witness": [...]}` with exactly 160,527 canonical BN254-scalar
field values encoded as decimal strings. These are the local witness cells;
the public-input prefix is not included. The source circuit's public order is
modulus bytes, digest bytes, then signature bytes.

## Hybrid Structure

`BigNumOp` uses arbitrary-precision `Nat`. Subtraction is truncated natural
subtraction; division returns both quotient and remainder, with the explicit
total convention `(0, x)` at divisor zero. The RSA input adapter excludes a zero
modulus. `FieldBridgeOp f` explicitly converts a natural number modulo `f`, or
extracts a field element's canonical natural representative.

The RSA program uses these operations compositionally, not through an opaque
RSA or modular-exponentiation primitive. `VectorOp` provides list storage,
finite tabulation/folds, and application of stored regions. Region bodies remain
`Program`/`Regions` syntax. The finite core and fail-closed authoring policy are
unchanged.

The circuit-specific path is:

1. Emit the complete signature comparison prefix.
2. Compute the first unsigned square, then fourteen signed squarings using
   24-bit limbs. Select both the quotient and the stored residue with the exact
   byte-centered offset, rather than assuming a half-radix offset.
3. Emit quotient/residue limbs, their low range bits, interpolation-window
   witnesses, low product coefficients and carry range bits in source order.
   Implicit high bits and other affine expressions are not extra witness cells.
4. Reconstruct the last square's implicit high-bit expressions from its
   allocated cells and repack those bits to 16-bit limbs.
5. Emit the fused final square–multiply relation, including PKCS#1 v1.5 encoding
   of the supplied digest and the final product/carry witnesses.

The generic field operations—not a bignum whole-circuit callback—compute the
convolutions, window products and signed carry recurrences.

## Pinned Target and Evidence Scope

The target is submission `aa9cb03a-4312-476d-8ed8-761f781f6a86` for
`rsa-pkcs1v15-sha256-4096-65537`, the winning entry when retrieved on 2026-09-13.[4][6]
The source archive SHA-256 is
`0c04418f927c53034bfa58702548d9da3b1dcaa69ef6ee76b4a05a4b8a72e7d0`.
Full source-file pins, table vectors and the compressed ordered allocation
manifest are retained in `tools/rsa4096/`.

The main runner's evidence is explicitly `SOURCE_REVIEWED_NOT_LEAN_BOUND`:
`reference.py` independently transcribes the pinned source's relation and
witness order; it is not a formal extraction from the original circuit.
Its checker consumes the actual Lean-generated cells, rather than replacing
them with its own generated values. The last-carry-bit negative control must
fail. Strict codecs also reject missing/extra cells and noncanonical outputs
before any field comparison.

The example runs through Lean's interpreter. It does not add Rust/GMP emission,
U64 lowering, or a hardware runtime bound for these new features. Generic bignum
and field-bridge laws, finite typing and the comparator-before-arithmetic layout
identity are kernel checked. The eight-declaration `Witgen/RsaAudit.lean` inventory
permits only `propext` and `Quot.sound` for the executable models/programs.
JSON parsing/printing and executable tests are a separate tested implementation
layer. There is no universal theorem that this full generator satisfies the
original RSA relation for every valid input, and passing fixtures do not imply
such a theorem.

The public test fixtures contain no private keys. The supplied digest is already
SHA-256; this is a witness generator for verification, not an RSA signer.

## Sources

[4] https://zk.golf/api/agent/v1/challenges/rsa-pkcs1v15-sha256-4096-65537/leaderboard
[6] https://zk.golf/api/submissions/aa9cb03a-4312-476d-8ed8-761f781f6a86/download
