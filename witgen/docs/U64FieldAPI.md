# Field → U64: Shared Method API

Namespace `Witgen.U64`. Logical sorts come from `Witgen.Typed.Types`; field identity
stays in the sort while its representation becomes four `UInt64` limbs.

## Arithmetic and Representation

- `Word4` has little-endian limbs `l0..l3`.
- `decode : Word4 → Nat` and `encode : Nat → Word4` are reference/ABI adapters;
  encode truncates modulo `2^256`. They are not invoked by field Add/Mul/Square.
- `Canonical p a := a.decode < p`.
- `addCarry`, `subBorrow` return a word vector and the final carry/borrow.
- `Add p a b` subtracts the modulus when the sum carried beyond four limbs or
  the subtraction did not borrow. This covers moduli near `2^256`.
- `Mul p a b` uses a structurally recursive 256-bit Horner loop.
- `Square p a` uses `Mul p a a`.
- `bitAt a i` is total: it returns `false` for every `i ≥ 256`, matching native
  `typed::bit_at` without wrapping the high-limb shift. `bitAt_out_of_range` proves
  this boundary; the original `bitAt_correct` statement for `i < 256` is unchanged.

`decode_encode`, `addCarry_correct`, `subBorrow_correct`, `Add_correct`,
`mulLoop_correct`, `Mul_correct` and `Square_correct` are kernel-checked. Modulus
and operands are actual Word4 values; assumptions are positive modulus and
canonical operands. No primality assumption is needed for these residue-ring laws.
The raw decoded result—not another modular normalization—equals the specification.

## Actual Stored Method Bodies

`U64Op` includes only word literals, word4 layout, carry/borrow word/flag operations,
Boolean selection, bit lookup, a bounded repeat, and raw field/layout wrappers.
There is no whole-field arithmetic intrinsic in this signature.

`addBody`, `mulBody`, `squareBody` are finite typed `Program` values. Their evaluation
and arithmetic correctness are proved separately. Mul's AST contains one `repeat 256`
with a closed region `[index,acc,p,a,b] → acc` and two earlier Add call sites.
The body evaluates both alternatives before selecting; it is a reference method,
not a constant-time or performance-optimized implementation.

`allLibrary` contains exactly three generic bodies plus nine field wrappers:
BN254 Fr, secp BASE and secp SCALAR each receive Add/Mul/Square wrappers. The generic
bodies use an explicit word4 modulus and are shared across all field identities.
`fieldAddRef`, `fieldMulRef`, `fieldSquareRef` are intrinsically typed links.

## Certified Lowering and Export

`lower : PartialHandler AnyFieldOp (WithCalls U64Op allSigs)` maps Add/Mul/Square
to retained method calls and constants to encoded literals. Neg/Inv are declined.
`compile p accepted` requires a success proof; there is no fallback program.
`certified` and `caller_correct` prove preservation for accepted programs. `Rep` says raw decoding of
a target field value equals the source canonical representative and recursively
covers pair/option/list values. This field-only model uses PUnit for unused curve-indexed point
sort; it is not a lowering of elliptic-curve operations.

`bundleJson` emits one `methods` array (12 definitions) and nine single-operation
callers. The parent adds three composed callers using the identical registry. Native
emission therefore has one copy of the three arithmetic bodies, nine thin wrappers
and twelve callers, not a copy of the bodies per caller.

Codec: v2 `u64-shared-library`; word literals/limbs are decimal strings, field types
retain their ID and exact modulus. `method.call` carries name and a newest-first
index in the appropriate earlier-method scope. `u64.repeat` retains a descending
native loop. Public native U64 admission uses usize only for bounded internal loop
indices and rejects arbitrary external Nat interfaces. WordField pack/unpack are raw.

## Reproduce

```sh
lake build Witgen.U64.Tests
lake env lean --run MainU64.lean export artifacts/u64
python3 tools/run_methods.py
python3 -B Witgen/U64/check.py
```

The cold checker rebuilds the entire local import closure without the existing
package olean cache, retaining only pinned dependency caches. Its field specification
now imports Mathlib for total inversion and prime certificates. It records the
dependency manifests, requires the independent 25-declaration axiom inventory, removes
stale verification receipts, checks the one-loop/shared-method shape and compares
raw output limbs with Python integers. Source tests cover 601 pairs/14 moduli,
1,803 algorithm and 1,803 body comparisons, and 279 field-caller executions
(264 distinct program/input tuples). Four cases have full 512-bit products.

Native codecs/emission/compiler are tested TCB, not kernel-proved. The U64 method
library has iteration-count proofs, not a complete Caliper or hardware cost theorem.
