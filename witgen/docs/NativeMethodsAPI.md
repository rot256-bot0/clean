# Native method emitter seam

```python
source = emit_module(exported_module, "native")  # also "nat" / "u64"
```

The v2 module has `version:2, name, inputs:[{name,type}], output, body,
methods:[{name,args,result,body}]`. Methods are oldest-first; a call's
`static.index` selects from the **newest-first prior scope**. The emitter checks
name/index agreement, exact signatures, and duplicate/forward/missing links,
then emits one function per method and preserves calls. Program refs are
newest-first. Names are escaped comment receipts, not Rust identifiers.

## Types and curve identity

Field types are `{field:0|1|2,modulus:exactDecimalString}`. IDs are 0 BN254 Fr,
1 secp256k1 base, and 2 secp256k1 scalar. A point type carries its entire curve
descriptor:

```json
{"point":{"id":"secp256k1","base":{"field":1,"modulus":"115792089237316195423570985008687907853269984665640564039457584007908834671663"},"scalar":{"field":2,"modulus":"115792089237316195423570985008687907852837564279074904382605163141518161494337"},"weierstrass":["0","0","0","0","7"]}}
```

The native backend admits only this exact descriptor. It validates keys, curve
ID, field IDs, canonical decimal moduli and the five exact Weierstrass
coefficients in every point type and primitive
static descriptor, including nested signatures and method calls. Another curve
name with identical fields is not an alias. See [CurveAPI.md](CurveAPI.md).

Other types are `nat`, `bool`, `u64`, `word4`, `{pair:[A,B]}`, `{option:A}`,
and `{list:A}`. Recursive metadata is retained; physically similar field
representations do not make their logical types interchangeable.

```rust
pub type Word4 = [u64; 4];
pub struct WordField<const ID: u8>(pub Word4);
pub struct NatField<const ID: u8>(pub rug::Integer);
pub type SecpBase = ark_secp256k1::Fq;
pub type SecpScalar = ark_secp256k1::Fr;
pub type SecpPoint = ark_secp256k1::Projective;
```

Native fields map to `witgen_native::Bn254Scalar`, `typed::SecpBase`, and
`typed::SecpScalar`. Nat and U64 fields map to `typed::NatField<ID>` and
`typed::WordField<ID>`. Pack/unpack and toWord/fromWord are raw constructors
and projections, without hidden modular reduction. Pairs, options, and lists
map recursively to Rust tuples, `Option<T>`, and `Vec<T>`.

## Curve primitives

Every curve tag except Const has static metadata exactly `{"curve": descriptor}` and no
regions. `P` below is the descriptor's point type, `S` its scalar field and `B`
its base field. Runtime helpers live in `witgen_native::typed`.

| IR tag | Signature | Native helper |
|---|---|---|
| `curve.add` | `[P,P] → P` | `point_add` |
| `curve.mul` | `[S,P] → P` | `point_mul` |
| `curve.eq` | `[P,P] → bool` | `point_eq` |
| `curve.msm` | `[List<(S,P)>] → P` | `point_msm` |
| `curve.inv` | `[P] → P` | `point_inv` |
| `curve.generator` | `[] → P` | `point_generator` |
| `curve.identity` | `[] → P` | `point_identity` |
| `curve.const` | `[] → P` | `point_const` / `point_identity` |
| `curve.toAffine` | `[P] → Option<(B,B)>` | `to_affine` |
| `curve.fromAffine` | `[(B,B)] → Option<P>` | `from_affine` |

`point_mul(scalar, point)` uses Arkworks scalar multiplication. `point_eq(a,b)`
returns Arkworks' semantic projective equality directly, not encoded-byte or
coordinate-tuple equality. It needs the curve operation capability, not a
Boolean-operations feature.

`point_msm(Vec<(SecpScalar,SecpPoint)>) -> Result<SecpPoint>` splits already-typed
pairs, batch-normalizes their points and calls checked Arkworks
`VariableBaseMSM::msm`. It accepts no independent parallel arrays. Empty input
returns identity; singleton input agrees with Mul. The complete JSON list is
decoded before invoking a method or primitive, including zero-scalar and unused
terms. Malformed pairs, noncanonical scalars and invalid SEC1 points return
structured errors rather than partially evaluating the MSM.

`curve.const` uses exactly `{"curve":descriptor,"value":{"infinity":true}}`
or `{"curve":descriptor,"value":{"x":"decimal","y":"decimal"}}`.
The emitter verifies the descriptor, canonical coordinates, and secp256k1
equation before emitting any Rust. Infinity emits `point_identity()`; a valid
affine literal emits `point_const(x:SecpBase,y:SecpBase) -> SecpPoint`, a direct
Arkworks constructor. The literal has no runtime arguments, Option result,
validity branch, or invalid-to-infinity fallback. Dynamic affine inputs continue
to use checked `from_affine`.

There are no `curve.x`, `secp.x`, `curve.scale`, or `secp.scale` primitives,
or `point_x` / `point_scale` runtime exports. Coordinate access is ToAffine
followed by pair projections inside an Option branch. Identity remains `None`.

## Field and word helpers

- `typed::adc(a:u64,b:u64,c:bool)->(u64,bool)`, `sbb(...)` analogous.
- `typed::bit_at(a:Word4,index:usize)->bool`, false for indices at least 256.
- `typed::secp_base_from_nat(&Integer)->Result<SecpBase>`, scalar variant;
  `*_from_str`, `*_to_nat`, and pure `*_add/mul/square/neg/inv` variants.
- `typed::bn254_square/neg/inv`; root `witgen_native::bn254_add/mul/from_nat/from_str/to_nat`.
- Native `field.neg` / `field.inv` are unary same-field operations with exactly
  `{field,modulus}` metadata. Neg is Arkworks field negation; Inv is Arkworks
  inversion with `0 → 0`.
- Nat-only lowered `nat.field.neg` / `nat.field.inv` take `[Field(id)] → Field(id)`,
  exactly `{field:id,modulus:exactDecimalString}`, and no regions. They emit
  `typed::nat_field_neg/inv::<ID>(NatField<ID>) -> Result<NatField<ID>>`.
  For raw nonnegative `a`, Neg is `(p - (a % p)) % p`; Inv is the canonical
  modular inverse, with every multiple of `p` mapping to zero. The registered
  moduli are prime. Internal `a ≥ p` is allowed by these arithmetic primitives;
  pack/unpack remain raw and external field input parsing remains strict.
  Source and lowered Neg/Inv are rejected in U64 mode, never silently replaced.

`u64.repeat` receives `[p,a,b,acc]`, one closed region
`[natIndex,acc,p,a,b] → word4`, and a static count. Emission is one descending
`for i in (0..count).rev()` loop. U64 admits Nat only as a bounded internal
`usize` index: external Nat is rejected even inside list/pair/option types.
U64 arithmetic uses word helpers, not whole-field GMP or native field calls.
Points are admitted only in native mode.

## Closed branches and structural values

All these tags use exactly empty static metadata:

- `value.pair`, `value.fst`, `value.snd`, `option.some`, `option.none`.
- `value.nil : [] → List<A>`; `value.cons : [A,List<A>] → List<A>` preserves order.
- `option.bind : [Option<A>] → Option<B>` has one closed `[A] → Option<B>` region.
- `control.if : [bool] ++ captures → R` has two closed `captures → R` regions,
  ordered true then false.
- `option.match : [Option<A>] ++ captures → R` has two closed regions, ordered
  none (`captures → R`) then some (`[A] ++ captures → R`).

`control.if` and `option.match` emit Rust `if` and `match` expressions with each
region body inside its arm. Only the selected region executes. Both regions
are statically validated, with exact signatures and no access to undeclared
parent refs. A Bool condition requires only the Bool sort. See
[BranchAPI.md](BranchAPI.md).

## JSON boundary

Each generated module exposes `run(...) -> witgen_native::Result<T>` and
`run_json(&[serde_json::Value]) -> witgen_native::Result<Value>`. The U64 shared
bundle emits one registry and oldest-first `program_N` / `program_N_json`
functions, plus `run_json(program_index, inputs)`.

- Nat/U64/field inputs are nonnegative decimal strings; field inputs must be
  canonical. `word4` is exactly four little-endian decimal word strings.
- Points are SEC1 hex strings: compressed or uncompressed finite points, or
  `"00"` for identity. Output uses compressed SEC1 or `"00"`.
- Pairs are exactly two-element arrays. Lists are ordered arrays, recursively
  encoded with no truncation or element coercion. MSM input is one array such
  as `[["1","02…"],["0","00"]]`.
- `None` is JSON `null`. `Some(x)` uses the child's ordinary encoding unless
  its immediate child type is itself Option, in which case it uses exactly
  `{"some":encode(x)}`. This keeps `None` and `Some(None)` distinct.

| `Option<Option<bool>>` | JSON |
|---|---|
| `None` | `null` |
| `Some(None)` | `{"some":null}` |
| `Some(Some(false))` | `{"some":false}` |
| `Some(Some(true))` | `{"some":true}` |

Nested-option objects require exactly the lowercase `some` key and recursively
valid payloads. Lists and pairs are never null, so `Option<List<A>>` and
`Option<Pair<A,B>>` stay untagged arrays for Some; tags appear only at immediate
Option-of-Option boundaries. The policy is unchanged inside lists.

Parsing helpers return existing structured `witgen_native::Error` variants:
`parse_nat`, `parse_u64`, `parse_word4`, `parse_nat_field::<ID>`,
`parse_word_field::<ID>`, and `parse_point`. Serialization uses
`word_field_decimal::<ID>`, `word4_json`, `point_hex`, or recursive generated
encoders. Decimal codecs and `field_modulus` remain outside U64 arithmetic.

## Execution checks

```sh
python3 -B tests/test_method_emitter.py GenericCurveEmitterTests BranchEmitterTests FieldNegInvEmitterTests -v
python3 -B -m unittest discover -s tests -p test_method_emitter.py -v
cargo test --offline --locked --test typed
```

Tests exercise actual emitted Rust, independent integer/affine group arithmetic,
strict metadata and input rejection, projectively equivalent points, recursive
roundtrips, and unselected-branch non-evaluation. This JSON/Rust/foreign-arithmetic
boundary is tested TCB; Lean's semantic proofs are separate.
