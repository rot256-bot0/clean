# Native method emitter seam

Parent owns `backend/src/typed.rs`, Cargo/error/lib changes, native runtime tests, and full runner/publication. A delegated emitter may own only `tools/emit_methods.py` and its Python tests.

## Input

Actual v2 JSON exports are in `artifacts/methods/{nat,u64,mixed,affine,from-affine}.json`.
Top-level: `version:2, name, inputs:[{name,type}], output, body, methods:[{name,args,result,body}]`.
Methods are oldest-first. Method call `static.index` is into the **newest-first prior scope**: a method sees only earlier definitions, caller sees all. Check index and name agree, exact args/result, no duplicate/forward/missing links. Emit each definition once; do not inline into callers. IR refs are newest-first normal Program refs.

Types: field `{field:0|1|2,modulus:exactDecimalString}`, `nat`, `bool`, `u64`, `word4`, point `{point:"secp256k1"}`, pair `{pair:[A,B]}`, option `{option:A}`. All field tags survive validation, even if physically represented alike. Known IDs: 0 BN254 Fr, 1 secp base, 2 secp scalar (exact moduli in Typed.Types and runtime `FIELD_MODULI`).

## Rust runtime (`witgen_native::typed`)

```rust
pub type Word4 = [u64; 4];
pub struct WordField<const ID: u8>(pub Word4); // Clone, Copy, Debug
pub struct NatField<const ID: u8>(pub rug::Integer); // Clone, Debug
pub type SecpBase = ark_secp256k1::Fq;
pub type SecpScalar = ark_secp256k1::Fr;
pub type SecpPoint = ark_secp256k1::Projective;
```

Fields in `native` mode map IDs 0→`witgen_native::Bn254Scalar`, 1→`typed::SecpBase`, 2→`typed::SecpScalar`. `nat` mode uses `typed::NatField<ID>`, with pack/unpack raw `.0`/constructor (NO hidden modular reduction). `u64` mode uses `typed::WordField<ID>`, with toWord/fromWord raw `.0`/constructor. Generic `word4` is `[u64;4]`.

Primitive helpers:

- `typed::adc(a:u64,b:u64,c:bool)->(u64,bool)`, `sbb(...)` analogous; word/flag projections `.0`/`.1`.
- `typed::bit_at(a:Word4,index:usize)->bool` (false if >=256).
- `typed::secp_base_from_nat(&Integer)->witgen_native::Result<SecpBase>`; `secp_scalar_from_nat` analogous; `*_from_str(&str)`.
- `typed::secp_base_to_nat(SecpBase)->Integer`, `secp_scalar_to_nat` analogous.
- `typed::secp_base_add/mul/square`, scalar variants, pure values.
- `typed::bn254_square(Bn254Scalar)->Bn254Scalar`; existing bn254_add/mul/from_nat/from_str/to_nat remain at crate root.
- `typed::point_add(P,Q)`, `point_scale(s:SecpScalar,P)`, `point_inv(P)`, `point_generator()`, `point_identity()`, `point_x(P)->SecpBase` with X(identity)=0.
- `typed::to_affine(P)->Option<(SecpBase,SecpBase)>`, `from_affine((x,y))->Option<SecpPoint>`; None=infinity on output, off-curve on input.

JSON helpers (all parsing returns `witgen_native::Result<T>`):

- `typed::parse_nat(&serde_json::Value)->Result<Integer>` decimal string/nonnegative.
- `typed::parse_u64(&Value)->Result<u64>` decimal string with bounds.
- `typed::parse_word4(&Value)->Result<Word4>` exactly four little-endian decimal word strings.
- `typed::parse_word_field::<ID>(&Value)->Result<WordField<ID>>` canonical decimal representative (not a raw limb array).
- `typed::parse_nat_field::<ID>(&Value)->Result<NatField<ID>>` canonical decimal representative.
- `typed::parse_point(&Value)->Result<SecpPoint>` SEC1 hex string, identity "00".
- `typed::word_field_decimal::<ID>(WordField<ID>)->String`; `word4_json(Word4)->Value` (4 word strings); `point_hex(P)->String`.
- `typed::field_modulus(ID:u8)->Result<Integer>` for input validation / static literal support. No use inside U64 method arithmetic.

Use existing enum errors for wrong arity/type/length and `?` where conversions can fail. Native method signatures may uniformly return `witgen_native::Result<T>`; U64 bodies then just return Ok.

## Control / admission

`u64.repeat` has arguments `[p,a,b,acc]`, one region `[natIndex,acc,p,a,b] -> word4`, and literal count; emit one descending `for i in (0..count).rev()` loop, never unroll256 iterations. `nat` in U64 mode is a bounded public `usize` index ONLY; reject external nat params/results in this mode rather than claim arbitrary Nat ABI. No whole-field GMP/BigInt/native field operations inside U64 method bodies. Parsing/decimal serialization may use Integer outside those bodies.

Support only the mode's registered ops: native field+curve/value, Nat arithmetic+raw field pack/unpack+calls, or exact U64Op tags+calls. Reject point sorts outside native mode: field-only Nat/U64 models use PUnit for that unused sort and do not certify EC lowering. The compiler does not use model evaluation to invent source.

## Recursive option JSON policy

Pairs encode as two-element arrays. `None` always encodes as JSON `null`.
For `Option<A>`, `Some(x)` encodes as the ordinary encoding of `x` **unless `A`
is itself an Option**. In that case it encodes as the single-key object
`{"some": encode(x)}`. The rule applies recursively, in all admitted modes:

| `Option<Option<bool>>` value | JSON |
|---|---|
| `None` | `null` |
| `Some(None)` | `{"some":null}` |
| `Some(Some(false))` | `{"some":false}` |
| `Some(Some(true))` | `{"some":true}` |

Nested-option decoders require exactly the lowercase `some` key on non-null
objects, reject missing/unknown/additional keys, and validate the contained value
recursively. Untagged non-null nested-option inputs are rejected with
`invalid_input_type`; there is no lossy legacy fallback or comparator normalization.

`Option<Point>` remains `null` or the SEC1 string. `Option<Pair<A,B>>` remains
`null` or `[encode(a),encode(b)]`, even when the pair contains nested options;
only those nested fields acquire tags. Thus the existing affine boundary remains
compatible: infinity/off-curve returns `null`, valid affine/point values keep their
ordinary array/string representation. This is a tested JSON/Rust boundary policy,
not a kernel proof of serialization or native execution.
