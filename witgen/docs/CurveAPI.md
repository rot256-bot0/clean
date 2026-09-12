# Generic curve API — implementation seam

```lean
structure CurveId where
  name : String
  base : FieldId
  scalar : FieldId
  a1 a2 a3 a4 a6 : FieldValue base -- canonical coefficients
  deriving DecidableEq, Repr
-- User-owned descriptors are ordinary values, not entries in a closed curve enum.
abbrev secp256k1 : CurveId :=
  { name := "secp256k1", base := secpBase, scalar := secpScalar, a6 := ⟨7, by decide⟩ }
-- Library sorts, not CoreProgram changes:
Ty.point (c : CurveId)
Ty.list (element : Ty)
CurveOp (c : CurveId) : Signature Ty
```

`CurveOp c` constructors: `const literal : [] → point c`, `add : [point c, point c] → point c`,
`mul : [field c.scalar, point c] → point c`, `inv : [point c] → point c`,
`eq : [point c, point c] → bool`, `msm : [list (pair (field c.scalar) (point c))] → point c`,
`generator/identity : [] → point c`,
`toAffine : [point c] → option (pair (field c.base) (field c.base))`,
`fromAffine : [pair (field c.base) (field c.base)] → option (point c)`.
All have no regions. Distinct descriptor names remain distinct point types even with identical fields.

`curve.Add/Mul/Inv/Eq/ToAffine/MSM` infer `c` from point/term operands.
`curve.Generator c`, `curve.Identity c`, and `curve.FromAffine c xy` take the descriptor explicitly.
Eq requires only `Has (CurveOp c) F`, not Bool operations.
There is no primitive `x`, no `X` helper, and no `Scale/scale` compatibility alias.

## Mathematical semantics

`Curve.Math c` supplies a prime base field, a proof of nonzero discriminant, and a point on the descriptor’s fixed Mathlib Weierstrass equation as generator; it cannot substitute a different equation.
Its point carrier is the equation's actual `WeierstrassCurve.Affine.Point`, with Mathlib's additive commutative group; it is not a host callback or discrete-log representation.
`Curve.model` interprets `CurveOp c` using this carrier. Affine encoding/decoding has a proved correspondence law: decoding coordinates succeeds exactly for nonsingular points, and finite points roundtrip; infinity encodes as `none`.
`mul s P = s.val • P`, `eq P Q = decide (P = Q)`, and
`msm terms = (terms.map (fun (s,P) => s.val • P)).sum`.
Empty MSM is zero and singleton MSM agrees with Mul.
`Secp.math` instantiates the actual equation `(0,0,0,0,7)` over `ZMod (modulus secpBase)` with the actual generator and existing kernel-checked base/scalar prime certificates.

## JSON contract (native worker)

Field type JSON stays `{"field":1,"modulus":"<decimal>"}`.
Curve descriptor JSON is exactly
`{"id":"secp256k1","base":{"field":1,"modulus":"<base decimal>"},"scalar":{"field":2,"modulus":"<scalar decimal>"},"weierstrass":["0","0","0","0","7"]}`.
Point type JSON is `{"point":<descriptor>}`.
Pair/option remain `{"pair":[A,B]}` / `{"option":A}`; list is `{"list":A}`.
All curve op tags use `curve.`: `curve.const`, `curve.add`, `curve.mul`, `curve.inv`, `curve.eq`,
`curve.msm`, `curve.generator`, `curve.identity`, `curve.toAffine`, `curve.fromAffine`.
Their static metadata is exactly `{"curve":<descriptor>}`, with the additional `value` member for Const described below.
Native support currently accepts only the full, exact secp256k1 descriptor and matching argument/result types; unknown IDs or changed field/modulus metadata fail closed. Generic Lean export does not silently relabel user descriptors as secp256k1.
MSM takes one list of scalar/point pairs, never parallel arrays. Fixture JSON list input is `[["scalar", "SEC1 point"], ...]`; empty input is `[]`.
Optional library constructors `value.nil` and `value.cons` have empty static metadata, like the existing structural value operations.
`option.match` also has static `{}`. Its first argument is `option a`, followed by explicitly typed captured values; region 0 takes the captures and returns `result`, region 1 takes `a :: captures` and returns `result`. None executes only region 0; Some executes only region 1. `value.Match x captures onNone onSome` exposes this finite AST; the parent-owned named `match` frontend supplies explicit captures. `option.bind` remains available internally.

## Checked constants

`CurveId` includes five canonical base-field coefficients. `CurveId.equation` constructs the exact Mathlib Weierstrass curve from them. `Curve.Math c` fixes its point type to that equation and cannot choose an unrelated curve.
`CurveLiteral c` is `.infinity` or `.affine (x y : FieldValue c.base) (valid : c.equation.Nonsingular x.val y.val)`.
`CurveOp.const (literal : CurveLiteral c)` has no runtime arguments and returns `point c`; `curve.Const c literal` is the public helper.
`curve.const` static metadata is `{"curve":<descriptor>,"value":{"infinity":true}}` or `{"curve":<descriptor>,"value":{"x":"<canonical decimal>","y":"<canonical decimal>"}}`.
The proof is checked during Lean elaboration and erased at export. Native emission independently rejects unsupported descriptor/equation metadata, noncanonical coordinates, or an off-curve literal before compiling a direct point constant. There is no Option result and no invalid-to-infinity fallback. Generator and Identity remain convenient nullary operations.

## Programs and source fixtures

Existing field programs and inputs stay unchanged.
`secp_mixed_fields` changes to two scalar inputs `[s,t]` and returns `option base` (JSON null or decimal string).
The reusable `CurvePrograms.mixed {F} c` requires only `Has (CurveOp c) F`, `Has (FieldOp c.scalar) F`, `Has (FieldOp c.base) F`, and `Has ValueOp F`.
It computes scalar arithmetic, Mul/Add/Inv, then ToAffine and a surface Option match containing Fst/Snd and all base arithmetic. The Some branch returns `some (x²·y+x)` in the base field; None remains None. The frontend emits `option.match` with explicit captures and two closed regions.
The previous unused outer base input is removed. No default coordinate at infinity remains.
Existing `secp_to_affine`, `secp_from_affine`, `secp_affine_roundtrip`, and `secp_generator_affine_roundtrip` keep their signatures with descriptor-tagged points.
New exports: `curve_eq : [point secp256k1, point secp256k1] → bool`;
`curve_msm : [list (pair scalar (point secp256k1))] → point secp256k1`;
`curve_msm_constructed : [scalar, point secp256k1] → point secp256k1` (Pair/Nil/Cons singleton, then MSM);
`curve_const_generator : [] → point secp256k1` and `curve_const_identity : [] → point secp256k1`.
`CurvePrograms.curveEq/curveMSM` require only the curve capability; roundtrip and constructedMSM additionally require `ValueOp`.
`MainMethods.exportAll` writes actual AST exports and computes references by evaluating those ASTs, including identity, empty/singleton/multi-term MSM, and full-width canonical scalars. The independent harness must enumerate the new reference set, not retain the previous 408 assertion.

For independent reference-input enumeration, write `S(a)` for the canonical scalar and `P = [0,G,2G,-G,(n−1)G]`. Keep duplicate points in P:
- mixed: `(0,0),(1,1),(1,0),(2,3),(n−1,1),(2^200+7,2^129+9),(17,19)`;
- ToAffine and affine roundtrip: every entry of P;
- FromAffine: coordinates of G, coordinates of 2G, `(0,0)`, `(1,1)`;
- Eq: P × P, preserving duplicates and order;
- MSM: `[]`, `[(S(0),G)]`, `[(S(1),G)]`, `[(S(1),0)]`, `[(S(1),G),(S(1),−G)]`, `[(S(2),G),(S(3),2G)]`, `[(S(n−1),G)]`, `[(S(2^200+7),G),(S(2^129+9),−G),(S(17),0)]`;
- constructed MSM: `(S(0),G),(S(1),G),(S(n−1),G),(S(n−1),0),(S(2^200+7),2G)`;
- generator affine roundtrip and both Const programs: no inputs.

Audit endpoints: `Curve.const_spec`, `Curve.literal_point_spec`, `Curve.mul_spec`, `Curve.eq_spec`, `Curve.msm_spec`, `Curve.msm_nil`,
`Curve.msm_singleton`, `Curve.affine_roundtrip`, `Curve.fromAffine_toAffine`,
`Secp.concrete_mixed_correct`, `Secp.concrete_generator_roundtrip`,
`Secp.curveEq_correct`, `Secp.curveMSM_correct`, `Secp.constructedMSM_correct`,
`Secp.constantGenerator_correct`, `Secp.constantIdentity_correct`, `Secp.mixed_identity_none`.
Exact final input enumeration and checked commands will be reported with the implemented exports.
