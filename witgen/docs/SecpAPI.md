# secp256k1 instance

```lean
namespace Witgen.Typed.Secp
abbrev curve : WeierstrassCurve.Affine Base := secp256k1.equation
abbrev Point := curve.Point

def math [Fact (modulus secpBase).Prime] : Curve.Math secp256k1 where
  basePrime := inferInstance
  nonsingular := discriminant_ne_zero
  generator := generator
end Witgen.Typed.Secp
```

The descriptor fixes coefficients `(0,0,0,0,7)` over `ZMod (modulus secpBase)`.
`Secp.basePrime` and `Secp.scalarPrime` supply the closed Lucas certificates for the exact base and scalar moduli. `Secp.secpModel = Curve.model Secp.math`; its carrier is Mathlib’s `WeierstrassCurve.Affine.Point`, not a discrete-log representation.

## Arithmetic and affine values

```lean
-- c is inferred from point/term operands.
curve.Mul scalar point
curve.Add point other
curve.Inv point
curve.Eq point other        -- Bool; only the curve capability is required
curve.MSM terms             -- List (scalar × point)
curve.ToAffine point        -- Option (base × base)
curve.FromAffine c xy       -- Option (point c)
curve.Generator c
curve.Identity c
```

Mul is the canonical natural action `scalar.val • point`; Mathlib’s point group uses `nsmulBinRec`.
MSM is the sum of those same actions over a list of pairs. Empty MSM is identity, and singleton MSM equals Mul. There is no assumption that arbitrary scalar representatives act modulo the group order.
Eq is exactly `decide (P = Q)`.

```lean
def roundtrip {F : Signature Ty} (c : CurveId)
    [Has (CurveOp c) F] [Has ValueOp F] :
    Program F [.point c] (.option (.point c)) :=
  witgen [p] do
    let xy ← curve.ToAffine p
    let out ← match xy with
      | none => value.None (.point c)
      | some coordinates => curve.FromAffine c coordinates
    return out
```

Infinity has no affine coordinates, so the None branch preserves it as absent. The Some branch receives the coordinate pair and checks the exact curve equation. `Secp.fromAffine_isSome_iff` proves acceptance exactly when `y² = x³ + 7`; `Secp.affine_roundtrip` proves every finite point returns unchanged.
The optional `ValueOp` feature supplies the match operation; the frontend stores two closed region ASTs and passes named captures explicitly. It is not a Lean callback in the serialized program.

## Checked literals

```lean
def generatorLiteral : CurveLiteral secp256k1 :=
  .affine (Residue.ofNat (modulus_pos secpBase) Secp.generatorX)
    (Residue.ofNat (modulus_pos secpBase) Secp.generatorY)
    Secp.generator_nonsingular

-- Both are point-valued, with no runtime inputs or Option result.
curve.Const secp256k1 generatorLiteral
curve.Const secp256k1 .infinity
```

The literal’s proof refers to the equation embedded in its descriptor. Native emission accepts only the exact secp descriptor, coefficients, and valid canonical coordinates. The JSON representation and generic signatures are specified in [CurveAPI.md](CurveAPI.md).

## Mixed fields

`CurvePrograms.mixed` is capability-polymorphic. It requires `CurveOp c`, `FieldOp c.scalar`, `FieldOp c.base`, and `ValueOp`, not a concrete feature bundle. The secp export specializes this source to `Secp.MixedFeature`.

For scalar inputs `s,t`, let `k = ((s² mod n)·t + s) mod n` and `Q = kG − G`.
The program returns None when Q is infinity; for `ToAffine Q = some (x,y)`, it returns `some (x²·y+x)` in the base field. Fst/Snd and all base arithmetic are inside the Some branch.

`MainTyped.lean` exports `eq`, `msm`, `msm-constructed`, `const`, `const-identity`, `affine`, and `from-affine`; its default is the mixed program. `MainMethods.lean` emits those actual ASTs together with source-evaluated reference values.
