import Witgen.Typed.SecpFeature
import Witgen.Typed.CurvePrograms

namespace Witgen.Typed.Secp
open Witgen

abbrev AffineTy : Ty := .pair (.field secpBase) (.field secpBase)
abbrev AffineFeature := SigSum ValueOp (CurveOp secp256k1)

def affineModel [Fact (modulus secpBase).Prime] : Model AffineFeature Val :=
  (ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64) (fun d => d.equation.Point)).sum secpModel

def roundtripProgram : Program AffineFeature [.point secp256k1] (.option (.point secp256k1)) :=
  CurvePrograms.roundtrip secp256k1

def generatorRoundtrip : Program AffineFeature [] (.option (.point secp256k1)) :=
  .let_ (.inr .generator) .nil .nil roundtripProgram

def invalidPair : Program AffineFeature [AffineTy] (.option (.point secp256k1)) :=
  witgen [xy] do
    let result ← curve.FromAffine secp256k1 xy
    return result

def curveEq : Program (CurveOp secp256k1) [.point secp256k1, .point secp256k1] .bool :=
  CurvePrograms.curveEq secp256k1

def curveMSM : Program (CurveOp secp256k1)
    [.list (.pair (.field secpScalar) (.point secp256k1))] (.point secp256k1) :=
  CurvePrograms.curveMSM secp256k1

def constructedMSM : Program AffineFeature [.field secpScalar, .point secp256k1] (.point secp256k1) :=
  CurvePrograms.constructedMSM secp256k1

def constantGenerator : Program (CurveOp secp256k1) [] (.point secp256k1) :=
  witgen [] do
    let p ← curve.Const secp256k1 generatorLiteral
    return p

def constantIdentity : Program (CurveOp secp256k1) [] (.point secp256k1) :=
  witgen [] do
    let p ← curve.Const secp256k1 .infinity
    return p

theorem roundtripProgram_eval [Fact (modulus secpBase).Prime] (p : Point) :
    roundtripProgram.eval affineModel h![p] = (toAffine p).bind fromAffine := by
  cases p <;> rfl

theorem generatorRoundtrip_correct [Fact (modulus secpBase).Prime] :
    generatorRoundtrip.eval affineModel .nil = some generator := by
  change roundtripProgram.eval affineModel h![generator] = some generator
  rw [roundtripProgram_eval]
  exact generator_roundtrip

theorem invalidPair_rejects_zero [Fact (modulus secpBase).Prime] :
    invalidPair.eval affineModel h![(Residue.ofNat (modulus_pos secpBase) 0,
      Residue.ofNat (modulus_pos secpBase) 0)] = none := fromAffine_zero_zero

theorem curveEq_correct [Fact (modulus secpBase).Prime] (p q : Point) :
    curveEq.eval secpModel h![p,q] = decide (p = q) := rfl

theorem curveMSM_correct [Fact (modulus secpBase).Prime] (terms : List (FieldValue secpScalar × Point)) :
    curveMSM.eval secpModel h![terms] = (terms.map (fun (s,p) => s.val • p)).sum := rfl

theorem constructedMSM_correct [Fact (modulus secpBase).Prime] (s : FieldValue secpScalar) (p : Point) :
    constructedMSM.eval affineModel h![s,p] = mul s p := Curve.msm_singleton math s p

theorem constantGenerator_correct [Fact (modulus secpBase).Prime] :
    constantGenerator.eval secpModel .nil = generator := rfl

theorem constantIdentity_correct [Fact (modulus secpBase).Prime] :
    constantIdentity.eval secpModel .nil = 0 := rfl

open Lean Methods in
def affineCodec : OpCodec AffineFeature := fun op => match op with
  | .inl op => ValueOp.codec op
  | .inr op => Curve.codec op

open Lean Methods in
def generatorRoundtripJson : Except String Json :=
  moduleJson typeJson affineCodec .nil "secp_generator_affine_roundtrip" []
    (generatorRoundtrip.mapHandler Sum.inl)

open Lean Methods in
def fromAffineJson : Except String Json :=
  moduleJson typeJson affineCodec .nil "secp_from_affine" ["coordinates"]
    (invalidPair.mapHandler Sum.inl)

open Lean Methods in
def curveEqJson : Except String Json :=
  moduleJson typeJson Curve.codec .nil "curve_eq" ["p","q"] (curveEq.mapHandler Sum.inl)

open Lean Methods in
def curveMSMJson : Except String Json :=
  moduleJson typeJson Curve.codec .nil "curve_msm" ["terms"] (curveMSM.mapHandler Sum.inl)

open Lean Methods in
def constructedMSMJson : Except String Json :=
  moduleJson typeJson affineCodec .nil "curve_msm_constructed" ["s","p"]
    (constructedMSM.mapHandler Sum.inl)

open Lean Methods in
def constantGeneratorJson : Except String Json :=
  moduleJson typeJson Curve.codec .nil "curve_const_generator" [] (constantGenerator.mapHandler Sum.inl)

open Lean Methods in
def constantIdentityJson : Except String Json :=
  moduleJson typeJson Curve.codec .nil "curve_const_identity" [] (constantIdentity.mapHandler Sum.inl)

end Witgen.Typed.Secp
