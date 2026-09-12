import Witgen.Typed.SecpFeature
import Witgen.Typed.Values

namespace Witgen.Typed.Secp
open Witgen

abbrev AffineTy : Ty := .pair (.field secpBase) (.field secpBase)
abbrev AffineFeature := SigSum ValueOp SecpOp

def affineModel [Fact (modulus secpBase).Prime] : Model AffineFeature Val :=
  (ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64) Point).sum secpModel

def roundtripProgram : Program AffineFeature [.point] (.option .point) :=
  witgen [p] do
    let xy ← curve.ToAffine p
    let q ← value.Bind xy (witgen [coords] do
      let out ← curve.FromAffine coords
      return out)
    return q

def generatorRoundtrip : Program AffineFeature [] (.option .point) :=
  .let_ (.inr .generator) .nil .nil roundtripProgram

def invalidPair : Program AffineFeature [AffineTy] (.option .point) :=
  witgen [xy] do
    let result ← curve.FromAffine xy
    return result

theorem roundtripProgram_eval [Fact (modulus secpBase).Prime] (p : Point) :
    roundtripProgram.eval affineModel h![p] = (toAffine p).bind fromAffine := rfl

theorem generatorRoundtrip_correct [Fact (modulus secpBase).Prime] :
    generatorRoundtrip.eval affineModel .nil = some generator := generator_roundtrip

theorem invalidPair_rejects_zero [Fact (modulus secpBase).Prime] :
    invalidPair.eval affineModel h![(Residue.ofNat (modulus_pos secpBase) 0,
      Residue.ofNat (modulus_pos secpBase) 0)] = none := fromAffine_zero_zero

open Lean Methods in
def affineCodec : OpCodec AffineFeature := fun op => match op with
  | .inl op => ValueOp.codec op
  | .inr op => codec (.inr op)

open Lean Methods in
def generatorRoundtripJson : Except String Json :=
  moduleJson typeJson affineCodec .nil "secp_generator_affine_roundtrip" []
    (generatorRoundtrip.mapHandler Sum.inl)

open Lean Methods in
def fromAffineJson : Except String Json :=
  moduleJson typeJson affineCodec .nil "secp_from_affine" ["coordinates"]
    (invalidPair.mapHandler Sum.inl)

end Witgen.Typed.Secp
