import Witgen.Typed.SecpExamples

namespace Witgen.Typed.CurveIntegrationTests
open Witgen

theorem field_neg (f : FieldId) (a : FieldValue f) :
    (Secp.fieldModel f).eval .neg h![a] .nil = Residue.neg a := rfl

theorem field_inv (f : FieldId) (a : FieldValue f) :
    (Secp.fieldModel f).eval .inv h![a] .nil = Residue.inv a := rfl

theorem field_inv_zero (f : FieldId) :
    (Secp.fieldModel f).eval .inv h![Residue.ofNat (modulus_pos f) 0] .nil =
      Residue.ofNat (modulus_pos f) 0 := Residue.inv_zero _

theorem mixed_correct [Fact (modulus secpBase).Prime] (s t : FieldValue secpScalar) :
    (CurvePrograms.mixed (F := Secp.MixedFeature) secp256k1).eval Secp.mixedModel h![s,t] =
      Secp.mixedSpec s t := Secp.mixed_correct s t

theorem roundtrip_eval [Fact (modulus secpBase).Prime] (p : Secp.Point) :
    (CurvePrograms.roundtrip (F := SigSum ValueOp (CurveOp secp256k1)) secp256k1).eval
      ((ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64)
        (fun d => d.equation.Point)).sum Secp.secpModel) h![p] =
      (Secp.toAffine p).bind Secp.fromAffine := by
  cases p <;> rfl

theorem generator_roundtrip [Fact (modulus secpBase).Prime] :
    (Program.let_ (Sum.inr CurveOp.generator) .nil .nil
      (CurvePrograms.roundtrip (F := SigSum ValueOp (CurveOp secp256k1)) secp256k1)).eval
      ((ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64)
        (fun d => d.equation.Point)).sum Secp.secpModel) .nil = some Secp.generator := by
  simp only [Program.eval, HList.map, Regions.eval]
  exact (roundtrip_eval Secp.generator).trans Secp.generator_roundtrip

#guard Secp.mixedJson.isOk

section
local instance : Fact (modulus secpBase).Prime := ⟨PrimeCertificates.secpBase_prime⟩

#guard (Secp.mixed.eval Secp.mixedModel h![Residue.ofNat (modulus_pos secpScalar) 1,
  Residue.ofNat (modulus_pos secpScalar) 1]).map Fin.val ==
    some 15049581136193944005155656881674271607086196878768533802525739169400035159716
#guard Secp.mixed.eval Secp.mixedModel h![Residue.ofNat (modulus_pos secpScalar) 1,
  Residue.ofNat (modulus_pos secpScalar) 0] == none

end
end Witgen.Typed.CurveIntegrationTests
