import Witgen.Typed.Secp

namespace Witgen.secp256k1
abbrev Base : Typed.FieldId := Typed.secpBase
abbrev Scalar : Typed.FieldId := Typed.secpScalar
abbrev Curve : Typed.CurveId := Typed.secp256k1
end Witgen.secp256k1

namespace Witgen.Typed.Public
open Witgen

/-- The public examples quantify over only their required capabilities. -/
abbrev mixed := @CurvePrograms.mixed
abbrev roundtrip := @CurvePrograms.roundtrip
abbrev curveEq := @CurvePrograms.curveEq
abbrev curveMSM := @CurvePrograms.curveMSM
abbrev constructedMSM := @CurvePrograms.constructedMSM

theorem mixed_eq : mixed (F := Secp.MixedFeature) secp256k1 = Secp.mixed := rfl

theorem mixed_correct (s t : FieldValue secpScalar) :
    (mixed (F := Secp.MixedFeature) secp256k1).eval Secp.mixedModel h![s,t] = Secp.mixedSpec s t :=
  Secp.concrete_mixed_correct s t

abbrev mixedJson := Secp.mixedJson
end Witgen.Typed.Public
