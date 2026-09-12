import Witgen.Typed.SecpCurve
import Witgen.PrimeCertificates

namespace Witgen.Typed.CurveMathTests
open Witgen

def first : CurveId := { secp256k1 with name := "user:alpha" }
def second : CurveId := { secp256k1 with name := "user:beta" }

def firstMath : Curve.Math first where
  basePrime := ⟨PrimeCertificates.secpBase_prime⟩
  nonsingular := Secp.discriminant_ne_zero
  generator := Secp.generator

def secondMath : Curve.Math second where
  basePrime := ⟨PrimeCertificates.secpBase_prime⟩
  nonsingular := Secp.discriminant_ne_zero
  generator := Secp.generator

-- Both mathematical models compose, but their point operands remain distinct.
def both : Model (SigSum (CurveOp first) (CurveOp second)) (Curve.Val firstMath) :=
  (Curve.model firstMath).sum (Curve.model secondMath)

def compareEach : Program (SigSum (CurveOp first) (CurveOp second))
    [.point first, .point second] .bool :=
  .let_ (.inl .eq) h![.zero,.zero] .nil
    (.let_ (.inr .eq) h![.succ (.succ .zero),.succ (.succ .zero)] .nil (.ret .zero))

example (p : firstMath.Point) (q : secondMath.Point) : compareEach.eval both h![p,q] = true := by
  change decide (q = q) = true
  simp

open Lean Methods in
def userIdentityJson : Except String Json :=
  moduleJson typeJson Curve.codec .nil "user_curve_identity" []
    ((.let_ .identity .nil .nil (.ret .zero) : Program (CurveOp first) [] (.point first)).mapHandler Sum.inl)

#guard (typeJson (.point first)) != typeJson (.point second)
#guard (Curve.codec (CurveOp.identity (c := first))) != Curve.codec (CurveOp.identity (c := second))
#guard userIdentityJson.isOk

end Witgen.Typed.CurveMathTests
