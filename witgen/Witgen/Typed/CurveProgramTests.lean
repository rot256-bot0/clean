import Witgen.Typed.CurvePrograms
open Witgen Witgen.Typed
example (c : CurveId) : Program (CurveOp c) [.point c, .point c] .bool := CurvePrograms.curveEq c
example (c : CurveId) : Program (CurveOp c) [.list (.pair (.field c.scalar) (.point c))] (.point c) :=
  CurvePrograms.curveMSM c
example (c : CurveId) : Program (SigSum ValueOp (CurveOp c)) [.field c.scalar, .point c] (.point c) :=
  CurvePrograms.constructedMSM c

namespace Witgen.Typed.CurveProgramTests

theorem curveEq_correct (c : CurveId) (M : Curve.Math c) (p q : M.Point) :
    (CurvePrograms.curveEq c).eval (Curve.model M) h![p,q] = decide (p = q) := rfl

theorem curveMSM_correct (c : CurveId) (M : Curve.Math c)
    (terms : List (FieldValue c.scalar × M.Point)) :
    (CurvePrograms.curveMSM c).eval (Curve.model M) h![terms] =
      (letI := M.basePrime; (terms.map (fun (s,p) => s.val • p)).sum) := rfl

theorem constructedMSM_correct (c : CurveId) (M : Curve.Math c)
    (s : FieldValue c.scalar) (p : M.Point) :
    (CurvePrograms.constructedMSM c).eval
      ((ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64)
        (fun d => d.equation.Point)).sum (Curve.model M)) h![s,p] =
      Curve.mul M s p := Curve.msm_singleton M s p

theorem roundtrip_correct (c : CurveId) (M : Curve.Math c) (p : M.Point) :
    (CurvePrograms.roundtrip c).eval
      ((ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64)
        (fun d => d.equation.Point)).sum (Curve.model M)) h![p] =
      (Curve.toAffine M p).bind (Curve.fromAffine M) := by
  cases p <;> rfl

end Witgen.Typed.CurveProgramTests
