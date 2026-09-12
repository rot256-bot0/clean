import Witgen.Typed.Curve

open Witgen Witgen.Typed
-- No BoolOp or ValueOp capability is present.
def curveEqualityOnly (c : CurveId) : Program (CurveOp c) [.point c, .point c] .bool :=
  .let_ .eq h![.zero, .succ .zero] .nil (.ret .zero)
example (c : CurveId) (M : Curve.Math c) (p q : M.Point) :
    (curveEqualityOnly c).eval (Curve.model M) h![p,q] = decide (p = q) := rfl
example (c : CurveId) (M : Curve.Math c) : Curve.msm M [] = 0 := Curve.msm_nil M
example (c : CurveId) (M : Curve.Math c) (s : FieldValue c.scalar) (p : M.Point) :
    Curve.msm M [(s,p)] = Curve.mul M s p := Curve.msm_singleton M s p
