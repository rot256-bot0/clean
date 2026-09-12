import Witgen.Typed.Curve
open Witgen Witgen.Typed
example (c : CurveId) (M : Curve.Math c) :
    (Curve.model M).eval (CurveOp.const CurveLiteral.infinity) .nil .nil = 0 := rfl
example : secp256k1.a6.val = 7 := rfl

/--
error: Tactic `decide` proved that the proposition
  secp256k1.equation.Nonsingular ↑↑⟨0, ⋯⟩ ↑↑⟨0, ⋯⟩
is false
-/
#guard_msgs in
def invalidLiteral : CurveLiteral secp256k1 :=
  .affine ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide)

-- A descriptor's equation cannot be replaced by a model field.
/-- error: `equation` is not a field of structure `Curve.Math` -/
#guard_msgs in
def differentEquation (M : Curve.Math secp256k1) : Curve.Math secp256k1 :=
  { M with equation := ⟨0,0,0,0,8⟩ }
