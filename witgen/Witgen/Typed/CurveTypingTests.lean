import Witgen.Typed.Curve

namespace Witgen.Typed.CurveTests
open Witgen
def first : CurveId := { secp256k1 with name := "user:first" }
def second : CurveId := { secp256k1 with name := "user:second" }
example : Ty.point first ≠ Ty.point second := by decide
example : Ty.list (.pair (.field first.scalar) (.point first)) ≠
    Ty.list (.pair (.field first.scalar) (.point second)) := by decide

example (Γ : List Ty) (p q : Var Γ (.point first)) : Step (CurveOp first) Γ .bool := curve.Eq p q
example (Γ : List Ty) (p : Var Γ (.point first)) : Step (CurveOp first) Γ (.point first) := curve.Inv p

/--
error: Application type mismatch: The argument
  q
has type
  Var Γ (Ty.point second)
but is expected to have type
  Var Γ (Ty.point first)
in the application
  curve.Add p q
-/
#guard_msgs in
example (Γ : List Ty) (p : Var Γ (.point first)) (q : Var Γ (.point second)) :
    Step (CurveOp first) Γ (.point first) := curve.Add p q

/--
error: Application type mismatch: The argument
  s
has type
  Var Γ (Ty.field first.base)
but is expected to have type
  Var Γ (Ty.field first.scalar)
in the application
  curve.Mul s
-/
#guard_msgs in
example (Γ : List Ty) (s : Var Γ (.field first.base)) (p : Var Γ (.point first)) :
    Step (CurveOp first) Γ (.point first) := curve.Mul s p

/--
error: Application type mismatch: The argument
  xy
has type
  Var Γ ((Ty.field first.scalar).pair (Ty.field first.scalar))
but is expected to have type
  Var Γ ((Ty.field first.base).pair (Ty.field first.base))
in the application
  curve.FromAffine first xy
-/
#guard_msgs in
example (Γ : List Ty) (xy : Var Γ (.pair (.field first.scalar) (.field first.scalar))) :
    Step (CurveOp first) Γ (.option (.point first)) := curve.FromAffine first xy

/--
error: Application type mismatch: The argument
  terms
has type
  Var Γ ((Ty.field first.base).pair (Ty.point first)).list
but is expected to have type
  Var Γ ((Ty.field first.scalar).pair (Ty.point first)).list
in the application
  curve.MSM terms
-/
#guard_msgs in
example (Γ : List Ty) (terms : Var Γ (.list (.pair (.field first.base) (.point first)))) :
    Step (CurveOp first) Γ (.point first) := curve.MSM terms

/--
error: Application type mismatch: The argument
  q
has type
  Var Γ (Ty.point second)
but is expected to have type
  Var Γ (Ty.point first)
in the application
  curve.Eq p q
-/
#guard_msgs in
example (Γ : List Ty) (p : Var Γ (.point first)) (q : Var Γ (.point second)) :
    Step (CurveOp first) Γ .bool := curve.Eq p q
end Witgen.Typed.CurveTests
