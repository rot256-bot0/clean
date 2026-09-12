import Witgen.Typed.SecpFeature

namespace Witgen.Typed.Secp.Tests
open Witgen

example [Fact (modulus secpBase).Prime] (p : Point) :
  secpModel.eval SecpOp.inv (.cons p .nil) .nil = -p := rfl

example (s : Var [Ty.field secpScalar, .point] (.field secpScalar))
    (p : Var [Ty.field secpScalar, .point] .point) :
    Step SecpOp [Ty.field secpScalar, .point] .point := secp.Scale s p

/--
error: Application type mismatch: The argument
  xy
has type
  Var [(Ty.field secpScalar).pair (Ty.field secpScalar)] ((Ty.field secpScalar).pair (Ty.field secpScalar))
but is expected to have type
  Var [(Ty.field secpScalar).pair (Ty.field secpScalar)] ((Ty.field secpBase).pair (Ty.field secpBase))
in the application
  curve.FromAffine xy
-/
#guard_msgs in
example (xy : Var [Ty.pair (.field secpScalar) (.field secpScalar)]
    (.pair (.field secpScalar) (.field secpScalar))) :
    Step SecpOp [Ty.pair (.field secpScalar) (.field secpScalar)] (.option .point) :=
  curve.FromAffine xy

end Witgen.Typed.Secp.Tests

open Witgen Witgen.Typed
/--
error: Application type mismatch: The argument
  b
has type
  Var [Ty.field secpBase, Ty.point] (Ty.field secpBase)
but is expected to have type
  Var [Ty.field secpBase, Ty.point] (Ty.field secpScalar)
in the application
  secp.Scale b
-/
#guard_msgs in
example (b : Var [Ty.field secpBase, .point] (.field secpBase))
    (p : Var [Ty.field secpBase, .point] .point) :
    Step SecpOp [Ty.field secpBase, .point] .point := secp.Scale b p
