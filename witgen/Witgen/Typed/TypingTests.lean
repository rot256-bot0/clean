import Witgen.Typed.Field
open Witgen Witgen.Typed

/--
error: Application type mismatch: The argument
  b
has type
  Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpScalar)
but is expected to have type
  Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpBase)
in the application
  field.Mul a b
-/
#guard_msgs in
example (a : Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpBase))
    (b : Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpScalar)) :
    Step AnyFieldOp [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpBase) := field.Mul a b
