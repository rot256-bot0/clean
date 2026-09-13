import Witgen.Typed.Field
open Witgen Witgen.Typed

theorem sqrtCrossFieldRejected
    (_a : Var [Ty.field secpBase] (Ty.field secpBase)) : True := by
  fail_if_success
    let _ : Step AnyFieldOp [Ty.field secpBase] (Ty.option (Ty.field secpScalar)) := field.Sqrt _a
  trivial

theorem subCrossFieldRejected
    (_a : Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpBase))
    (_b : Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpScalar)) : True := by
  fail_if_success
    let _ := field.Sub (F := AnyFieldOp) _a _b
  trivial

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
