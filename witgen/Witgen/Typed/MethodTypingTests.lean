import Witgen.Typed.MethodTests
set_option pp.mvars false

open Witgen Witgen.Methods Witgen.Typed Witgen.Typed.MethodTests

/--
error: Type mismatch
  Ref.zero
has type
  Ref (?_ :: ?_) ?_
but is expected to have type
  Ref [] twiceSig
-/
#guard_msgs in
example : Ref [] twiceSig := .zero

/--
error: Tactic `decide` proved that the proposition
  ¬twiceSig.name ∈ List.map MethodSig.name [twiceSig]
is false
-/
#guard_msgs in
example : Library Prim [twiceSig, twiceSig] :=
  .cons lib twiceSig (by decide) (.ret .zero)

/--
error: Application type mismatch: The argument
  Var.zero
has type
  Var (?_ :: ?_) ?_
but is expected to have type
  Var [Ty.bool] Ty.nat
in the application
  HList.cons Var.zero
-/
#guard_msgs in
example : Program (WithCalls Prim [twiceSig]) [.bool] .nat :=
  .let_ (.inr (.call .zero)) (.cons .zero .nil) .nil (.ret .zero)
