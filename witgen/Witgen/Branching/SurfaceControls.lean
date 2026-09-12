import Witgen.Branching.SurfaceTests

namespace Witgen.Branching.SurfaceControls
open Typed SurfaceTests

/-- error: implicit witgen capture 'secret'; declare it as a region input and pass it explicitly -/
#guard_msgs in
def foreignCapture (secret : Var (S := Ty) [.option .nat, .nat] .nat) :
    Program Feature [.option .nat, .nat] (.option .nat) :=
  witgen [input,_other] do
    let out ← match input with
      | none => value.Some secret
      | some item => value.Some item
    return out

/-- error: witgen effects support operation calls, if/else, and exhaustive Option match -/
#guard_msgs in
def incomplete : Program Feature [.option .nat] (.option .nat) :=
  witgen [input] do
    let out ← match input with
      | some item => value.Some item
    return out

/--
error: failed to synthesize instance of type class
  Has (BranchOp Ty.bool) ValueOp

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def missingFeature : Program ValueOp [.bool, .nat] (.option .nat) :=
  witgen [flag,item] do
    let out ← if flag then value.Some item else value.None .nat
    return out

end Witgen.Branching.SurfaceControls
