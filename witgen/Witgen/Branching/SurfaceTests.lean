import Witgen.Typed.Values
import Witgen.Branching.Basic

namespace Witgen.Branching.SurfaceTests
open Typed

abbrev Feature := SigSum ValueOp (BranchOp Ty.bool)
def model : Model Feature FieldVal :=
  Model.sum (ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64) (fun _ => PUnit))
    (BranchOp.model FieldVal id)

def optionalIdentity : Program Feature [.option .nat] (.option .nat) :=
  witgen [input] do
    let out ← match input with
      | none => value.None .nat
      | some item => value.Some item
    return out

def selectOptional : Program Feature [.bool, .nat] (.option .nat) :=
  witgen [condition,x] do
    let out ← if condition then value.Some x else value.None .nat
    return out

example : optionalIdentity.eval model h![none] = none := by decide
example : optionalIdentity.eval model h![some 7] = some 7 := by decide
example : selectOptional.eval model h![true,7] = some 7 := by decide
example : selectOptional.eval model h![false,7] = none := by decide

def shadowPayload : Program Feature [.option .nat, .nat] (.option .nat) :=
  witgen [input,item] do
    let out ← match input with
      | some item => value.Some item
      | none => value.Some item
    return out

def aliasCapture : Program Feature [.option .nat, .nat] (.pair (.option .nat) .nat) :=
  witgen [input,fallback] do
    let saved := fallback
    let out ← match input with
      | none => value.Some saved
      | some item => value.Some item
    let pair ← value.Pair out fallback
    return pair

def nestedControl : Program Feature [.option .nat, .bool, .nat] (.option .nat) :=
  witgen [input,condition,fallback] do
    let out ← match input with
      | none => value.Some fallback
      | some item =>
        let selected ← if condition then value.Some item else value.Some fallback
        return selected
    return out

example : shadowPayload.eval model h![some 7,9] = some 7 := by decide
example : shadowPayload.eval model h![none,9] = some 9 := by decide
example : aliasCapture.eval model h![none,9] = (some 9,9) := by decide
example : aliasCapture.eval model h![some 7,9] = (some 7,9) := by decide
example : nestedControl.eval model h![some 7,true,9] = some 7 := by decide
example : nestedControl.eval model h![some 7,false,9] = some 9 := by decide
example : nestedControl.eval model h![none,true,9] = some 9 := by decide

end Witgen.Branching.SurfaceTests
