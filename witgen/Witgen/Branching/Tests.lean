import Witgen.Branching.Basic

namespace Witgen.Branching.Tests

inductive Kind where | flag | number

abbrev Val : Kind → Type
  | .flag => Bool
  | .number => Nat

abbrev Feature : Signature Kind := BranchOp .flag

def model : Model Feature Val := BranchOp.model Val id

def choose : Program Feature [.flag, .number, .number] .number :=
  witgen [condition,x,y] do
    let out ← control.If condition h![x,y]
      (witgen [a,_b] do
        return a)
      (witgen [_a,b] do
        return b)
    return out

example : choose.eval model h![true,7,9] = 7 := by decide
example : choose.eval model h![false,7,9] = 9 := by decide
example : choose.eval model h![true,9,7] = 9 := by decide
example : choose.eval model h![false,9,7] = 7 := by decide

-- The selection law does not invoke the other region.
example (xs : HList Val captures) (yes no : HList Val captures → Val result) :
    model.eval (.branch captures result) (.cons true xs)
      (.cons yes (.cons no .nil)) = yes xs := rfl
example (xs : HList Val captures) (yes no : HList Val captures → Val result) :
    model.eval (.branch captures result) (.cons false xs)
      (.cons yes (.cons no .nil)) = no xs := rfl

end Witgen.Branching.Tests
