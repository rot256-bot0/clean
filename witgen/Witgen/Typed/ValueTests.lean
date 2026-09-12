import Witgen.Typed.Values
namespace Witgen.Typed.ValueTests
open Witgen
abbrev model := ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64) (fun _ => PUnit)
example : model.eval (ValueOp.pair Ty.nat Ty.bool) h![7,true] .nil = (7, true) := rfl
example : model.eval (ValueOp.nil Ty.nat) .nil .nil = ([] : List Nat) := rfl
example : model.eval (ValueOp.cons Ty.nat) h![7, [8,9]] .nil = [7,8,9] := rfl
example : model.eval (ValueOp.case Ty.nat Ty.nat [Ty.nat]) h![none, 17]
    h![(fun xs => Var.get .zero xs), (fun xs => Var.get .zero xs + Var.get (.succ .zero) xs)] = 17 := rfl
example : model.eval (ValueOp.case Ty.nat Ty.nat [Ty.nat]) h![some 7, 17]
    h![(fun xs => Var.get .zero xs), (fun xs => Var.get .zero xs + Var.get (.succ .zero) xs)] = 24 := rfl
end Witgen.Typed.ValueTests
