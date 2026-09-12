import Witgen.U64.Lowering

namespace Witgen.U64.PartialTests
open Typed

def rejectedInv (f : FieldId) : Program AnyFieldOp [.field f] (.field f) :=
  witgen [x] do
    let y ← field.Inv x
    return y

def rejectedNeg (f : FieldId) : Program AnyFieldOp [.field f] (.field f) :=
  witgen [x] do
    let y ← field.Neg x
    return y

example (f : FieldId) : (rejectedInv f).mapHandler? lower = none := rfl
example (f : FieldId) : (rejectedNeg f).mapHandler? lower = none := rfl
#check certified.correct
#check caller_correct
end Witgen.U64.PartialTests
