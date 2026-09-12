import Witgen.Typed.Field

namespace Witgen.Typed.FieldExtendedTests

def negInv {F : Signature Ty} (f : FieldId) [Has (FieldOp f) F] :
    Program F [.field f] (.field f) :=
  witgen [x] do
    let negative ← field.Neg x
    let inverse ← field.Inv negative
    return inverse

example (f : FieldId) (a : FieldValue f) :
    (negInv (F := FieldOp f) f).eval (fieldModel f) h![a] = Residue.inv (Residue.neg a) := rfl

#check FieldOp.neg
#check FieldOp.inv
#check field.Neg
#check field.Inv
end Witgen.Typed.FieldExtendedTests
