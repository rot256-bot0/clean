import Witgen.Typed.NatMethods

namespace Witgen.Typed.FieldNatExtendedTests

def negative (f : FieldId) : Program (FieldOp f) [.field f] (.field f) :=
  witgen [x] do
    let y ← field.Neg x
    return y

def inverse (f : FieldId) : Program (FieldOp f) [.field f] (.field f) :=
  witgen [x] do
    let y ← field.Inv x
    return y

example (f : FieldId) (a : FieldValue f) :
    ((inverse f).mapHandler (NatMethods.handler f)).eval ((NatMethods.library f).model NatMethods.model)
      h![a.val] = (Residue.inv a).val :=
  ((NatMethods.lowering f).correct (inverse f) h![a] h![a.val] ⟨rfl,trivial⟩).symm

example (f : FieldId) (a : FieldValue f) :
    ((negative f).mapHandler (NatMethods.handler f)).eval ((NatMethods.library f).model NatMethods.model)
      h![a.val] = (Residue.neg a).val :=
  ((NatMethods.lowering f).correct (negative f) h![a] h![a.val] ⟨rfl,trivial⟩).symm
end Witgen.Typed.FieldNatExtendedTests
