import Witgen.Typed.NatMethods

namespace Witgen.Typed
open Witgen

/-- Reusable source fixture for Field→Nat and Field→U64. -/
def fieldProgram (f : FieldId) : Program (FieldOp f) [.field f, .field f] (.field f) :=
  witgen [a,b] do
    let aa ← field.Square a
    let product ← field.Mul aa b
    let five ← field.Const f 5
    let out ← field.Add product five
    return out

def fieldProgramNat (f : FieldId) := (NatMethods.lowering f).run (fieldProgram f)

theorem fieldProgramNat_correct (f : FieldId) (a b : FieldValue f) :
    (fieldProgramNat f).eval ((NatMethods.library f).model NatMethods.model) h![a.val,b.val] =
      ((fieldProgram f).eval (fieldModel f) h![a,b]).val := by
  exact ((NatMethods.lowering f).correct (fieldProgram f) h![a,b] h![a.val,b.val]
    ⟨rfl,rfl,trivial⟩).symm

open Lean Methods in
def fieldProgramNatJson (f : FieldId) : Except String Json :=
  moduleJson typeJson NatMethods.codec (NatMethods.library f)
    ("field_" ++ toString f.val ++ "_nat_methods") ["a", "b"] (fieldProgramNat f)

end Witgen.Typed
