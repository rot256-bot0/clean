import Witgen.Typed.NatMethods
import Witgen.Typed.FieldTests
namespace Witgen.Typed.NatMethodTests
open Witgen

example (f : FieldId) (a : FieldValue f) :
    ((NatMethods.lowering f).run (Tests.square (f := f))).eval
      ((NatMethods.library f).model NatMethods.model) (.cons a.val .nil) = a.val ^ 2 % modulus f := by
  have h := (NatMethods.lowering f).correct (Tests.square (f := f))
    (.cons a .nil) (.cons a.val .nil) ⟨rfl, trivial⟩
  exact h.symm

end Witgen.Typed.NatMethodTests
