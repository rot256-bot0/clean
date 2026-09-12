import Witgen.Typed.Examples
namespace Witgen.Typed.ExampleTests
open Witgen
example : (fieldProgram secpScalar).eval (fieldModel secpScalar)
    h![Residue.ofNat (modulus_pos secpScalar) 3, Residue.ofNat (modulus_pos secpScalar) 4] =
      Residue.ofNat (modulus_pos secpScalar) 41 := rfl
#guard (Methods.libraryJson typeJson NatMethods.codec (NatMethods.library secpScalar)).size == 3
end Witgen.Typed.ExampleTests
