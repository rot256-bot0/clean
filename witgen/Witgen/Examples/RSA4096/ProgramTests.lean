import Witgen.Examples.RSA4096.Program

namespace Witgen.Examples.RSA4096
open Typed

-- Compare the surrounding layout without unfolding either large finite body.
attribute [local irreducible] comparatorWitness arithmeticWitness

/-- Composition preserves every cell and its comparator-before-arithmetic ordering. -/
theorem witnessProgram_layout (n s d : Nat) :
    (witnessProgram (F := Feature)).eval model h![n, s, d] =
      (comparatorWitness (F := Feature)).eval model h![n, s] ++
      (arithmeticWitness (F := Feature)).eval model h![n, s, d] := rfl

end Witgen.Examples.RSA4096
