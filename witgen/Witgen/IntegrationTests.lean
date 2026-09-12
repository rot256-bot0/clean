import Witgen.Integration

open Witgen

#check Integration.quadraticFieldWitgen
#check Integration.quadraticField_generates
#check Integration.quadraticField_buffer

example : Integration.quadraticFieldWitgen.generate ⟨3, 4⟩ = ⟨9, 13⟩ := rfl

#print axioms Integration.quadraticField_buffer

#check Integration.quadraticNatWitgen
#check Integration.quadraticWordWitgen
#check Integration.modMulNatWitgen
#check Integration.modMulWordWitgen
#check Integration.quadraticWord_buffer
#check Integration.modMulWord_buffer

example : Integration.quadraticNatWitgen.generate ⟨3, 4⟩ = ⟨9, 13⟩ := rfl
example : Integration.quadraticWordWitgen.generate ⟨3, 4⟩ = ⟨9, 13⟩ := rfl
example : Integration.modMulNatWitgen.generate ⟨15, 15, 16⟩ = ⟨225, 14, 1⟩ := rfl
example : Integration.modMulWordWitgen.generate ⟨15, 15, 16⟩ = ⟨225, 14, 1⟩ := rfl

#print axioms Integration.quadraticWord_buffer
#print axioms Integration.modMulWord_buffer
