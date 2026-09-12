import Witgen.Crypto.Custom

/-! Explicit proof-dependency receipts. No primality theorem, native decision,
foreign execution, or unbounded-to-machine-word claim is used by these proofs. -/
#print axioms Witgen.Crypto.bn254Positive
#print axioms Witgen.Crypto.Residue.mul_val
#print axioms Witgen.Crypto.fieldToNat_law
#print axioms Witgen.Crypto.fieldToNat_correct
#print axioms Witgen.Crypto.quadToField_correct
#print axioms Witgen.Crypto.QuadCircuit.sound
#print axioms Witgen.Crypto.QuadCircuit.constraints_iff
#print axioms Witgen.Crypto.QuadCircuit.Slots.noAliases
#print axioms Witgen.Crypto.QuadCircuit.Slots.covers
#print axioms Witgen.Crypto.quadNatWitgen
#print axioms Witgen.Crypto.quad_full_buffer_agrees
#print axioms Witgen.Crypto.quad_nat_raw_buffer
#print axioms Witgen.Crypto.quad_nat_buffer_correct
#print axioms Witgen.Crypto.envelopeNat_raw_buffer
#print axioms Witgen.Crypto.envelope_nat_buffer_correct
#print axioms Witgen.Crypto.envelopeOutputPaths_exact
