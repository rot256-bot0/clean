import Witgen.U64.Lowering

/- The executable field model must not inherit the classical existence proof
used only to establish square-root completeness. Keep the U64 trust policy. -/

/-- info: 'Witgen.Typed.FieldSqrt.sqrt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.Typed.FieldSqrt.sqrt

/-- info: 'Witgen.Typed.Residue.sqrt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.Typed.Residue.sqrt

/-- info: 'Witgen.Typed.sqrtNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.Typed.sqrtNat

/-- info: 'Witgen.Typed.fieldModel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.Typed.fieldModel

/-- info: 'Witgen.Typed.Residue.sqrt_nat_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.Typed.Residue.sqrt_nat_rel

/-- info: 'Witgen.U64.lower_respects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.U64.lower_respects

/-- info: 'Witgen.U64.certified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.U64.certified

/-- info: 'Witgen.U64.caller_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Witgen.U64.caller_correct
