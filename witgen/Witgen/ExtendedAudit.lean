import Witgen.SqrtAudit
import Witgen.SqrtChoiceAudit
import Witgen.FieldInversesTests
import Witgen.FieldExtendedTests
import Witgen.FieldNatExtendedTests
import Witgen.FieldPrimalityTests
import Witgen.PartialLoweringTests
import Witgen.U64.PartialTests
import Witgen.Branching.Tests
import Witgen.Branching.SurfaceTests
import Witgen.Branching.ProgramTests
import Witgen.Branching.SurfaceControls

#print axioms Witgen.PrimeCertificates.bn254Scalar_prime
#print axioms Witgen.Typed.modulus_prime
#print axioms Witgen.Typed.Residue.inv_zero
#print axioms Witgen.Typed.Residue.add_neg
#print axioms Witgen.Typed.Residue.mul_inv_of_prime
#print axioms Witgen.Typed.Residue.mul_inv
#print axioms Witgen.Typed.NatMethods.handler_respects
#print axioms Witgen.Program.eval_mapHandler?_related
#print axioms Witgen.PartialCertifiedLowering.ofHandler
#print axioms Witgen.U64.compile_accepted
#print axioms Witgen.U64.lower_respects
#print axioms Witgen.U64.certified
#print axioms Witgen.U64.caller_correct
#print axioms Witgen.BranchOp.eval_true
#print axioms Witgen.BranchOp.eval_false
#print axioms Witgen.Branching.conditional_true
#print axioms Witgen.Branching.conditional_false
#print axioms Witgen.Branching.match_none
#print axioms Witgen.Branching.match_some
#print axioms Witgen.Typed.FieldSqrt.sqrt_sound
#print axioms Witgen.Typed.FieldSqrt.sqrt_none_iff
#print axioms Witgen.Typed.FieldSqrt.canonical_unique
#print axioms Witgen.Typed.FieldSqrt.sqrt_eq_some_iff
#print axioms Witgen.Typed.FieldSqrt.sqrt_square
#print axioms Witgen.Typed.FieldSqrt.sqrt_zero
#print axioms Witgen.Typed.FieldSqrt.sqrt_of_candidate
#print axioms Witgen.Typed.FieldSqrt.sqrt_none_of_euler
#print axioms Witgen.Typed.Residue.sqrt_eq_some_iff
#print axioms Witgen.Typed.Residue.sqrt_sound
#print axioms Witgen.Typed.Residue.sqrt_none_iff
#print axioms Witgen.Typed.Residue.sqrt_canonical_unique
#print axioms Witgen.Typed.Residue.sqrt_zero
#print axioms Witgen.Typed.Residue.sqrt_square
#print axioms Witgen.Typed.Residue.sqrt_nat_rel
#print axioms Witgen.Typed.sqrtNat_mod
#print axioms Witgen.Typed.Residue.sub_eq_add_neg
#print axioms Witgen.Typed.Residue.sub_val
#print axioms Witgen.Typed.Residue.sub_self
#print axioms Witgen.Typed.FieldSubTests.lowering_correct
#print axioms Witgen.Typed.squareFallback_respects
