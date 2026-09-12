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
