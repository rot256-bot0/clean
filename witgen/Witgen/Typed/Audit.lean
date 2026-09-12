import Witgen.Typed.FieldTests
import Witgen.Typed.TypingTests
import Witgen.Typed.MethodTests
import Witgen.Typed.MethodTypingTests
import Witgen.Typed.ExportTests
import Witgen.Typed.ExampleTests
import Witgen.Typed.NatMethodTests
import Witgen.Typed.SecpCurveTests
import Witgen.Typed.SecpTests
import Witgen.Typed.SecpExampleTests
import Witgen.Typed.AffineTests
import Witgen.Typed.AffineExampleTests
import Witgen.Typed.ValueTests
import Witgen.Typed.SecpConcreteTests
import Witgen.Typed.U64IntegrationTests

#print axioms Witgen.Methods.call_substitution
#print axioms Witgen.Methods.Library.ref_unique
#print axioms Witgen.Methods.Library.earlier_only
#print axioms Witgen.Methods.Library.caller_refinement
#print axioms Witgen.Methods.libraryJson_size
#print axioms Witgen.Typed.squareFallback_respects
#print axioms Witgen.Typed.NatMethods.handler_respects
#print axioms Witgen.Typed.fieldProgramNat_correct
#print axioms Witgen.Typed.Secp.basePrime
#print axioms Witgen.Typed.Secp.scalarPrime
#print axioms Witgen.Typed.Secp.generator_equation
#print axioms Witgen.Typed.Secp.discriminant_ne_zero
#print axioms Witgen.Typed.Secp.affine_roundtrip
#print axioms Witgen.Typed.Secp.fromAffine_isSome_iff
#print axioms Witgen.Typed.Secp.concrete_mixed_correct
#print axioms Witgen.Typed.Secp.concrete_generator_roundtrip
#print axioms Witgen.Typed.u64FieldProgram_correct
