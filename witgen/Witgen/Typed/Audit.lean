import Witgen.Typed.CurveAudit
import Witgen.Typed.CurveProgramTests
import Witgen.Typed.CurveNamedTests
import Witgen.Typed.CurveIntegrationTests
import Witgen.Typed.PublicTests
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
#print axioms Witgen.Typed.ValueOp.case_none
#print axioms Witgen.Typed.ValueOp.case_some
#print axioms Witgen.Typed.Curve.const_spec
#print axioms Witgen.Typed.Curve.literal_point_spec
#print axioms Witgen.Typed.Curve.mul_spec
#print axioms Witgen.Typed.Curve.eq_spec
#print axioms Witgen.Typed.Curve.msm_spec
#print axioms Witgen.Typed.Curve.msm_nil
#print axioms Witgen.Typed.Curve.msm_singleton
#print axioms Witgen.Typed.Curve.affine_roundtrip
#print axioms Witgen.Typed.Curve.fromAffine_toAffine
#print axioms Witgen.Typed.Curve.fromAffine_isSome_iff
#print axioms Witgen.Typed.Secp.math
#print axioms Witgen.Typed.Secp.mixed_identity_none
#print axioms Witgen.Typed.Secp.curveEq_correct
#print axioms Witgen.Typed.Secp.curveMSM_correct
#print axioms Witgen.Typed.Secp.constructedMSM_correct
#print axioms Witgen.Typed.Secp.constantGenerator_correct
#print axioms Witgen.Typed.Secp.constantIdentity_correct
#print axioms Witgen.Typed.u64FieldProgram_correct
#print axioms Witgen.Typed.Secp.generator_nonsingular
#print axioms Witgen.Typed.Secp.mul_spec
#print axioms Witgen.Typed.Secp.fromAffine_zero_zero
#print axioms Witgen.Typed.Secp.generator_roundtrip
#print axioms Witgen.Typed.Secp.mixed_correct
#print axioms Witgen.Typed.Secp.mixed_one_one
#print axioms Witgen.Typed.Secp.roundtripProgram_eval
#print axioms Witgen.Typed.Secp.generatorRoundtrip_correct
#print axioms Witgen.Typed.Secp.invalidPair_rejects_zero
#print axioms Witgen.Typed.Public.mixed_eq
#print axioms Witgen.Typed.Public.mixed_correct
#print axioms Witgen.Typed.CurveProgramTests.curveEq_correct
#print axioms Witgen.Typed.CurveProgramTests.curveMSM_correct
#print axioms Witgen.Typed.CurveProgramTests.constructedMSM_correct
#print axioms Witgen.Typed.CurveProgramTests.roundtrip_correct
#print axioms Witgen.Typed.CurveIntegrationTests.field_neg
#print axioms Witgen.Typed.CurveIntegrationTests.field_inv
#print axioms Witgen.Typed.CurveIntegrationTests.field_inv_zero
#print axioms Witgen.Typed.CurveIntegrationTests.mixed_correct
#print axioms Witgen.Typed.CurveIntegrationTests.roundtrip_eval
#print axioms Witgen.Typed.CurveIntegrationTests.generator_roundtrip
