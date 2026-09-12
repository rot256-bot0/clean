import Witgen.PrimeCertificates
import Witgen.Typed.SecpExamples
import Witgen.Typed.AffineExamples

/-! Concrete secp256k1 entry point. Both modulus primality facts are closed,
kernel-checked Lucas certificates, not hypotheses or custom axioms. -/
namespace Witgen.Typed.Secp

instance basePrime : Fact (modulus secpBase).Prime :=
  ⟨Witgen.PrimeCertificates.secpBase_prime⟩
instance scalarPrime : Fact (modulus secpScalar).Prime :=
  ⟨Witgen.PrimeCertificates.secpScalar_prime⟩

theorem concrete_mixed_correct (s t : FieldValue secpScalar) (b : FieldValue secpBase) :
    (mixed.eval model (.cons s (.cons t (.cons b .nil)))).val = mixedSpec s t b :=
  mixed_correct s t b

theorem concrete_generator_roundtrip : generatorRoundtrip.eval affineModel .nil = some generator :=
  generatorRoundtrip_correct

end Witgen.Typed.Secp
