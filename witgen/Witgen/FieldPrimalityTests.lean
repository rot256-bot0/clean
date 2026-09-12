import Witgen.PrimeCertificates
import Witgen.Crypto.Field

example : Nat.Prime Witgen.Crypto.bn254Modulus := Witgen.PrimeCertificates.bn254Scalar_prime
#print axioms Witgen.PrimeCertificates.bn254Scalar_prime
