import Witgen.Typed.Secp

namespace Witgen.Typed.Secp.ConcreteTests
open Witgen

example : Nat.Prime (modulus secpBase) := basePrime.out
example : Nat.Prime (modulus secpScalar) := scalarPrime.out
example : generator + -generator = 0 := by simp

/-- Independent affine-doubling values (also recorded in fixtures/secp_known_points.json). -/
def twiceX : Nat := 89565891926547004231252920425935692360644145829622209833684329913297188986597
def twiceY : Nat := 12158399299693830322967808612713398636155367887041628176798871954788371653930

#guard toAffine (generator + generator) == some
  (Residue.ofNat (modulus_pos secpBase) twiceX, Residue.ofNat (modulus_pos secpBase) twiceY)
#guard toAffine (-generator) == some
  (Residue.ofNat (modulus_pos secpBase) generatorX,
   Residue.ofNat (modulus_pos secpBase)
     83121579216557378445487899878180864668798711284981320763518679672151497189239)
#guard toAffine (mul (Residue.ofNat (modulus_pos secpScalar) (modulus secpScalar - 1)) generator) ==
  toAffine (-generator)
#guard (mixed.eval mixedModel h![Residue.ofNat (modulus_pos secpScalar) 1,
  Residue.ofNat (modulus_pos secpScalar) 1]).map Fin.val ==
    some 15049581136193944005155656881674271607086196878768533802525739169400035159716
#guard mixed.eval mixedModel h![Residue.ofNat (modulus_pos secpScalar) 1,
  Residue.ofNat (modulus_pos secpScalar) 0] == none
#guard (generatorRoundtrip.eval affineModel .nil).map toAffine == some (toAffine generator)
#guard invalidPair.eval affineModel h![(Residue.ofNat (modulus_pos secpBase) 0,
  Residue.ofNat (modulus_pos secpBase) 0)] == none
#guard toAffine (0 : Point) == none

end Witgen.Typed.Secp.ConcreteTests
