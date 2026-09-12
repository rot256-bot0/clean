import Witgen.Typed.SecpCurve
namespace Witgen.Typed.Secp.AffineTests
example : toAffine (0 : Point) = none := rfl
example : toAffine generator = some (Residue.ofNat (modulus_pos secpBase) generatorX,
    Residue.ofNat (modulus_pos secpBase) generatorY) := rfl
example [Fact (modulus secpBase).Prime] :
    fromAffine (Residue.ofNat (modulus_pos secpBase) 0, Residue.ofNat (modulus_pos secpBase) 0) = none := by
  exact fromAffine_zero_zero
example [Fact (modulus secpBase).Prime] :
    (toAffine generator).bind fromAffine = some generator := generator_roundtrip
end Witgen.Typed.Secp.AffineTests
