import Witgen.Typed.SecpCurve
namespace Witgen.Typed.Secp.Tests
example : generatorX =
    55066263022277343669578718895168534326250603453777594175500187360389116729240 := rfl
example : curve.Equation (generatorX : Base) (generatorY : Base) := generator_equation
example : toAffine generator = some (Residue.ofNat (modulus_pos secpBase) generatorX,
    Residue.ofNat (modulus_pos secpBase) generatorY) := rfl
example [Fact (modulus secpBase).Prime] : generator + -generator = 0 := by simp
example [Fact (modulus secpBase).Prime] : mul (Residue.ofNat (modulus_pos secpScalar) 1) generator =
    generator := by
  change (1 : Nat) • generator = generator
  exact one_nsmul generator
example : curve.Nonsingular (generatorX : Base) (generatorY : Base) := by decide
example [Fact (modulus secpBase).Prime] :
    (Curve.model math).eval (.const generatorLiteral) .nil .nil = generator := rfl
end Witgen.Typed.Secp.Tests
