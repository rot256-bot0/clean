import Witgen.Typed.Curve
import Mathlib.Tactic.NormNum

namespace Witgen.Typed.Secp

abbrev Base := ZMod (modulus secpBase)
instance : NeZero (modulus secpBase) := ⟨Nat.ne_of_gt (modulus_pos secpBase)⟩
abbrev curve : WeierstrassCurve.Affine Base := secp256k1.equation
abbrev Point := curve.Point

def generatorX : Nat :=
  55066263022277343669578718895168534326250603453777594175500187360389116729240
def generatorY : Nat :=
  32670510020758816978083085130507043184471273380659243275938904335757337482424

theorem generator_equation : curve.Equation (generatorX : Base) (generatorY : Base) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change (generatorY : Base) ^ 2 + 0 * generatorX * generatorY + 0 * generatorY =
    (generatorX : Base) ^ 3 + 0 * (generatorX : Base) ^ 2 + 0 * generatorX + 7
  decide

theorem generator_nonsingular : curve.Nonsingular (generatorX : Base) (generatorY : Base) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨generator_equation, Or.inr ?_⟩
  change (generatorY : Base) ≠ -(generatorY : Base) - 0 * generatorX - 0
  decide

def generator : Point := .some _ _ generator_nonsingular

def generatorLiteral : CurveLiteral secp256k1 :=
  .affine (Residue.ofNat (modulus_pos secpBase) generatorX)
    (Residue.ofNat (modulus_pos secpBase) generatorY) generator_nonsingular

theorem discriminant_ne_zero : curve.Δ ≠ 0 := by decide

/-- Actual Mathlib equation/points instantiate the generic mathematical model. -/
def math [Fact (modulus secpBase).Prime] : Curve.Math secp256k1 where
  basePrime := inferInstance
  nonsingular := discriminant_ne_zero
  generator := generator

def mul [Fact (modulus secpBase).Prime] (s : FieldValue secpScalar) (p : Point) : Point :=
  Curve.mul math s p

theorem mul_spec [Fact (modulus secpBase).Prime] (s : FieldValue secpScalar) (p : Point) :
    mul s p = s.val • p := rfl

abbrev AffinePair := FieldValue secpBase × FieldValue secpBase

def toAffine : Point → Option AffinePair
  | .zero => none
  | .some x y _ => some (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)

def fromAffine [Fact (modulus secpBase).Prime] (xy : AffinePair) : Option Point :=
  Curve.fromAffine math xy

private theorem zero_not_equation :
    ¬ ((0 : Base) ^ 2 + 0 * 0 * 0 + 0 * 0 = 0 ^ 3 + 0 * 0 ^ 2 + 0 * 0 + 7) := by decide

theorem fromAffine_zero_zero [Fact (modulus secpBase).Prime] :
    fromAffine (Residue.ofNat (modulus_pos secpBase) 0,
      Residue.ofNat (modulus_pos secpBase) 0) = none := by
  unfold fromAffine Curve.fromAffine
  apply dif_neg
  intro h
  have heq := (WeierstrassCurve.Affine.equation_iff ..).mp h.1
  change (0 : Base) ^ 2 + 0 * 0 * 0 + 0 * 0 = 0 ^ 3 + 0 * 0 ^ 2 + 0 * 0 + 7 at heq
  exact zero_not_equation heq

theorem affine_roundtrip [Fact (modulus secpBase).Prime]
    (x y : Base) (h : curve.Nonsingular x y) :
    (toAffine (.some x y h)).bind fromAffine = some (.some x y h) :=
  Curve.affine_roundtrip math x y h

theorem generator_roundtrip [Fact (modulus secpBase).Prime] :
    (toAffine generator).bind fromAffine = some generator := affine_roundtrip _ _ generator_nonsingular

theorem fromAffine_isSome_iff [Fact (modulus secpBase).Prime] (xy : AffinePair) :
    (fromAffine xy).isSome = true ↔
      (xy.2.val : Base) ^ 2 = (xy.1.val : Base) ^ 3 + 7 := by
  calc
    _ ↔ math.equation.Nonsingular (xy.1.val : Base) (xy.2.val : Base) :=
      Curve.fromAffine_isSome_iff math xy
    _ ↔ _ := by
      change curve.Nonsingular (xy.1.val : Base) (xy.2.val : Base) ↔ _
      rw [← curve.equation_iff_nonsingular_of_Δ_ne_zero discriminant_ne_zero,
        WeierstrassCurve.Affine.equation_iff]
      simp [curve, CurveId.equation]

end Witgen.Typed.Secp
