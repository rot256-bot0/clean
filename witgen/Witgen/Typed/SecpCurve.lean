import Witgen.Typed.Types
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-! The genuine secp256k1 curve, not a discrete-log model. Addition requires the
explicit base primality fact; the concrete instance is supplied in Secp.lean. -/
namespace Witgen.Typed.Secp

abbrev Base := ZMod (modulus secpBase)

instance : NeZero (modulus secpBase) := ⟨Nat.ne_of_gt (modulus_pos secpBase)⟩

def curve : WeierstrassCurve.Affine Base := ⟨0, 0, 0, 0, 7⟩
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

/-- A total coordinate view. Identity has no affine x; this API explicitly maps it to zero. -/
def xCoord : Point → FieldValue secpBase
  | .zero => Residue.ofNat (modulus_pos secpBase) 0
  | .some x _ _ => ⟨x.val, ZMod.val_lt x⟩

/-- Canonical natural action. Mathlib's point group uses logarithmic `nsmulBinRec`.
No assertion about reduction modulo group order is needed or made here. -/
def scale [Fact (modulus secpBase).Prime] (s : FieldValue secpScalar) (p : Point) : Point :=
  s.val • p

theorem scale_spec [Fact (modulus secpBase).Prime] (s : FieldValue secpScalar) (p : Point) :
    scale s p = s.val • p := rfl

/-- Affine coordinates contain base-field values, never scalar-field values. -/
abbrev AffinePair := FieldValue secpBase × FieldValue secpBase

def toAffine : Point → Option AffinePair
  | .zero => none
  | .some x y _ => some (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)

theorem discriminant_ne_zero : curve.Δ ≠ 0 := by
  decide

private theorem equation_of_short {x y : Base} (h : y ^ 2 = x ^ 3 + 7) : curve.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simpa [curve] using h

/-- An off-curve pair returns None, never the identity point. -/
def fromAffine (xy : AffinePair) : Option Point :=
  let x : Base := xy.1.val
  let y : Base := xy.2.val
  if h : y ^ 2 = x ^ 3 + 7 then
    some (.some x y (curve.equation_iff_nonsingular_of_Δ_ne_zero discriminant_ne_zero |>.mp
      (equation_of_short h)))
  else none

theorem fromAffine_zero_zero :
    fromAffine (Residue.ofNat (modulus_pos secpBase) 0,
      Residue.ofNat (modulus_pos secpBase) 0) = none := by
  unfold fromAffine
  have h : ¬ (0 : Base) ^ 2 = (0 : Base) ^ 3 + 7 := by decide
  exact dif_neg h

/-- Every genuine affine point roundtrips, with coordinates preserved. -/
theorem affine_roundtrip (x y : Base) (h : curve.Nonsingular x y) :
    (toAffine (.some x y h)).bind fromAffine = some (.some x y h) := by
  have heq : y ^ 2 = x ^ 3 + 7 := by
    have h' := (WeierstrassCurve.Affine.equation_iff ..).mp h.1
    simpa [curve] using h'
  simp only [toAffine, Option.bind_some, fromAffine, ZMod.natCast_zmod_val]
  rw [dif_pos heq]

theorem generator_roundtrip : (toAffine generator).bind fromAffine = some generator :=
  affine_roundtrip _ _ generator_nonsingular

/-- Accepted coordinates are exactly the curve equation, not a vacuous witness predicate. -/
theorem fromAffine_isSome_iff (xy : AffinePair) :
    (fromAffine xy).isSome = true ↔
      (xy.2.val : Base) ^ 2 = (xy.1.val : Base) ^ 3 + 7 := by
  simp [fromAffine]

end Witgen.Typed.Secp
