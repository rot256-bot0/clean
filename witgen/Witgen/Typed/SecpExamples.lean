import Witgen.Typed.SecpFeature
import Witgen.Typed.CurvePrograms

namespace Witgen.Typed.Secp
open Witgen

def mixed : Program MixedFeature [.field secpScalar, .field secpScalar] (.option (.field secpBase)) :=
  CurvePrograms.mixed secp256k1

/-- Independent modular-arithmetic/group specification. Infinity stays absent. -/
def mixedSpec [Fact (modulus secpBase).Prime]
    (s t : FieldValue secpScalar) : Option (FieldValue secpBase) :=
  let n := modulus secpScalar
  let k := ((s.val ^ 2 % n * t.val) % n + s.val) % n
  (toAffine (k • generator + -generator)).map fun (x,y) =>
    Residue.add (Residue.mul (Residue.square x) y) x

theorem mixed_correct [Fact (modulus secpBase).Prime] (s t : FieldValue secpScalar) :
    mixed.eval mixedModel h![s,t] = mixedSpec s t := by
  simp only [mixed, CurvePrograms.mixed, Step.bindNamed, Step.bind, call, field.Square,
    field.Add, field.Mul, curve.Generator, curve.Mul, curve.Inv, curve.Add, curve.ToAffine,
    value.Match, value.None, value.Some, value.Fst, value.Snd, Program.eval, HList.map,
    Var.get, Regions.eval, mixedModel, model, fieldsModel, fieldModel, secpModel,
    Model.sum, ValueOp.model, Curve.model, Program.withInputs, inputRefs, Var.weakenBy, Has.inject]
  let n := modulus secpScalar
  let p : Point := (((s.val ^ 2 % n * t.val) % n + s.val) % n) • generator + -generator
  have hp : Curve.mul math (Residue.add (Residue.mul (Residue.square s) t) s) math.generator +
      -math.generator = p := rfl
  rw [hp]
  have hs : mixedSpec s t = (toAffine p).map
      (fun (x,y) => Residue.add (Residue.mul (Residue.square x) y) x) := rfl
  rw [hs]
  rw [show Curve.toAffine math p = toAffine p from by cases p <;> rfl]
  cases toAffine p <;> rfl

theorem mixed_one_one [Fact (modulus secpBase).Prime] :
    mixed.eval mixedModel h![Residue.ofNat (modulus_pos secpScalar) 1,
      Residue.ofNat (modulus_pos secpScalar) 1] =
    (toAffine generator).map (fun (x,y) => Residue.add (Residue.mul (Residue.square x) y) x) := by
  rw [mixed_correct]
  change (toAffine ((2 : Nat) • generator + -generator)).map _ = _
  rw [two_nsmul, add_neg_cancel_right]

theorem mixed_identity_none [Fact (modulus secpBase).Prime] :
    mixed.eval mixedModel h![Residue.ofNat (modulus_pos secpScalar) 1,
      Residue.ofNat (modulus_pos secpScalar) 0] = none := by
  rw [mixed_correct]
  change (toAffine ((1 : Nat) • generator + -generator)).map
    (fun (x,y) => Residue.add (Residue.mul (Residue.square x) y) x) = none
  rw [one_nsmul, add_neg_cancel]
  rfl

open Lean Methods in
def mixedJson : Except String Json :=
  moduleJson typeJson mixedCodec .nil "secp_mixed_fields" ["s", "t"]
    (mixed.mapHandler Sum.inl)

end Witgen.Typed.Secp
