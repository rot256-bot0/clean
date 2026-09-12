import Witgen.Typed.Export
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod

namespace Witgen.Typed

def CurveId.equation (c : CurveId) : WeierstrassCurve.Affine (ZMod (modulus c.base)) :=
  ⟨c.a1.val, c.a2.val, c.a3.val, c.a4.val, c.a6.val⟩

instance {R : Type} [CommRing R] [DecidableEq R] (W : WeierstrassCurve.Affine R) (x y : R) :
    Decidable (W.Nonsingular x y) :=
  decidable_of_iff
    (y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ ∧
      (W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y ≠ -y - W.a₁ * x - W.a₃))
    (by rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff])

/-- Compile-time checked literals. The curve equation is fixed by the sort. -/
inductive CurveLiteral (c : CurveId) where
  | infinity
  | affine (x y : FieldValue c.base)
      (valid : c.equation.Nonsingular (x.val : ZMod (modulus c.base)) (y.val : ZMod (modulus c.base)))

def CurveLiteral.point {c : CurveId} : CurveLiteral c → c.equation.Point
  | .infinity => .zero
  | .affine x y valid => .some (x.val : ZMod (modulus c.base)) (y.val : ZMod (modulus c.base)) valid

open Lean in
def CurveLiteral.json {c : CurveId} : CurveLiteral c → Json
  | .infinity => Json.mkObj [("infinity", .bool true)]
  | .affine x y _ => Json.mkObj [("x", .str (toString x.val)), ("y", .str (toString y.val))]

inductive CurveOp (c : CurveId) : Signature Ty where
  | const (literal : CurveLiteral c) : CurveOp c [] [] (.point c)
  | add : CurveOp c [.point c, .point c] [] (.point c)
  | mul : CurveOp c [.field c.scalar, .point c] [] (.point c)
  | inv : CurveOp c [.point c] [] (.point c)
  | eq : CurveOp c [.point c, .point c] [] .bool
  | msm : CurveOp c [.list (.pair (.field c.scalar) (.point c))] [] (.point c)
  | generator : CurveOp c [] [] (.point c)
  | identity : CurveOp c [] [] (.point c)
  | toAffine : CurveOp c [.point c] [] (.option (.pair (.field c.base) (.field c.base)))
  | fromAffine : CurveOp c [.pair (.field c.base) (.field c.base)] [] (.option (.point c))

namespace Curve

instance (f : FieldId) : NeZero (modulus f) := ⟨Nat.ne_of_gt (modulus_pos f)⟩

/-- A mathematical curve, never an implementation callback. Points are Mathlib's
nonsingular points on the supplied Weierstrass equation, including infinity. -/
structure Math (c : CurveId) where
  basePrime : Fact (modulus c.base).Prime
  nonsingular : c.equation.Δ ≠ 0
  generator : c.equation.Point

abbrev Math.equation {c : CurveId} (_M : Math c) := c.equation

abbrev Math.Point {c : CurveId} (M : Math c) := M.equation.Point

instance {c : CurveId} (M : Math c) : AddCommGroup M.Point :=
  letI := M.basePrime
  inferInstanceAs (AddCommGroup M.equation.Point)

abbrev AffinePair (c : CurveId) := FieldValue c.base × FieldValue c.base
abbrev Val {c : CurveId} (_M : Math c) :=
  Value FieldValue (UInt64 × UInt64 × UInt64 × UInt64) (fun d => d.equation.Point)

def mul {c : CurveId} (M : Math c) (s : FieldValue c.scalar) (p : M.Point) : M.Point := s.val • p
def eq {c : CurveId} (M : Math c) (p q : M.Point) : Bool := decide (p = q)
def msm {c : CurveId} (M : Math c) (terms : List (FieldValue c.scalar × M.Point)) : M.Point :=
  (terms.map (fun (s,p) => s.val • p)).sum

theorem literal_point_spec {c : CurveId} (x y : FieldValue c.base)
    (h : c.equation.Nonsingular (x.val : ZMod (modulus c.base)) (y.val : ZMod (modulus c.base))) :
    (CurveLiteral.affine x y h).point = .some _ _ h := rfl

theorem mul_spec {c : CurveId} (M : Math c) (s : FieldValue c.scalar) (p : M.Point) :
    mul M s p = s.val • p := rfl
theorem eq_spec {c : CurveId} (M : Math c) (p q : M.Point) : eq M p q = decide (p = q) := rfl
theorem msm_spec {c : CurveId} (M : Math c) (terms : List (FieldValue c.scalar × M.Point)) :
    msm M terms = (terms.map (fun (s,p) => s.val • p)).sum := rfl
@[simp] theorem msm_nil {c : CurveId} (M : Math c) : msm M [] = 0 := rfl
@[simp] theorem msm_singleton {c : CurveId} (M : Math c) (s : FieldValue c.scalar) (p : M.Point) :
    msm M [(s,p)] = mul M s p := by simp [msm, mul]

def toAffine {c : CurveId} (M : Math c) : M.Point → Option (AffinePair c)
  | .zero => none
  | .some x y _ => some (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)

def fromAffine {c : CurveId} (M : Math c) (xy : AffinePair c) : Option M.Point :=
  if h : M.equation.Nonsingular (xy.1.val : ZMod (modulus c.base)) (xy.2.val : ZMod (modulus c.base)) then
    some (.some _ _ h)
  else none

theorem fromAffine_isSome_iff {c : CurveId} (M : Math c) (xy : AffinePair c) :
    (fromAffine M xy).isSome = true ↔
      M.equation.Nonsingular (xy.1.val : ZMod (modulus c.base)) (xy.2.val : ZMod (modulus c.base)) := by
  simp [fromAffine]

theorem affine_roundtrip {c : CurveId} (M : Math c)
    (x y : ZMod (modulus c.base)) (h : M.equation.Nonsingular x y) :
    (toAffine M (.some x y h)).bind (fromAffine M) = some (.some x y h) := by
  simp only [toAffine, Option.bind_some, fromAffine, ZMod.natCast_zmod_val]
  rw [dif_pos h]

theorem fromAffine_toAffine {c : CurveId} (M : Math c) (xy : AffinePair c) (p : M.Point) :
    fromAffine M xy = some p ↔ toAffine M p = some xy := by
  cases p with
  | zero => simp [fromAffine, toAffine]
  | some x y h =>
    constructor
    · intro hp
      unfold fromAffine at hp
      split at hp
      · cases Option.some.inj hp
        simp only [toAffine, Option.some.injEq]
        apply Prod.ext <;> apply Fin.ext <;> simp [ZMod.val_natCast, Nat.mod_eq_of_lt]
      · contradiction
    · intro hp
      have round := affine_roundtrip M x y h
      rw [hp] at round
      exact round

/-- Each descriptor has its own actual point carrier; models for different curves
share this interpretation and compose through the generic signature sum. -/
def model {c : CurveId} (M : Math c) : Model (CurveOp c) (Val M) where
  eval := fun op args _ =>
    letI := M.basePrime
    match op, args with
    | .const literal, .nil => literal.point
    | .add, .cons p (.cons q .nil) => p + q
    | .mul, .cons s (.cons p .nil) => mul M s p
    | .inv, .cons p .nil => -p
    | .eq, .cons p (.cons q .nil) => eq M p q
    | .msm, .cons terms .nil => msm M terms
    | .generator, .nil => M.generator
    | .identity, .nil => 0
    | .toAffine, .cons p .nil => toAffine M p
    | .fromAffine, .cons xy .nil => fromAffine M xy

theorem const_spec {c : CurveId} (M : Math c) (literal : CurveLiteral c) :
    (model M).eval (.const literal) .nil .nil = literal.point := rfl

open Lean Methods in
def codec {c : CurveId} : OpCodec (CurveOp c) := fun op =>
  let tag := match op with
    | .const _ => "curve.const"
    | .add => "curve.add"
    | .mul => "curve.mul"
    | .inv => "curve.inv"
    | .eq => "curve.eq"
    | .msm => "curve.msm"
    | .generator => "curve.generator"
    | .identity => "curve.identity"
    | .toAffine => "curve.toAffine"
    | .fromAffine => "curve.fromAffine"
  let literal := match op with
    | .const value => [("value", value.json)]
    | _ => []
  Json.mkObj [("op", .str tag), ("static", Json.mkObj ([("curve", curveJson c)] ++ literal))]

end Curve
end Witgen.Typed

namespace Witgen.curve
open Typed
variable {F : Signature Ty} {Γ : List Ty} {c : CurveId}

def Const (c : CurveId) [Has (CurveOp c) F] (literal : CurveLiteral c) : Step F Γ (.point c) :=
  call (CurveOp.const literal) .nil .nil
def Add [Has (CurveOp c) F] (p q : Var Γ (.point c)) : Step F Γ (.point c) :=
  call (CurveOp.add (c := c)) h![p,q] .nil
def Mul [Has (CurveOp c) F] (s : Var Γ (.field c.scalar)) (p : Var Γ (.point c)) : Step F Γ (.point c) :=
  call (CurveOp.mul (c := c)) h![s,p] .nil
def Inv [Has (CurveOp c) F] (p : Var Γ (.point c)) : Step F Γ (.point c) :=
  call (CurveOp.inv (c := c)) h![p] .nil
def Eq [Has (CurveOp c) F] (p q : Var Γ (.point c)) : Step F Γ .bool :=
  call (CurveOp.eq (c := c)) h![p,q] .nil
def MSM [Has (CurveOp c) F] (terms : Var Γ (.list (.pair (.field c.scalar) (.point c)))) :
    Step F Γ (.point c) := call (CurveOp.msm (c := c)) h![terms] .nil
def Generator (c : CurveId) [Has (CurveOp c) F] : Step F Γ (.point c) :=
  call (CurveOp.generator (c := c)) .nil .nil
def Identity (c : CurveId) [Has (CurveOp c) F] : Step F Γ (.point c) :=
  call (CurveOp.identity (c := c)) .nil .nil
def ToAffine [Has (CurveOp c) F] (p : Var Γ (.point c)) :
    Step F Γ (.option (.pair (.field c.base) (.field c.base))) :=
  call (CurveOp.toAffine (c := c)) h![p] .nil
def FromAffine (c : CurveId) [Has (CurveOp c) F]
    (xy : Var Γ (.pair (.field c.base) (.field c.base))) : Step F Γ (.option (.point c)) :=
  call (CurveOp.fromAffine (c := c)) h![xy] .nil
end Witgen.curve
