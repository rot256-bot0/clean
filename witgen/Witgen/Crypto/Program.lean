import Witgen.Crypto.Features
import Witgen.Authoring

namespace Witgen.Crypto

/-- Authoring smart constructors hide empty argument/region plumbing. -/
def fieldConst {F : Signature Ty} [Has FieldOp F] {Γ : List Ty}
    (n : Nat) : Step F Γ .scalar := call (FieldOp.const n) h![] .nil

def fieldAdd {F : Signature Ty} [Has FieldOp F] {Γ : List Ty}
    (a b : Var Γ .scalar) : Step F Γ .scalar := call FieldOp.add h![a, b] .nil

def fieldMul {F : Signature Ty} [Has FieldOp F] {Γ : List Ty}
    (a b : Var Γ .scalar) : Step F Γ .scalar := call FieldOp.mul h![a, b] .nil

/-- An open, feature-polymorphic implementation of a custom circuit witness.
Named do-notation elaborates into finite typed syntax; the record operation is
exactly the reusable schema-based StructOp, not a circuit-specific constructor. -/
def quadratic {F : Signature Ty} [Has FieldOp F] [Has (StructOp schemaDesc) F] :
    Program F [.scalar, .scalar] .quad :=
  witgen [x, y] do
    let square ← fieldMul x x
    let output ← fieldAdd square y
    let witness ← makeNamedStruct schemaDesc .quad
      fields![square := square, output := output]
    return witness

/-- Circuit-level feature. Its implementation lowers to arithmetic + structural
features; its semantic specification includes both required witness cells. -/
inductive QuadFeature : Signature Ty where
  | generate : QuadFeature [.scalar, .scalar] [] .quad

def generateQuad {F : Signature Ty} [Has QuadFeature F] {Γ : List Ty}
    (x y : Var Γ .scalar) : Step F Γ .quad := call QuadFeature.generate h![x, y] .nil

def quadFeatureModel {p : Nat} (_hp : 0 < p) : Model QuadFeature (Val (Fin p)) where
  eval := fun op args _ => match op, args with
    | .generate, .cons x (.cons y .nil) =>
      ⟨Residue.mul x x, Residue.add (Residue.mul x x) y⟩

def quadToField : Template QuadFeature FieldSig
  | _, _, _, .generate, _ => quadratic

def quadraticFeature : Program QuadFeature [.scalar, .scalar] .quad :=
  witgen [x, y] do
    let witness ← generateQuad x y
    return witness

/-- The exported field AST is actually produced by the circuit-feature lowering. -/
def quadraticField : Program FieldSig [.scalar, .scalar] .quad :=
  quadraticFeature.lower quadToField

def quadraticNat (p : Nat) : Program NatSig [.scalar, .scalar] .quad :=
  quadraticField.lower (fieldToNat p)

theorem quadraticField_eval {p : Nat} (hp : 0 < p) (x y : Fin p) :
    quadraticField.eval (fieldModel hp) (.cons x (.cons y .nil)) =
      (⟨Residue.mul x x, Residue.add (Residue.mul x x) y⟩ : QuadWitness (Fin p)) := rfl

/-- Local circuit-feature implementation law, using ordinary equality. -/
theorem quadToField_law {p : Nat} (hp : 0 < p) :
    Template.Respects (quadFeatureModel hp) (fieldModel hp) quadToField
      (fun _ x y => x = y) := by
  intro args shapes t op xs ys fs regions hr _
  cases op
  cases xs with
  | cons x xs => cases xs with
    | cons y xs =>
      cases xs
      cases ys with
      | cons x' ys => cases ys with
        | cons y' ys =>
          cases ys
          rcases hr with ⟨hx, hy, _⟩
          cases hx
          cases hy
          rfl

theorem eq_env {S : Type} {V : S → Type} {Γ : List S} (xs : HList V Γ) :
    HList.Rel (fun _ x y => x = y) xs xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨rfl, ih⟩

/-- Any subprogram over the custom feature can use the same proved lowering. -/
theorem quadToField_correct {p : Nat} (hp : 0 < p)
    (program : Program QuadFeature Γ t) (env : HList (Val (Fin p)) Γ) :
    (program.lower quadToField).eval (fieldModel hp) env =
      program.eval (quadFeatureModel hp) env :=
  (Program.eval_lower_related quadToField (quadFeatureModel hp) (fieldModel hp)
    (fun _ x y => x = y) (quadToField_law hp) program env env (eq_env env)).symm

theorem quadraticNat_eval {p : Nat} (hp : 0 < p) (x y : Fin p) :
    (quadraticNat p).eval natModel (.cons x.val (.cons y.val .nil)) =
      (⟨(x.val * x.val) % p, ((x.val * x.val) % p + y.val) % p⟩ : QuadWitness Nat) :=
  (fieldToNat_correct hp quadraticField (.cons x (.cons y .nil))).symm

end Witgen.Crypto
