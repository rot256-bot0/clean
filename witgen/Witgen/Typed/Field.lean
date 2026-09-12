import Witgen.Typed.Types
import Witgen.Authoring

namespace Witgen.Typed

inductive FieldOp (f : FieldId) : Signature Ty where
  | const (n : Nat) : FieldOp f [] [] (.field f)
  | add : FieldOp f [.field f, .field f] [] (.field f)
  | mul : FieldOp f [.field f, .field f] [] (.field f)
  | square : FieldOp f [.field f] [] (.field f)

def fieldModel (f : FieldId) : Model (FieldOp f) FieldVal where
  eval := fun op args _ => match op, args with
    | .const n, .nil => Residue.ofNat (modulus_pos f) n
    | .add, .cons a (.cons b .nil) => Residue.add a b
    | .mul, .cons a (.cons b .nil) => Residue.mul a b
    | .square, .cons a .nil => Residue.square a

/-- Every field feature keeps its identity, even in a dynamically assembled signature. -/
inductive AnyFieldOp : Signature Ty where
  | field (f : FieldId) (op : FieldOp f args shapes t) : AnyFieldOp args shapes t

instance (f : FieldId) : Has (FieldOp f) AnyFieldOp where
  inject := .field f
  injective := by intro args shapes t a b h; cases h; rfl

def anyFieldModel : Model AnyFieldOp FieldVal where
  eval := fun (.field f op) args bodies => (fieldModel f).eval op args bodies

/-- A backend fallback replaces only the implementation, not the caller API. -/
def squareFallback (f : FieldId) : Template (FieldOp f) (FieldOp f)
  | _, _, _, .const n, .nil => .let_ (.const n) .nil .nil (.ret .zero)
  | _, _, _, .add, .nil => .let_ .add h![.zero, .succ .zero] .nil (.ret .zero)
  | _, _, _, .mul, .nil => .let_ .mul h![.zero, .succ .zero] .nil (.ret .zero)
  | _, _, _, .square, .nil => .let_ .mul h![.zero, .zero] .nil (.ret .zero)

private theorem eq_of_hrel {ts : List Ty} (xs ys : HList FieldVal ts)
    (h : HList.Rel (fun _ a b => a = b) xs ys) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys =>
      have hxy := h.1
      have hxs := ih ys h.2
      cases hxy; cases hxs; rfl

theorem squareFallback_respects (f : FieldId) :
    Template.Respects (fieldModel f) (fieldModel f) (squareFallback f)
      (fun _ a b => a = b) := by
  intro args shapes t op xs ys fs regions hr _
  cases eq_of_hrel xs ys hr
  cases op with
  | const n => cases xs; cases regions; rfl
  | add =>
    cases xs with | cons a tail =>
      cases tail with | cons b tail =>
        cases tail; cases regions; rfl
  | mul =>
    cases xs with | cons a tail =>
      cases tail with | cons b tail =>
        cases tail; cases regions; rfl
  | square =>
    cases xs with | cons a tail =>
      cases tail; cases regions
      exact Residue.square_eq_mul a

def certifiedSquareFallback (f : FieldId) :
    CertifiedLowering (fieldModel f) (fieldModel f) (fun _ a b => a = b) :=
  .ofTemplate _ _ (squareFallback f) _ (squareFallback_respects f)

end Witgen.Typed

namespace Witgen.field
open Typed

variable {F : Signature Ty} {Γ : List Ty} {f : FieldId}

def Const (f : FieldId) [Has (FieldOp f) F] (n : Nat) :
    Step F Γ (.field f) := call (FieldOp.const (f := f) n) .nil .nil

def Add [Has (FieldOp f) F] (a b : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.add (f := f)) h![a, b] .nil

def Mul [Has (FieldOp f) F] (a b : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.mul (f := f)) h![a, b] .nil

def Square [Has (FieldOp f) F] (a : Var Γ (.field f)) : Step F Γ (.field f) :=
  call (FieldOp.square (f := f)) h![a] .nil

end Witgen.field
