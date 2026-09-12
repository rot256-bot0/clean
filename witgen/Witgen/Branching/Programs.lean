import Witgen.Branching.Basic
import Witgen.Typed.Values
import Witgen.Typed.NatMethods

namespace Witgen.Branching
open Typed

abbrev Feature (f : FieldId) := SigSum (FieldOp f) (SigSum (BranchOp Ty.bool) ValueOp)

instance (f : FieldId) : Has (BranchOp Ty.bool) (Feature f) where
  inject := fun op => .inr (.inl op)
  injective := by intro args shapes t a b h; cases h; rfl

instance (f : FieldId) : Has ValueOp (Feature f) where
  inject := fun op => .inr (.inr op)
  injective := by intro args shapes t a b h; cases h; rfl

def model (f : FieldId) : Model (Feature f) FieldVal :=
  Model.sum (fieldModel f) (Model.sum (BranchOp.model FieldVal id)
    (ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64) (fun _ => PUnit)))

def conditional {F : Signature Ty} (f : FieldId)
    [Has (FieldOp f) F] [Has (BranchOp Ty.bool) F] :
    Program F [.bool, .field f, .field f] (.field f) :=
  witgen [flag,a,b] do
    let out ← if flag then field.Mul a b else field.Add a b
    return out

def matchFallback {F : Signature Ty} (f : FieldId)
    [Has (FieldOp f) F] [Has ValueOp F] :
    Program F [.option (.field f), .field f] (.field f) :=
  witgen [input,fallback] do
    let out ← match input with
      | none => field.Neg fallback
      | some x => field.Inv x
    return out

def negative {F : Signature Ty} (f : FieldId) [Has (FieldOp f) F] :
    Program F [.field f] (.field f) :=
  witgen [x] do
    let out ← field.Neg x
    return out

def inverse {F : Signature Ty} (f : FieldId) [Has (FieldOp f) F] :
    Program F [.field f] (.field f) :=
  witgen [x] do
    let out ← field.Inv x
    return out

theorem conditional_true (f : FieldId) (a b : FieldValue f) :
    (conditional (F := Feature f) f).eval (model f) h![true,a,b] = Residue.mul a b := rfl

theorem conditional_false (f : FieldId) (a b : FieldValue f) :
    (conditional (F := Feature f) f).eval (model f) h![false,a,b] = Residue.add a b := rfl

theorem match_none (f : FieldId) (a : FieldValue f) :
    (matchFallback (F := Feature f) f).eval (model f) h![none,a] = Residue.neg a := rfl

theorem match_some (f : FieldId) (a b : FieldValue f) :
    (matchFallback (F := Feature f) f).eval (model f) h![some a,b] = Residue.inv a := rfl

open Lean Methods in
def codec (f : FieldId) : OpCodec (Feature f) := fun op => match op with
  | .inl op => fieldCodec op
  | .inr (.inl (.branch _ _)) => Json.mkObj [("op", .str "control.if"), ("static", Json.mkObj [])]
  | .inr (.inr op) => ValueOp.codec op

end Witgen.Branching
