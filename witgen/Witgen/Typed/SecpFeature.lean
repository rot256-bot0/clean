import Witgen.Typed.SecpCurve
import Witgen.Typed.Values

namespace Witgen.Typed.Secp

abbrev Val := Value FieldValue (UInt64 × UInt64 × UInt64 × UInt64) (fun d => d.equation.Point)
def secpModel [Fact (modulus secpBase).Prime] : Model (CurveOp secp256k1) Val := Curve.model math

def fieldModel (f : FieldId) : Model (FieldOp f) Val where
  eval := fun op args _ => match op, args with
    | .const n, .nil => Residue.ofNat (modulus_pos f) n
    | .add, .cons a (.cons b .nil) => Residue.add a b
    | .mul, .cons a (.cons b .nil) => Residue.mul a b
    | .square, .cons a .nil => Residue.square a
    | .neg, .cons a .nil => Residue.neg a
    | .inv, .cons a .nil => Residue.inv a

def fieldsModel : Model AnyFieldOp Val where
  eval := fun (.field f op) args bodies => (fieldModel f).eval op args bodies

abbrev Feature := SigSum AnyFieldOp (CurveOp secp256k1)
instance (f : FieldId) : Has (FieldOp f) Feature where
  inject := fun op => .inl (.field f op)
  injective := by intro args shapes t a b h; cases h; rfl

def model [Fact (modulus secpBase).Prime] : Model Feature Val := fieldsModel.sum secpModel

open Lean Methods in
def codec : OpCodec Feature := fun op => match op with
  | .inl op => anyFieldCodec op
  | .inr op => Curve.codec op

abbrev MixedFeature := SigSum ValueOp Feature
instance : Has (CurveOp secp256k1) MixedFeature where
  inject := fun op => .inr (.inr op)
  injective := by intro args shapes t a b h; cases h; rfl

instance (f : FieldId) : Has (FieldOp f) MixedFeature where
  inject := fun op => .inr (.inl (.field f op))
  injective := by intro args shapes t a b h; cases h; rfl

def mixedModel [Fact (modulus secpBase).Prime] : Model MixedFeature Val :=
  (ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64) (fun d => d.equation.Point)).sum model

open Lean Methods in
def mixedCodec : OpCodec MixedFeature := fun op => match op with
  | .inl op => ValueOp.codec op
  | .inr op => codec op

end Witgen.Typed.Secp
