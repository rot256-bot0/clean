import Witgen.Typed.SecpCurve
import Witgen.Typed.Export

namespace Witgen.Typed

inductive SecpOp : Signature Ty where
  | add : SecpOp [.point, .point] [] .point
  | scale : SecpOp [.field secpScalar, .point] [] .point
  | inv : SecpOp [.point] [] .point
  | generator : SecpOp [] [] .point
  | identity : SecpOp [] [] .point
  | x : SecpOp [.point] [] (.field secpBase)
  | toAffine : SecpOp [.point] [] (.option (.pair (.field secpBase) (.field secpBase)))
  | fromAffine : SecpOp [.pair (.field secpBase) (.field secpBase)] [] (.option .point)

namespace Secp

abbrev Val := Value FieldValue (UInt64 × UInt64 × UInt64 × UInt64) Point

def secpModel [Fact (modulus secpBase).Prime] : Model SecpOp Val where
  eval := fun op args _ => match op, args with
    | .add, .cons p (.cons q .nil) => p + q
    | .scale, .cons s (.cons p .nil) => scale s p
    | .inv, .cons p .nil => -p
    | .generator, .nil => generator
    | .identity, .nil => 0
    | .x, .cons p .nil => xCoord p
    | .toAffine, .cons p .nil => toAffine p
    | .fromAffine, .cons xy .nil => fromAffine xy

def fieldModel (f : FieldId) : Model (FieldOp f) Val where
  eval := fun op args _ => match op, args with
    | .const n, .nil => Residue.ofNat (modulus_pos f) n
    | .add, .cons a (.cons b .nil) => Residue.add a b
    | .mul, .cons a (.cons b .nil) => Residue.mul a b
    | .square, .cons a .nil => Residue.square a

def fieldsModel : Model AnyFieldOp Val where
  eval := fun (.field f op) args bodies => (fieldModel f).eval op args bodies

abbrev Feature := SigSum AnyFieldOp SecpOp

instance (f : FieldId) : Has (FieldOp f) Feature where
  inject := fun op => .inl (.field f op)
  injective := by intro args shapes t a b h; cases h; rfl

def model [Fact (modulus secpBase).Prime] : Model Feature Val := fieldsModel.sum secpModel

open Lean Methods in
def codec : OpCodec Feature := fun op => match op with
  | .inl op => anyFieldCodec op
  | .inr op =>
    let tag := match op with
      | .add => "secp.add"
      | .scale => "secp.scale"
      | .inv => "secp.inv"
      | .generator => "secp.generator"
      | .identity => "secp.identity"
      | .x => "secp.x"
      | .toAffine => "curve.toAffine"
      | .fromAffine => "curve.fromAffine"
    Json.mkObj [("op", .str tag), ("static", Json.mkObj [("curve", .str "secp256k1")])]

end Secp
end Witgen.Typed

namespace Witgen.secp
open Typed
variable {F : Signature Ty} {Γ : List Ty} [Has SecpOp F]

def Add (p q : Var Γ .point) : Step F Γ .point := call SecpOp.add h![p, q] .nil
def Scale (s : Var Γ (.field secpScalar)) (p : Var Γ .point) : Step F Γ .point :=
  call SecpOp.scale h![s, p] .nil
def Inv (p : Var Γ .point) : Step F Γ .point := call SecpOp.inv h![p] .nil
def Generator : Step F Γ .point := call SecpOp.generator .nil .nil
def Identity : Step F Γ .point := call SecpOp.identity .nil .nil
def X (p : Var Γ .point) : Step F Γ (.field secpBase) := call SecpOp.x h![p] .nil

end Witgen.secp

namespace Witgen.curve
open Typed
variable {F : Signature Ty} {Γ : List Ty} [Has SecpOp F]
def ToAffine (p : Var Γ .point) :
    Step F Γ (.option (.pair (.field secpBase) (.field secpBase))) :=
  call SecpOp.toAffine h![p] .nil
def FromAffine (xy : Var Γ (.pair (.field secpBase) (.field secpBase))) :
    Step F Γ (.option .point) := call SecpOp.fromAffine h![xy] .nil
end Witgen.curve
