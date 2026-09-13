import Witgen.Typed.BigNum
import Witgen.Typed.Field
import Witgen.Typed.Values
import Witgen.Typed.Vector
import Witgen.Branching.Basic

namespace Witgen.Examples.RSA4096
open Witgen.Typed

abbrev Scalar : Ty := .field bn254Fr
abbrev Scalars : Ty := .list Scalar

/-- All arithmetic is in explicit optional capabilities; no RSA primitive or host callback. -/
inductive Feature : Signature Ty where
  | big (op : BigNumOp args shapes t) : Feature args shapes t
  | field (op : FieldOp bn254Fr args shapes t) : Feature args shapes t
  | bridge (op : FieldBridgeOp bn254Fr args shapes t) : Feature args shapes t
  | value (op : ValueOp args shapes t) : Feature args shapes t
  | vector (op : VectorOp args shapes t) : Feature args shapes t
  | branch (op : BranchOp .bool args shapes t) : Feature args shapes t

instance : Has BigNumOp Feature where
  inject := .big
  injective := by intro args shapes t a b h; cases h; rfl
instance : Has (FieldOp bn254Fr) Feature where
  inject := .field
  injective := by intro args shapes t a b h; cases h; rfl
instance : Has (FieldBridgeOp bn254Fr) Feature where
  inject := .bridge
  injective := by intro args shapes t a b h; cases h; rfl
instance : Has ValueOp Feature where
  inject := .value
  injective := by intro args shapes t a b h; cases h; rfl
instance : Has VectorOp Feature where
  inject := .vector
  injective := by intro args shapes t a b h; cases h; rfl
instance : Has (BranchOp .bool) Feature where
  inject := .branch
  injective := by intro args shapes t a b h; cases h; rfl

def model : Model Feature FieldVal where
  eval := fun op args regions => match op with
    | .big op => bigNumModel.eval op args regions
    | .field op => (fieldModel bn254Fr).eval op args regions
    | .bridge op => (fieldBridgeModel bn254Fr).eval op args regions
    | .value op => (ValueOp.model FieldValue _ (fun _ => PUnit)).eval op args regions
    | .vector op => VectorOp.model.eval op args regions
    | .branch op => (BranchOp.model FieldVal id).eval op args regions

end Witgen.Examples.RSA4096
