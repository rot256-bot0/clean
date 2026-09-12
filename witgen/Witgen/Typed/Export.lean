import Witgen.Methods
import Witgen.Typed.Field

namespace Witgen.Typed
open Lean Methods

def typeJson : Ty → Json
  | .field f => Json.mkObj [("field", toJson f.val), ("modulus", .str (toString (modulus f)))]
  | .nat => .str "nat"
  | .bool => .str "bool"
  | .u64 => .str "u64"
  | .word4 => .str "word4"
  | .point => Json.mkObj [("point", .str "secp256k1")]
  | .pair a b => Json.mkObj [("pair", .arr #[typeJson a, typeJson b])]
  | .option a => Json.mkObj [("option", typeJson a)]

def fieldCodec {f : FieldId} : OpCodec (FieldOp f) := fun op =>
  let (tag, literal) : String × List (String × Json) := match op with
    | .const n => ("field.const", [("value", .str (toString n))])
    | .add => ("field.add", [])
    | .mul => ("field.mul", [])
    | .square => ("field.square", [])
  Json.mkObj [("op", .str tag), ("static", Json.mkObj
    ([("field", toJson f.val), ("modulus", .str (toString (modulus f)))] ++ literal))]

def anyFieldCodec : OpCodec AnyFieldOp := fun (.field _ op) => fieldCodec op

end Witgen.Typed
