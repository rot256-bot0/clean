import Witgen.Methods
import Witgen.Typed.Field

namespace Witgen.Typed
open Lean Methods

def fieldJson (f : FieldId) : Json :=
  Json.mkObj [("field", toJson f.val), ("modulus", .str (toString (modulus f)))]

def curveJson (c : CurveId) : Json :=
  Json.mkObj [("id", .str c.name), ("base", fieldJson c.base), ("scalar", fieldJson c.scalar),
    ("weierstrass", .arr (#[c.a1,c.a2,c.a3,c.a4,c.a6].map (fun a => .str (toString a.val))))]

def typeJson : Ty → Json
  | .field f => Json.mkObj [("field", toJson f.val), ("modulus", .str (toString (modulus f)))]
  | .nat => .str "nat"
  | .bool => .str "bool"
  | .u64 => .str "u64"
  | .word4 => .str "word4"
  | .point c => Json.mkObj [("point", curveJson c)]
  | .pair a b => Json.mkObj [("pair", .arr #[typeJson a, typeJson b])]
  | .option a => Json.mkObj [("option", typeJson a)]
  | .list a => Json.mkObj [("list", typeJson a)]

def fieldCodec {f : FieldId} : OpCodec (FieldOp f) := fun op =>
  let (tag, literal) : String × List (String × Json) := match op with
    | .const n => ("field.const", [("value", .str (toString n))])
    | .add => ("field.add", [])
    | .sub => ("field.sub", [])
    | .mul => ("field.mul", [])
    | .square => ("field.square", [])
    | .neg => ("field.neg", [])
    | .inv => ("field.inv", [])
    | .sqrt => ("field.sqrt", [])
  Json.mkObj [("op", .str tag), ("static", Json.mkObj
    ([("field", toJson f.val), ("modulus", .str (toString (modulus f)))] ++ literal))]

def anyFieldCodec : OpCodec AnyFieldOp := fun (.field _ op) => fieldCodec op

end Witgen.Typed
