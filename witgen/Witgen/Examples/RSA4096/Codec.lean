import Witgen.Examples.RSA4096.Basic

namespace Witgen.Examples.RSA4096
open Lean Typed Methods

/-- Serialized operation tags and literal data, separate from executable semantics. -/
def codec : OpCodec Feature := fun feature => match feature with
  | .field op => fieldCodec op
  | .value op => ValueOp.codec op
  | .vector op => VectorOp.codec op
  | .branch (.branch _ _) => Json.mkObj [("op", .str "control.if"), ("static", Json.mkObj [])]
  | .bridge op =>
      let tag := match op with
        | .natToField => "field.from_nat"
        | .fieldToNat => "field.to_nat"
      Json.mkObj [("op", .str tag), ("static", fieldJson bn254Fr)]
  | .big op =>
      let (tag, extra) : String × List (String × Json) := match op with
        | .const n => ("bignum.const", [("value", .str (toString n))])
        | .add => ("bignum.add", [])
        | .sub => ("bignum.sub", [])
        | .mul => ("bignum.mul", [])
        | .square => ("bignum.square", [])
        | .divMod => ("bignum.divmod", [])
        | .lt => ("bignum.lt", [])
        | .bit index => ("bignum.bit", [("index", toJson index)])
        | .shl amount => ("bignum.shl", [("amount", toJson amount)])
        | .shr amount => ("bignum.shr", [("amount", toJson amount)])
        | .shrBy => ("bignum.shr_by", [])
      Json.mkObj [("op", .str tag), ("static", Json.mkObj extra)]

end Witgen.Examples.RSA4096
