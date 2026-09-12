import Witgen.Typed.Secp
import Witgen.Typed.Public
import Witgen.Typed.Examples
import Witgen.Typed.U64Integration

open Witgen.Typed

def main (args : List String) : IO Unit := do
  let json := if args == ["nat"] then fieldProgramNatJson secpScalar
    else if args == ["u64"] then u64FieldProgramJson secpScalar
    else if args == ["affine"] then Secp.generatorRoundtripJson
    else if args == ["from-affine"] then Secp.fromAffineJson
    else if args == ["eq"] then Secp.curveEqJson
    else if args == ["msm"] then Secp.curveMSMJson
    else if args == ["msm-constructed"] then Secp.constructedMSMJson
    else if args == ["const"] then Secp.constantGeneratorJson
    else if args == ["const-identity"] then Secp.constantIdentityJson
    else Public.mixedJson
  match json with
  | .ok json => IO.println json.compress
  | .error message => throw (IO.userError message)
