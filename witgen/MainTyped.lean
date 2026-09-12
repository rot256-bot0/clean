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
    else Public.mixedJson
  match json with
  | .ok json => IO.println json.compress
  | .error message => throw (IO.userError message)
