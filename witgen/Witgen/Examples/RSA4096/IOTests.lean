import Witgen.Examples.RSA4096.IO

namespace Witgen.Examples.RSA4096
open Lean Typed

private def request (n s d : String) : Json := Json.mkObj
  [("modulus", .str n), ("signature", .str s), ("digest", .str d)]

#eval (do
  let n : Nat := 2^4095
  unless parseInputs (request (toString n) "7" "3") == .ok (n, 7, 3) do
    throw (IO.userError "fixed input decoding")
  for bad in ["0", "-1", "+1", "01", " 1", toString (2^4096 : Nat)] do
    if (parseInputs (request bad "7" "3")).toOption.isSome then
      throw (IO.userError "invalid modulus accepted")
  for bad in ["-1", "+1", "01", " 1", toString (2^4096 : Nat)] do
    if (parseInputs (request (toString n) bad "3")).toOption.isSome then
      throw (IO.userError "invalid signature accepted")
  if (parseInputs (request (toString n) "7" (toString (2^256 : Nat)))).toOption.isSome then
    throw (IO.userError "oversized digest accepted")
  let encoded := witnessJson [Residue.ofNat (modulus_pos bn254Fr) 5]
  unless encoded.getObjValAs? (Array String) "witness" == .ok #["5"] do
    throw (IO.userError "witness scalars must be decimal strings")
  : IO Unit)

end Witgen.Examples.RSA4096
