import Witgen.Examples.RSA4096.Basic

namespace Witgen.Examples.RSA4096
open Lean Typed

private def decimalInput (j : Json) (name : String) : Except String Nat := do
  let raw ← j.getObjValAs? String name
  let some n := raw.toNat? | throw s!"{name}: expected a natural-number decimal string"
  if toString n != raw then throw s!"{name}: expected canonical decimal encoding"
  return n

/-- Fixed ABI validation and byte-packing boundary only; no RSA or witness computation. -/
def parseInputs (j : Json) : Except String (Nat × Nat × Nat) := do
  let n ← decimalInput j "modulus"
  let s ← decimalInput j "signature"
  let d ← decimalInput j "digest"
  if n < 2^4095 || n ≥ 2^4096 then throw "modulus must have exactly 4096 bits"
  if s ≥ 2^4096 then throw "signature must fit exactly the 512-byte input layout"
  if d ≥ 2^256 then throw "digest must fit the 32-byte input layout"
  return (n, s, d)

def witnessJson (cells : List (FieldValue bn254Fr)) : Json :=
  Json.mkObj [("witness", .arr ((cells.map (fun x => Json.str (toString x.val))).toArray))]

end Witgen.Examples.RSA4096
