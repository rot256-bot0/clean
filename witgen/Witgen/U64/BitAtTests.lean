import Witgen.U64.Export

namespace Witgen.U64.BitAtTests
open Witgen.Typed Witgen.Methods Lean

-- Retain the original bounded statement, not a weakened arithmetic contract.
example (a : Word4) (i : Nat) (hi : i < 256) :
    a.bitAt i = a.decode.testBit i := Word4.bitAt_correct a hi

example (a : Word4) (i : Nat) (hi : 256 ≤ i) :
    a.bitAt i = false := Word4.bitAt_out_of_range a hi

example : (Word4.mk 0 0 0 1).bitAt 256 = false := by decide
example : (Word4.mk 0 0 0 2).bitAt 257 = false := by decide

/-- Real finite IR exports, including the reviewer's exact repeat257 body.
The second body also reaches index257; neither is a field-library replacement. -/
def exportControls : IO Json := do
  let p := Word4.encode (2^256-1)
  let b := Word4.encode 1
  let mut programs := #[]
  let mut cases := #[]
  for n in [257,258] do
    let name := "bit-domain-" ++ toString n
    let module ← match moduleJson typeJson codec addLibrary name ["p","a","b"] (mulBodyN n) with
      | .ok m => pure m
      | .error e => throw (IO.userError e)
    programs := programs.push module
    for a in [Word4.mk 0 0 0 1, Word4.mk 0 0 0 2, Word4.mk 0 0 0 3] do
      let actual := (mulBodyN n).eval (addLibrary.model primitive) h![p,a,b]
      cases := cases.push (Json.mkObj [("program", .str name),
        ("inputs", .arr #[wordJson p, wordJson a, wordJson b]),
        ("actual", wordJson actual), ("expected", wordJson a)])
  let indices := [0,63,64,127,128,191,192,193,255,256,257,319,320,2^64]
  let bitCases := ([Word4.mk 0 0 0 1, Word4.mk 0 0 0 2,
      Word4.encode (2^256-1)] : List Word4).flatMap fun a => indices.map fun i =>
    Json.mkObj [("word", wordJson a), ("index", .str (toString i)),
      ("actual", .bool (a.bitAt i)), ("expected", .bool (a.decode.testBit i))]
  return Json.mkObj [("programs", .arr programs), ("cases", .arr cases),
    ("bit_cases", toJson bitCases)]

end Witgen.U64.BitAtTests

def main : IO Unit := do
  IO.println (← Witgen.U64.BitAtTests.exportControls).compress
