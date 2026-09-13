import Witgen.Examples.RSA4096.Compare

namespace Witgen.Examples.RSA4096.CompareTests
open Witgen.Typed

/- First vertical slice: full-width big-endian chunks, with 28 zero padding bytes. -/
#eval (do
  let n := (2^4095 : Nat) + 0x123456789abc
  let actual := (Compare.chunks (F := Feature)).eval model h![n]
  let expected := (List.replicate 4 0) ++ [0x8000] ++
    (List.replicate 84 0) ++ [0x123456789abc]
  unless actual == expected do
    throw <| IO.userError "90 big-endian chunks do not match 512-byte ABI"
  IO.println "PASS full-width 90-chunk adapter"
  : IO Unit)

/- Second vertical slice: the bounded scan must retain the earliest mismatch. -/
#eval (do
  let chunker := Compare.chunks (F := Feature)
  let scanner := Compare.firstDifference (F := Feature)
  for k in List.range 86 do
    let first := k + 4
    let n := (2^4095 : Nat)
    let s := n + 2^(48*(89-first)) + 1
    let actual := scanner.eval model h![chunker.eval model h![n], chunker.eval model h![s]]
    unless actual == first do
      throw <| IO.userError s!"first difference: expected {first}, got {actual}"
  for n in [(0 : Nat), 2^4095 + 123] do
    let cs := chunker.eval model h![n]
    unless scanner.eval model h![cs, cs] == 90 do
      throw <| IO.userError "equal-input sentinel must be 90"
  IO.println "PASS scan: 86 first-chunk positions and zero/nonzero equality"
  : IO Unit)

/- Equality is not success: only delta/extraction fall back to zero. The original
product cells are [1, -1, 1], and the resulting comparator relation rejects it. -/
#eval (do
  let expected := List.replicate 17 1 ++ [0] ++ List.replicate 5 0 ++
    [1, modulus bn254Fr - 1, 1] ++ List.replicate 47 0
  for n in [(0 : Nat), 2^4095 + 123] do
    let actual := ((comparatorWitness (F := Feature)).eval model h![n, n]).map Fin.val
    unless actual == expected do
      throw <| IO.userError "equal-input fallback must match all 73 source cells"
  IO.println "PASS complete 73-cell zero/nonzero equality fallback"
  : IO Unit)

#print axioms comparatorWitness

private def jsonOrFail (x : Except String α) : IO α :=
  match x with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

private def decimal (j : Lean.Json) (key : String) : IO Nat := do
  let raw ← jsonOrFail (j.getObjValAs? String key)
  match raw.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"invalid decimal {key}"

/-- Execute the real finite AST, checking every canonical field cell, not a digest. -/
def checkCases (input output : System.FilePath) : IO Unit := do
  let json ← jsonOrFail <| Lean.Json.parse (← IO.FS.readFile input)
  let cases ← jsonOrFail json.getArr?
  let mut results : Array Lean.Json := #[]
  for test in cases do
    let name ← jsonOrFail (test.getObjValAs? String "name")
    let n ← decimal test "modulus"
    let s ← decimal test "signature"
    unless n < 2^4096 && s < 2^4096 do
      throw <| IO.userError s!"{name}: input exceeds the 512-byte ABI"
    let expected ← jsonOrFail (test.getObjValAs? (Array String) "cells")
    let actual := ((comparatorWitness (F := Feature)).eval model h![n, s]).map Fin.val
    unless actual.length == 73 && expected.size == 73 do
      throw <| IO.userError s!"{name}: expected exactly 73 cells, got {actual.length}"
    for (cell, i) in actual.zipIdx do
      unless toString cell == expected[i]! do
        throw <| IO.userError s!"{name}: cell {i}: {cell} != {expected[i]!}"
    results := results.push <| Lean.Json.mkObj [
      ("name", .str name), ("cells", Lean.toJson (actual.map toString))]
  IO.FS.writeFile output ((Lean.Json.arr results).compress ++ "\n")
  IO.println s!"PASS {cases.size} comparator cases; every one of 73 cells matched"

end Witgen.Examples.RSA4096.CompareTests

/-- `lake env lean --run .../CompareTests.lean oracle-cases.json actual.json` -/
def main (args : List String) : IO Unit := do
  match args with
  | [input, output] => Witgen.Examples.RSA4096.CompareTests.checkCases input output
  | _ => throw <| IO.userError "expected oracle-cases.json and output.json paths"
