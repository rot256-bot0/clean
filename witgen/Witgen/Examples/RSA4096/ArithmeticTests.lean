import Witgen.Examples.RSA4096.Arithmetic
import Lean

namespace Witgen.Examples.RSA4096.ArithmeticTests
open Witgen Witgen.Typed Lean

/-- Generic big-endian hexadecimal adapter; no RSA computation. -/
def parseHex (s : String) : Except String Nat := do
  let mut n := 0
  for c in s.toList do
    let v := c.toNat
    let d ← if 48 ≤ v && v ≤ 57 then pure (v - 48)
      else if 97 ≤ v && v ≤ 102 then pure (v - 87)
      else throw s!"invalid hexadecimal character {c}"
    n := 16 * n + d
  return n

def expect {α : Type} (x : Except String α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

def fixture : IO (Nat × Nat × Nat) := do
  let path := (← IO.getEnv "RSA_ARITHMETIC_FIXTURE").getD "tests/data/rsa4096/case-00.json"
  let j ← expect (Json.parse (← IO.FS.readFile path))
  let n ← expect ((j.getObjValAs? String "modulus") >>= parseHex)
  let s ← expect ((j.getObjValAs? String "signature") >>= parseHex)
  let d ← expect ((j.getObjValAs? String "digest") >>= parseHex)
  return (n, s, d)

def reference (source : String) : IO (Array Nat) := do
  let j ← expect (Json.parse (← IO.FS.readFile s!"{source}/reference-witness.json"))
  expect (fromJson? j)

/-- Default package tests execute the fixture without external files. Setting
    RSA_HYBRID_SOURCE additionally enforces the complete source-reviewed comparison.
    No canonicalization/reduction is applied to either side by this harness. -/
def compareCells (label : String) (start count : Nat) (cells : List (FieldValue bn254Fr)) : IO Unit := do
  let actual := (cells.map (·.val)).toArray
  unless count > 0 && actual.size == count do
    throw (IO.userError s!"{label}: wrong count actual={actual.size} required={count}")
  if let some source ← IO.getEnv "RSA_HYBRID_SOURCE" then
    let expected := (← reference source).extract start (start + count)
    unless expected.size == count do
      throw (IO.userError s!"{label}: reference slice has {expected.size} cells, expected {count}")
    for i in [:count] do
      unless actual[i]! == expected[i]! do
        throw (IO.userError s!"{label}: mismatch local={i} source={start+i}: actual={actual[i]!} expected={expected[i]!}")
    IO.println s!"{label}: exact canonical equality of {count} cells at source offset {start}"
  else
    IO.println s!"{label}: executed fixture, {count} canonical cells (external comparison not requested)"
  if let some dir ← IO.getEnv "RSA_ARITHMETIC_EVIDENCE" then
    IO.FS.createDirAll dir
    IO.FS.writeFile s!"{dir}/{label}-witness.json" (toJson actual).compress

#eval (do
  let (n, s, _) ← fixture
  let (stored, cells) := (squareWitness (F := Feature) true).eval model h![n, s]
  unless stored < 2^4096 do throw (IO.userError "first square stored output exceeds 4096 bits")
  compareCells "first-square" 73 9851 cells
  : IO Unit)

#eval (do
  let (n, s, _) ← fixture
  let (stored, _) := (squareWitness (F := Feature) true).eval model h![n, s]
  let (next, cells) := (squareWitness (F := Feature) false).eval model h![n, stored]
  unless next < 2^4096 do throw (IO.userError "middle stored output exceeds 4096 bits")
  compareCells "first-middle" 9924 9832 cells
  : IO Unit)

#eval (do
  let (n, s, _) ← fixture
  let (stored, cells) := (squaresWitness (F := Feature)).eval model h![n, s]
  unless stored < 2^4096 do throw (IO.userError "square-chain stored output exceeds 4096 bits")
  compareCells "all-squares" 73 147499 cells
  let bits := (returnedSquareBits (F := Feature)).eval model h![cells]
  let expected := (List.range 4096).map (fun i => if stored.testBit i then 1 else 0)
  unless bits.map (·.val) == expected do
    throw (IO.userError "returned residue bits differ from the full stored value")
  let a16 := (repackSquareBits (F := Feature)).eval model h![cells]
  let reconstructed := a16.foldr (fun limb acc => 65536*acc+limb.val) 0
  unless a16.length == 256 && reconstructed == stored do
    throw (IO.userError "bit-expression radix-16 repack mismatch")
  IO.println "repack: all 4096 returned bit expressions and 256 radix-16 limbs agree"
  : IO Unit)

#eval (do
  let (n, s, d) ← fixture
  let cells := (arithmeticWitness (F := Feature)).eval model h![n, s, d]
  compareCells "final-fused" 147572 12955 (cells.drop 147499)
  compareCells "arithmetic" 73 160454 cells
  : IO Unit)

#print axioms arithmeticWitness
#print axioms squareMagnitude_unsigned_model
#print axioms BigNumOp.divMod_reconstruct
#print axioms BigNumOp.divMod_remainder_lt
#print axioms FieldBridgeOp.field_nat_field
#print axioms VectorOp.tabulate_length
#print axioms VectorOp.fold_zero

end Witgen.Examples.RSA4096.ArithmeticTests
