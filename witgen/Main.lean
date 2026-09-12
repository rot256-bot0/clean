import Witgen.Export
import Witgen.Integration
import Witgen.Batch

set_option autoImplicit false

open Lean Witgen Witgen.Demo

namespace Driver

def quadLayout : Json :=
  Json.mkObj [("field", toJson (17 : Nat)), ("cells", toJson Circuits.Quadratic.Slots.layout.length),
    ("input_slots", toJson [Circuits.Quadratic.Slots.x, Circuits.Quadratic.Slots.y]),
    ("outputs", .arr #[
      Json.mkObj [("path", toJson (["square"] : List String)),
        ("slot", toJson Circuits.Quadratic.Slots.square)],
      Json.mkObj [("path", toJson (["output"] : List String)),
        ("slot", toJson Circuits.Quadratic.Slots.output)]])]

def jsonOrError (result : Except String Json) : IO Json :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def modMulLayout : Json :=
  Json.mkObj [("field", toJson (257 : Nat)), ("cells", toJson Circuits.ModMul.Slots.layout.length),
    ("policy", .str "modmul_small"),
    ("input_slots", toJson [Circuits.ModMul.Slots.a, Circuits.ModMul.Slots.b, Circuits.ModMul.Slots.n]),
    ("outputs", .arr #[
      Json.mkObj [("path", toJson (["product"] : List String)), ("slot", toJson Circuits.ModMul.Slots.product)],
      Json.mkObj [("path", toJson (["quotient"] : List String)), ("slot", toJson Circuits.ModMul.Slots.quotient)],
      Json.mkObj [("path", toJson (["remainder"] : List String)), ("slot", toJson Circuits.ModMul.Slots.remainder)]])]

def batchOutput (index : Nat) (field : String) (slot : Nat) : Json :=
  Json.mkObj [("path", .arr #[toJson index, .str field]), ("slot", toJson slot)]

def batchLayout : Json :=
  Json.mkObj [("field", toJson (17 : Nat)), ("cells", toJson Batch.Slots.layout.length),
    ("policy", .str "batch3"), ("output_length", toJson Batch.Slots.recordStarts.length),
    ("input_bindings", .arr #[
      Json.mkObj [("slot", toJson Batch.Slots.enabled)],
      Json.mkObj [("slots", toJson [Batch.Slots.x0, Batch.Slots.x1, Batch.Slots.x2])],
      Json.mkObj [("slot", toJson Batch.Slots.c)]]),
    ("outputs", .arr #[
      batchOutput 0 "square" Batch.Slots.square0, batchOutput 0 "output" Batch.Slots.out0,
      batchOutput 1 "square" Batch.Slots.square1, batchOutput 1 "output" Batch.Slots.out1,
      batchOutput 2 "square" Batch.Slots.square2, batchOutput 2 "output" Batch.Slots.out2])]

def modules : List (String × Except String Json) :=
  [("quadratic_field", Export.moduleJson fieldInfo "generate" "field17"
      ["x", "y"] Integration.quadraticFieldWitgen.program (some quadLayout) "field17"),
   ("quadratic_nat", Export.moduleJson natInfo "generate" "nat"
      ["x", "y"] Integration.quadraticNatWitgen.program (some quadLayout) "field17"),
   ("quadratic_word", Export.moduleJson wordInfo "generate" "word"
      ["x", "y"] Integration.quadraticWordWitgen.program (some quadLayout) "field17"),
   ("modmul_nat", Export.moduleJson natInfo "generate" "nat"
      ["a", "b", "modulus"] Integration.modMulNatWitgen.program (some modMulLayout)),
   ("modmul_word", Export.moduleJson wordInfo "generate" "word"
      ["a", "b", "modulus"] Integration.modMulWordWitgen.program (some modMulLayout)),
   ("modmul_nat_raw", Export.moduleJson natInfo "generate" "nat"
      ["a", "b", "modulus"] modMulNat),
   ("conditional_field", Export.moduleJson fieldInfo "generate" "field17"
      ["enabled", "xs", "offset"] conditionalBatchField none "field17"),
   ("conditional_nat", Export.moduleJson natInfo "generate" "nat"
      ["enabled", "xs", "offset"] conditionalBatchNat none "field17"),
   ("conditional_word", Export.moduleJson wordInfo "generate" "word"
      ["enabled", "xs", "offset"] conditionalBatchWord none "field17"),
   ("conditional_fold_field", Export.moduleJson fieldInfo "generate" "field17"
      ["enabled", "xs", "offset"] conditionalBatchFoldField none "field17"),
   ("conditional_fold_nat", Export.moduleJson natInfo "generate" "nat"
      ["enabled", "xs", "offset"] conditionalBatchFoldNat none "field17"),
   ("conditional_fold_word", Export.moduleJson wordInfo "generate" "word"
      ["enabled", "xs", "offset"] conditionalBatchFoldWord none "field17"),
   ("batch_field", Export.moduleJson fieldInfo "generate" "field17"
      ["enabled", "xs", "c"] Batch.sourceWitgen.program (some batchLayout) "field17"),
   ("batch_nat", Export.moduleJson natInfo "generate" "nat"
      ["enabled", "xs", "c"] Batch.natWitgen.program (some batchLayout) "field17"),
   ("batch_word", Export.moduleJson wordInfo "generate" "word"
      ["enabled", "xs", "c"] Batch.wordWitgen.program (some batchLayout) "field17"),
   ("batch_fold_field", Export.moduleJson fieldInfo "generate" "field17"
      ["enabled", "xs", "c"] Batch.foldFieldWitgen.program (some batchLayout) "field17"),
   ("batch_fold_nat", Export.moduleJson natInfo "generate" "nat"
      ["enabled", "xs", "c"] Batch.foldNatWitgen.program (some batchLayout) "field17"),
   ("batch_fold_word", Export.moduleJson wordInfo "generate" "word"
      ["enabled", "xs", "c"] Batch.foldWordWitgen.program (some batchLayout) "field17")]

def exportAll (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for (name, result) in modules do
    let source ← jsonOrError result
    IO.FS.writeFile (directory / (name ++ ".json")) source.pretty
  IO.FS.writeFile (directory / "manifest.json")
    (Json.mkObj [("programs", toJson (modules.map Prod.fst))]).pretty
  IO.println (Json.mkObj [("exported", toJson modules.length)]).compress

def fixture (program : String) (inputs : List Json) (expected : Json) : Json :=
  Json.mkObj [("program", .str program), ("inputs", .arr inputs.toArray), ("expected", expected)]

def natJson (n : Nat) : Json := .str (toString n)
def fieldJson (n : Arithmetic.Field17) : Json := natJson n.toNat
def wordJson (n : UInt64) : Json := natJson n.toNat

def fixtures (path : System.FilePath) : IO Unit := do
  let mut cases : Array Json := #[]
  for x in List.range 17 do
    for y in List.range 17 do
      let i : Circuits.Quadratic.Input := ⟨Arithmetic.Field17.ofNat x, Arithmetic.Field17.ofNat y⟩
      let witnesses : List (String × Circuits.Quadratic.Witness) :=
        [("quadratic_field", Integration.quadraticFieldWitgen.generate i),
         ("quadratic_nat", Integration.quadraticNatWitgen.generate i),
         ("quadratic_word", Integration.quadraticWordWitgen.generate i)]
      for (name, witness) in witnesses do
        let buffer := Circuits.Quadratic.populate (Circuits.Quadratic.initial i) witness
        cases := cases.push (fixture name [natJson x, natJson y]
          (Json.mkObj [("cells", toJson buffer.toArray)]))
  for n0 in List.range 16 do
    let n := n0 + 1
    for a in List.range n do
      for b in List.range n do
        let i : Circuits.ModMul.Input := ⟨a, b, n⟩
        let witnesses : List (String × Circuits.ModMul.Witness) :=
          [("modmul_nat", Integration.modMulNatWitgen.generate i),
           ("modmul_word", Integration.modMulWordWitgen.generate i)]
        for (name, witness) in witnesses do
          let buffer := Circuits.ModMul.populate (Circuits.ModMul.initial i) witness
          cases := cases.push (fixture name [natJson a, natJson b, natJson n]
            (Json.mkObj [("cells", toJson buffer.toArray)]))
  for values in ([[], [0], [3, 1, 4], [16, 0, 15]] : List (List Nat)) do
    for enabled in [false, true] do
      for offset in [0, 2, 16] do
        let fe : HList (Val Arithmetic.Field17) [.bool, .list .scalar, .scalar] :=
          .cons enabled (.cons (values.map Arithmetic.Field17.ofNat)
            (.cons (Arithmetic.Field17.ofNat offset) .nil))
        let ne : HList (Val Nat) [.bool, .list .scalar, .scalar] :=
          .cons enabled (.cons values (.cons offset .nil))
        let we : HList (Val UInt64) [.bool, .list .scalar, .scalar] :=
          .cons enabled (.cons (values.map UInt64.ofNat) (.cons (UInt64.ofNat offset) .nil))
        let runs : List (String × Json) :=
          [("conditional_field", Export.valueJson fieldJson _ (conditionalBatchField.eval fieldModel fe)),
           ("conditional_nat", Export.valueJson natJson _ (conditionalBatchNat.eval natModel ne)),
           ("conditional_word", Export.valueJson wordJson _ (conditionalBatchWord.eval wordModel we)),
           ("conditional_fold_field", Export.valueJson fieldJson _ (conditionalBatchFoldField.eval fieldModel fe)),
           ("conditional_fold_nat", Export.valueJson natJson _ (conditionalBatchFoldNat.eval natModel ne)),
           ("conditional_fold_word", Export.valueJson wordJson _ (conditionalBatchFoldWord.eval wordModel we))]
        for (name, value) in runs do
          cases := cases.push (fixture name [toJson enabled, toJson (values.map toString), natJson offset]
            (Json.mkObj [("value", value)]))
  for enabled in [false, true] do
    for x in List.range 17 do
      for offset in List.range 17 do
        let i : Batch.Input := ⟨enabled, Arithmetic.Field17.ofNat x,
          Arithmetic.Field17.ofNat (x + 1), Arithmetic.Field17.ofNat 16,
          Arithmetic.Field17.ofNat offset⟩
        let witnesses : List (String × Option Batch.Witness) :=
          [("batch_field", Batch.sourceWitgen.generate i),
           ("batch_nat", Batch.natWitgen.generate i),
           ("batch_word", Batch.wordWitgen.generate i),
           ("batch_fold_field", Batch.foldFieldWitgen.generate i),
           ("batch_fold_nat", Batch.foldNatWitgen.generate i),
           ("batch_fold_word", Batch.foldWordWitgen.generate i)]
        for (name, witness) in witnesses do
          match Batch.populateDecoded (Batch.initial i) witness with
          | none => throw (IO.userError ("invalid typed batch witness shape: " ++ name))
          | some buffer =>
            cases := cases.push (fixture name
              [toJson enabled, toJson ([i.x0.toNat, i.x1.toNat, i.x2.toNat].map toString), natJson offset]
              (Json.mkObj [("cells", toJson buffer.toArray)]))
  let modulus : Nat := 2 ^ 4096 - 1
  let a := modulus - 123
  let b := modulus - 456
  let raw := modMulNat.eval natModel (.cons a (.cons b (.cons modulus .nil)))
  cases := cases.push (fixture "modmul_nat_raw" [natJson a, natJson b, natJson modulus]
    (Json.mkObj [("value", Export.valueJson natJson .modmul raw)]))
  IO.FS.writeFile path (Json.arr cases).compress
  IO.println (Json.mkObj [("fixtures", toJson cases.size)]).compress

def demo : IO Unit := do
  let input : Circuits.Quadratic.Input := ⟨3, 4⟩
  let witness := Integration.quadraticFieldWitgen.generate input
  let buffer := Circuits.Quadratic.populate (Circuits.Quadratic.initial input) witness
  IO.println (toJson buffer.toArray).compress

end Driver

def main (args : List String) : IO UInt32 := do
  match args with
  | ["export", directory] => Driver.exportAll directory; return 0
  | ["demo"] => Driver.demo; return 0
  | ["fixtures", path] => Driver.fixtures path; return 0
  | _ =>
    IO.eprintln "usage: witgen export DIR | witgen fixtures FILE | witgen demo"
    return 1
