import Witgen.Pipeline

namespace Witgen.Demo
example : (structInfo (StructOp.make (desc := schemaDesc) Schema.quad)).tag = "record.make" := rfl
example : (ListOp.empty .scalar).info.tag = "list.empty" := rfl
end Witgen.Demo

open Witgen Witgen.Demo Witgen.Arithmetic

-- Tracer 1: actual first-class record from the source AST.
example : quadraticField.eval fieldModel
    (.cons (Field17.ofNat 16) (.cons (Field17.ofNat 3) .nil)) =
    (⟨Field17.ofNat 1, Field17.ofNat 4⟩ : Quad Field17) := by decide

#check fieldToNat_correct
#check fieldToWord_correct
#check lower_commutes
#check quadraticNat_correct
#check quadraticWord_correct

example : quadraticNat.eval natModel (.cons 16 (.cons 3 .nil)) =
    (⟨1, 4⟩ : Quad Nat) := by decide

example : quadraticWord.eval wordModel (.cons 16 (.cons 3 .nil)) =
    (⟨1, 4⟩ : Quad UInt64) := by decide

-- Tracer 3: all modular-multiplication fields, including the non-output cells.
#check modMulWord_correct
#check modMulWord_small_correct
#check modMulNat_satisfies
#check modMulWord_small_satisfies
example : modMulNat.eval natModel (.cons 16 (.cons 16 (.cons 17 .nil))) =
    (⟨256, 15, 1⟩ : ModMul Nat) := by decide
example : modMulWord.eval wordModel (.cons 16 (.cons 16 (.cons 17 .nil))) =
    (⟨256, 15, 1⟩ : ModMul UInt64) := by decide

-- Tracer 4: branch → arbitrary map body → first-class record list, then fold.
#check mapToFold_correct
#check conditionalBatch_eval
example : batchQuadraticField.eval fieldModel
    (.cons [Field17.ofNat 3, Field17.ofNat 1, Field17.ofNat 4]
      (.cons (Field17.ofNat 2) .nil)) =
    ([⟨Field17.ofNat 9, Field17.ofNat 11⟩,
      ⟨Field17.ofNat 1, Field17.ofNat 3⟩,
      ⟨Field17.ofNat 16, Field17.ofNat 1⟩] : List (Quad Field17)) := by decide
example : (batchQuadraticField.lower (mapToFold FieldOp)).eval fieldModel
    (.cons [] (.cons (Field17.ofNat 2) .nil)) = ([] : List (Quad Field17)) := by decide

-- Tracer 5: inspect transformed syntax, never a model-produced pseudo-AST.
example : (nativeOps fieldInfo quadraticField).map OpInfo.tag =
    ["field.mul", "field.add", "record.make"] := by decide
example : (nativeOps natInfo quadraticNat).map OpInfo.tag =
    ["nat.mul", "nat.const", "nat.mod", "nat.add", "nat.const", "nat.mod", "record.make"] := by decide
example : (nativeOps wordInfo conditionalBatchFoldWord).any (fun i => i.tag == "control.map") = false := by decide
example : (nativeOps wordInfo conditionalBatchFoldWord).any (fun i => i.tag == "control.fold") = true := by decide
#check quadraticWord_bounded

example : Ty.recordName .quad = some "Quad" := by decide
example : Ty.recordFields .quad = [("square", .scalar), ("output", .scalar)] := by decide
example : Ty.recordFields .modmul =
    [("product", .scalar), ("quotient", .scalar), ("remainder", .scalar)] := by decide

-- Captures can be records; body returns the capture as one first-class value.
def capturedRecordMap : Program NatSig [.list .scalar, .quad] (.list .quad) :=
  .let_ (.inr (.inr (.map [.quad] .scalar .quad)))
    (.cons .zero (.cons (.succ .zero) .nil))
    (.cons (.ret (.succ .zero)) .nil) (.ret .zero)
example : (capturedRecordMap.lower (mapToFold NatOp)).eval natModel
    (.cons [3, 1, 4] (.cons (⟨7, 8⟩ : Quad Nat) .nil)) =
    ([⟨7, 8⟩, ⟨7, 8⟩, ⟨7, 8⟩] : List (Quad Nat)) := by decide

-- Nested lists and a different element/result sort require no kernel change.
def capturedListMap : Program FieldSig [.list .quad, .list .scalar] (.list (.list .scalar)) :=
  .let_ (.inr (.inr (.map [.list .scalar] .quad (.list .scalar))))
    (.cons .zero (.cons (.succ .zero) .nil))
    (.cons (.ret (.succ .zero)) .nil) (.ret .zero)
example : ((capturedListMap.lower (mapToFold FieldOp)).lower fieldToNat).eval natModel
    (.cons [⟨2, 3⟩, ⟨4, 5⟩] (.cons [7, 8] .nil)) = ([[7, 8], [7, 8]] : List (List Nat)) := by decide

-- Negative controls: arbitrary Nat addition/product do not lower exactly.
def rawNatAdd : Program NatSig [.scalar, .scalar] .scalar := emit (.inl .add) .nil
example : ((rawNatAdd.mapHandler natToWord).eval wordModel
    (.cons (UInt64.ofNat (UInt64.size - 1)) (.cons 1 .nil))).toNat ≠
    rawNatAdd.eval natModel (.cons (UInt64.size - 1) (.cons 1 .nil)) := by decide
example : (modMulWord.eval wordModel
    (.cons (UInt64.ofNat (2^32)) (.cons (UInt64.ofNat (2^32)) (.cons 17 .nil)))).product.toNat ≠
    (modMulNat.eval natModel (.cons (2^32) (.cons (2^32) (.cons 17 .nil)))).product := by decide

example : conditionalBatchFoldWord.eval wordModel
    (.cons false (.cons [3, 1, 4] (.cons 2 .nil))) = ([] : List (Quad UInt64)) := by decide
example : conditionalBatchFoldWord.eval wordModel
    (.cons true (.cons [3, 1, 4] (.cons 2 .nil))) =
    ([⟨9, 11⟩, ⟨1, 3⟩, ⟨16, 1⟩] : List (Quad UInt64)) := by decide

-- Native traversal includes the false branch's empty constructor as well.
example : (nativeOps fieldInfo conditionalBatchField).map OpInfo.tag =
    ["control.branch", "control.map", "field.mul", "field.add", "record.make", "list.empty"] := by decide
example : (nativeOps natInfo quadraticNat).filterMap OpInfo.literal = [17, 17] := by decide
example : (structInfo (StructOp.get (desc := schemaDesc) .modmul (.there .here))).field = some 1 := by decide

-- Runtime checks exercise the actual AST transformations (not foreign code).
#eval show IO Unit from do
  let mut checked := 0
  for x in List.range 17 do
    for c in List.range 17 do
      let expected := quadraticField.eval fieldModel
        (.cons (Field17.ofNat x) (.cons (Field17.ofNat c) .nil))
      let natResult := quadraticNat.eval natModel (.cons x (.cons c .nil))
      let wordResult := quadraticWord.eval wordModel
        (.cons (UInt64.ofNat x) (.cons (UInt64.ofNat c) .nil))
      unless Val.map Field17.toNat (t := .quad) expected == natResult &&
          Val.map UInt64.toNat (t := .quad) wordResult == natResult do
        throw (IO.userError s!"quadratic mismatch: {x}, {c}")
      checked := checked + 1
  IO.println s!"quadratic: {checked} Field17/Nat/UInt64 full-record checks passed"

#eval show IO Unit from do
  let mut checked := 0
  for n in List.range 18 do
    if n > 0 then
      for a in List.range n do
        for b in List.range n do
          let expected := modMulNat.eval natModel (.cons a (.cons b (.cons n .nil)))
          let actual := modMulWord.eval wordModel
            (.cons (UInt64.ofNat a) (.cons (UInt64.ofNat b) (.cons (UInt64.ofNat n) .nil)))
          unless Val.map UInt64.toNat (t := .modmul) actual == expected do
            throw (IO.userError s!"modmul mismatch: {a}, {b}, {n}")
          checked := checked + 1
  IO.println s!"modmul: {checked} Nat/UInt64 full-record checks passed"

def fieldEquality : Program FieldSig [.scalar, .scalar] .bool := emit (.inl .eq) .nil
example : (fieldEquality.lower fieldToNat).eval natModel (.cons 16 (.cons 16 .nil)) = true := by decide
example : ((fieldEquality.lower fieldToNat).mapHandler natToWord).eval wordModel
    (.cons 16 (.cons 15 .nil)) = false := by decide
example : (((emit (.inl (.const 52)) .nil : Program FieldSig [] .scalar).lower fieldToNat).mapHandler
    natToWord).eval wordModel .nil = (1 : UInt64) := by decide

#eval show IO Unit from do
  let n := 2^32
  let a := n - 1
  let expected := modMulNat.eval natModel (.cons a (.cons a (.cons n .nil)))
  let actual := modMulWord.eval wordModel
    (.cons (UInt64.ofNat a) (.cons (UInt64.ofNat a) (.cons (UInt64.ofNat n) .nil)))
  unless Val.map UInt64.toNat (t := .modmul) actual == expected do
    throw (IO.userError "modulus 2^32 boundary mismatch")
  IO.println s!"modmul boundary 2^32: {repr expected}"
  let large := modMulNat.eval natModel
    (.cons (2^256 - 1) (.cons (2^256 - 3) (.cons (2^128 + 51) .nil)))
  unless decide (MulModRel (2^256 - 1) (2^256 - 3) (2^128 + 51) large.toArithmetic) do
    throw (IO.userError "large Nat modular multiplication relation failed")
  IO.println "large Nat: 256-bit operands satisfy the full product/quotient/remainder relation"

#eval (nativeOps wordInfo conditionalBatchFoldWord).map OpInfo.tag
#print axioms fieldToNat_correct
#print axioms fieldToWord_correct
#print axioms lower_commutes
#print axioms natToWord_fieldImage_correct
#print axioms quadraticWord_bounded
#print axioms modMulWord_correct
#print axioms modMulWord_small_satisfies
#print axioms mapToFold_correct
#print axioms conditionalBatchFoldWord_correct

#eval quadraticField.eval fieldModel
  (.cons (Field17.ofNat 16) (.cons (Field17.ofNat 3) .nil))
