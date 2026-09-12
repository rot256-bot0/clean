import Witgen.Batch

#check Witgen.Batch.buffer_layout
#check Witgen.Batch.result_layout_size

open Witgen Witgen.Demo Witgen.Arithmetic Witgen.Batch

-- Tracer 1: real per-element branch keeps the complete three-record shape.
def enabledInput : Input := ⟨true, 3, 4, 16, 4⟩
def disabledInput : Input := ⟨false, 3, 4, 16, 4⟩

example : Val.map Field17.toNat (t := .list .quad)
    (gatedBatchField.eval fieldModel (encodeField enabledInput)) =
    [⟨9, 13⟩, ⟨16, 3⟩, ⟨1, 5⟩] := by decide

example : Val.map Field17.toNat (t := .list .quad)
    (gatedBatchField.eval fieldModel (encodeField disabledInput)) =
    [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩] := by decide

example (i : Input) : (gatedBatchField.eval fieldModel (encodeField i)).length = 3 :=
  gatedBatchField_length i

example : (nativeOps fieldInfo gatedBatchField).map OpInfo.tag =
    ["control.map", "control.branch", "field.mul", "field.add", "record.make",
      "field.const", "record.make"] := by decide

set_option autoImplicit false

-- Tracer 2: actual transforms preserve every native record field.
example (i : Input) : gatedBatchFoldField.eval fieldModel (encodeField i) =
    gatedBatchField.eval fieldModel (encodeField i) := gatedBatchFoldField_correct i
example (i : Input) : gatedBatchNat.eval natModel (encodeNat i) =
    Val.map Field17.toNat (t := .list .quad) (expectedRecords i) := gatedBatchNat_correct i
example (i : Input) : Val.map UInt64.toNat (t := .list .quad)
    (gatedBatchWord.eval wordModel (encodeWord i)) =
    gatedBatchNat.eval natModel (encodeNat i) := gatedBatchWord_correct i
example (i : Input) : Val.map UInt64.toNat (t := .list .quad)
    (gatedBatchFoldWord.eval wordModel (encodeWord i)) =
    Val.map Field17.toNat (t := .list .quad) (expectedRecords i) :=
  gatedBatchFoldWord_correct i
example : ((nativeOps wordInfo gatedBatchFoldWord).map OpInfo.tag).contains "control.map" =
    false := by decide
example : ((nativeOps wordInfo gatedBatchFoldWord).map OpInfo.tag).contains "control.fold" =
    true := by decide
example : ((nativeOps wordInfo gatedBatchFoldWord).map OpInfo.tag).contains "control.branch" =
    true := by decide

-- Tracer 3: checked, full-record decoders and actual certificates.
example : decodeNat [] = none := rfl
example : decodeNat [⟨0,0⟩, ⟨0,0⟩] = none := rfl
example : decodeNat [⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩] = none := rfl
example (i : Input) : ¬ Relation i none := none_rejected i
example (i : Input) : Relation i (sourceWitgen.generate i) := sourceWitgen.satisfies i trivial
example (i : Input) : Relation i (foldWordWitgen.generate i) := foldWordWitgen.satisfies i trivial
example (i : Input) : foldWordWitgen.generate i = sourceWitgen.generate i :=
  foldWord_generate_eq_source i
example : Circuits.CompleteOver circuit wordModel (t := .list .quad) encodeWord decodeWord :=
  word_completeOver
example (xs : List (Quad Nat)) (h : xs.length ≠ 3) : decodeNat xs = none :=
  decodeNat_wrong_length xs h
example (xs : List (Quad Nat)) (w : Witness) (h : decodeNat xs = some w) :
    xs = [w.q0, w.q1, w.q2] := decodeNat_complete_records xs w h

-- Tracer 4: the whole 11-cell witness ABI, including disabled writes.
example : Slots.layout = [0,1,2,3,4,5,6,7,8,9,10] := rfl
example : Slots.layout.Nodup := Slots.noAliases
example (k : Fin 11) : k.val ∈ Slots.layout := Slots.covers k
example (b : Buffer) (w : Witness) : WitnessCells (populate b w) w :=
  populate_witnessCells b w
example (b : Buffer) (w : Witness) (k : Fin 5) :
    (populate b w)[k.val] = b[k.val] := populate_inputs_unchanged b w k
example (i : Input) : Constraints i (populate (initial i) (expectedWitness i)) :=
  honest_buffer i
example : populateDecoded (initial enabledInput) (sourceWitgen.generate enabledInput) =
    some ⟨#[1,3,4,16,4,9,13,16,3,1,5], rfl⟩ := by decide
example : populateDecoded (initial disabledInput) (foldWordWitgen.generate disabledInput) =
    some ⟨#[0,3,4,16,4,0,0,0,0,0,0], rfl⟩ := by decide
example (b : Buffer) : populateDecoded b none = none := rfl
example (i : Input) (b : Buffer) (h : i.enabled = false) (k : Fin 6) :
    (populate b (expectedWitness i))[k.val + 5] = 0 := disabled_populates_all i b h k
example : ¬ Constraints enabledInput ⟨#[1,3,4,16,4,0,13,16,3,1,5], rfl⟩ :=
  missing_square_rejected
example : ¬ Constraints disabledInput ⟨#[0,3,4,16,4,9,0,0,0,0,0], rfl⟩ :=
  disabled_stale_cell_rejected

-- Tracer 5: accepting buffers and arbitrary certified generators.
example (i : Input) (b : Buffer) : Constraints i b ↔
    Inputs i b ∧ ∃ w, WitnessCells b w ∧ RecordsRelation i w := constraints_iff i b
example (i : Input) (b : Buffer) (h : Constraints i b) :
    Spec i (some [b[6], b[8], b[10]]) := constraints_sound i b h
example (i : Input) (b : Buffer) (h : Constraints i b) (k : Fin 11) :
    b[k.val] < 17 := constraints_canonical i b h k
example (i : Input) : ∃ w b, foldWordWitgen.generate i = some w ∧
    populateDecoded (initial i) (foldWordWitgen.generate i) = some b ∧
    WitnessCells b w ∧ Inputs i b ∧ Constraints i b := certified_buffer foldWordWitgen i
example (xs : List (Quad UInt64)) (h : xs.length ≠ 3) : decodeWord xs = none :=
  decodeWord_wrong_length xs h
example (xs : List (Quad Field17)) (h : xs.length ≠ 3) : decodeField xs = none :=
  decodeField_wrong_length xs h
example (i : Input) : (gatedBatchFoldWord.eval wordModel (encodeWord i)).length = 3 :=
  native_record_shape i |>.2.2.2.2.2

-- The existing empty-disabled demo cannot masquerade as a circuit generator.
example : ¬ Relation disabledInput
    (decodeField (conditionalBatchField.eval fieldModel (encodeField disabledInput))) := by decide
example : ¬ Constraints enabledInput ⟨#[1,3,4,16,4,26,13,16,3,1,5], rfl⟩ := by decide
example : ¬ Constraints enabledInput ⟨#[1,3,4,16,4,13,9,16,3,1,5], rfl⟩ := by decide
example : ¬ Constraints enabledInput ⟨#[0,3,4,16,4,9,13,16,3,1,5], rfl⟩ := by decide
example : Ty.recordName .quad = some "Quad" := rfl
example : Ty.recordFields .quad = [("square", .scalar), ("output", .scalar)] := rfl
example : foldWordWitgen.program = gatedBatchFoldWord := rfl
example : wordWitgen.program = gatedBatchNat.mapHandler natToWord := rfl
example : foldNatWitgen.program = gatedBatchFoldField.lower fieldToNat := rfl

-- Bounded executable regression: every scalar x/c pair, both branches, all six ASTs.
-- This is not an exhaustive enumeration of the five-field Input type.
#eval do
  let mut inputs := 0
  let mut stages := 0
  for enabled in [false, true] do
    for x in List.range 17 do
      for c in List.range 17 do
        let x1 := (x + 1) % 17
        let i : Input := ⟨enabled, Field17.ofNat x, Field17.ofNat x1, 16, Field17.ofNat c⟩
        let row := fun x : Nat =>
          if enabled then (⟨x*x%17, (x*x%17+c)%17⟩ : Quad Nat) else ⟨0,0⟩
        let expected : Witness := ⟨row x, row x1, row 16⟩
        let results : List (String × Option Witness) :=
          [("field", sourceWitgen.generate i), ("fold-field", foldFieldWitgen.generate i),
           ("nat", natWitgen.generate i), ("word", wordWitgen.generate i),
           ("fold-nat", foldNatWitgen.generate i), ("fold-word", foldWordWitgen.generate i)]
        let dirty : Buffer := ⟨#[boolCell enabled, x, x1, 16, c, 99,98,97,96,95,94], rfl⟩
        for entry in results do
          let entry : String × Option Witness := entry
          let name : String := entry.1
          let result : Option Witness := entry.2
          unless result == some expected do
            throw (IO.userError s!"record mismatch: {name}, {repr i}, {repr result}")
          match populateDecoded dirty result with
          | none => throw (IO.userError s!"missing decoded witness: {name}")
          | some b =>
            unless decide (Constraints i b) && decide (WitnessCells b expected) do
              throw (IO.userError s!"invalid complete buffer: {name}, {repr b.toArray}")
          stages := stages + 1
        inputs := inputs + 1
  IO.println s!"batch: {inputs} fixed triples; {stages} full-record and dirty-buffer checks passed"

#eval (populateDecoded (initial enabledInput) (sourceWitgen.generate enabledInput)).map Vector.toArray
#eval (populateDecoded (initial disabledInput) (foldWordWitgen.generate disabledInput)).map Vector.toArray
#print axioms Witgen.Batch.sound
#print axioms Witgen.Batch.gatedBatchField_eval
#print axioms Witgen.Batch.gatedBatchFoldField_correct
#print axioms Witgen.Batch.gatedBatchNat_correct
#print axioms Witgen.Batch.gatedBatchWord_correct
#print axioms Witgen.Batch.gatedBatchWord_eval
#print axioms Witgen.Batch.gatedBatchFoldNat_correct
#print axioms Witgen.Batch.gatedBatchFoldWord_eval
#print axioms Witgen.Batch.gatedBatchFoldWord_correct
#print axioms Witgen.Batch.sourceWitgen
#print axioms Witgen.Batch.foldFieldWitgen
#print axioms Witgen.Batch.natWitgen
#print axioms Witgen.Batch.wordWitgen
#print axioms Witgen.Batch.foldNatWitgen
#print axioms Witgen.Batch.foldWordWitgen
#print axioms Witgen.Batch.foldWord_generate_eq_source
#print axioms Witgen.Batch.mathematicallyComplete
#print axioms Witgen.Batch.source_completeOver
#print axioms Witgen.Batch.nat_completeOver
#print axioms Witgen.Batch.word_completeOver
#print axioms Witgen.Batch.decodeNat_complete_records
#print axioms Witgen.Batch.decodeNat_wrong_length
#print axioms Witgen.Batch.decodeField_wrong_length
#print axioms Witgen.Batch.decodeWord_wrong_length
#print axioms Witgen.Batch.none_rejected
#print axioms Witgen.Batch.native_record_shape
#print axioms Witgen.Batch.Slots.noAliases
#print axioms Witgen.Batch.Slots.covers
#print axioms Witgen.Batch.populate_inputs_unchanged
#print axioms Witgen.Batch.populate_witnessCells
#print axioms Witgen.Batch.constraints_of_cells
#print axioms Witgen.Batch.populate_constraints
#print axioms Witgen.Batch.honest_buffer
#print axioms Witgen.Batch.disabled_populates_all
#print axioms Witgen.Batch.constraints_iff
#print axioms Witgen.Batch.constraints_sound
#print axioms Witgen.Batch.constraints_canonical
#print axioms Witgen.Batch.certified_buffer
#print axioms Witgen.Batch.missing_square_rejected
#print axioms Witgen.Batch.disabled_stale_cell_rejected
