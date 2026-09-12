import Witgen.Pipeline
import Witgen.Circuits

set_option autoImplicit false

/-! Fixed three-row gated circuit. Native arithmetic is exclusively in typed
optional feature ASTs; adapters only pack inputs and check complete records. -/
namespace Witgen.Batch
open Demo Arithmetic Circuits

structure Input where
  enabled : Bool
  x0 : Field17
  x1 : Field17
  x2 : Field17
  c : Field17
  deriving Repr, DecidableEq

abbrev Context : List Ty := [.bool, .list .scalar, .scalar]

def encodeField (i : Input) : HList (Val Field17) Context :=
  .cons i.enabled (.cons [i.x0, i.x1, i.x2] (.cons i.c .nil))

/-- Even the disabled record is built by field/data operation syntax. -/
def zeroQuad {F : Signature Ty} [Has FieldOp F] [Has DataOp F] :
    Program F [.scalar, .scalar] .quad :=
  .let_ (Has.inject (FieldOp.const 0)) .nil .nil <|
  .let_ (Has.inject DataOp.quad) (.cons .zero (.cons .zero .nil)) .nil (.ret .zero)

/-- Map body receives [element, enabled, c]; branch regions receive [element,c]. -/
def gatedQuad {F : Signature Ty} [Has FieldOp F] [Has DataOp F] [Has Control F] :
    Program F [.scalar, .bool, .scalar] .quad :=
  .let_ (Has.inject (Control.branch [.scalar, .scalar] .quad))
    (.cons (.succ .zero) (.cons .zero (.cons (.succ (.succ .zero)) .nil)))
    (.cons quadratic (.cons zeroQuad .nil)) (.ret .zero)

def gatedBatch {F : Signature Ty} [Has FieldOp F] [Has DataOp F] [Has Control F] :
    Program F Context (.list .quad) :=
  .let_ (Has.inject (Control.map [.bool, .scalar] .scalar .quad))
    (.cons (.succ .zero) (.cons .zero (.cons (.succ (.succ .zero)) .nil)))
    (.cons gatedQuad .nil) (.ret .zero)

def gatedBatchField : Program FieldSig Context (.list .quad) := gatedBatch

/-- Mathematical specification, not an encoder/decoder or hidden program node. -/
def expectedQuad (enabled : Bool) (x c : Field17) : Quad Field17 :=
  if enabled then ⟨Field17.mul x x, Field17.add (Field17.mul x x) c⟩ else ⟨0, 0⟩

def expectedRecords (i : Input) : List (Quad Field17) :=
  [expectedQuad i.enabled i.x0 i.c, expectedQuad i.enabled i.x1 i.c,
   expectedQuad i.enabled i.x2 i.c]

theorem gatedBatchField_eval (i : Input) :
    gatedBatchField.eval fieldModel (encodeField i) = expectedRecords i := by
  cases i with
  | mk enabled x0 x1 x2 c => cases enabled <;> rfl

theorem gatedBatchField_length (i : Input) :
    (gatedBatchField.eval fieldModel (encodeField i)).length = 3 := by
  rw [gatedBatchField_eval]
  rfl

def encodeNat (i : Input) : HList (Val Nat) Context :=
  (encodeField i).map (Val.map Field17.toNat)

def encodeWord (i : Input) : HList (Val UInt64) Context :=
  (encodeField i).map (Val.map fieldWord)

def gatedBatchFoldField : Program FieldSig Context (.list .quad) :=
  gatedBatchField.lower (mapToFold FieldOp)

def gatedBatchNat : Program NatSig Context (.list .quad) :=
  gatedBatchField.lower fieldToNat

def gatedBatchWord : Program WordSig Context (.list .quad) :=
  gatedBatchNat.mapHandler natToWord

def gatedBatchFoldNat : Program NatSig Context (.list .quad) :=
  gatedBatchFoldField.lower fieldToNat

def gatedBatchFoldWord : Program WordSig Context (.list .quad) :=
  gatedBatchFoldNat.mapHandler natToWord

theorem gatedBatchFoldField_correct (i : Input) :
    gatedBatchFoldField.eval fieldModel (encodeField i) =
      gatedBatchField.eval fieldModel (encodeField i) :=
  mapToFold_correct fieldScalarModel gatedBatchField (encodeField i)

theorem gatedBatchNat_correct (i : Input) :
    gatedBatchNat.eval natModel (encodeNat i) =
      Val.map Field17.toNat (t := .list .quad) (expectedRecords i) := by
  rw [← gatedBatchField_eval]
  exact (fieldToNat_correct gatedBatchField (encodeField i)).symm

/-- The word theorem is restricted to the actual Field17→Nat image, not all Nat ASTs. -/
theorem gatedBatchWord_correct (i : Input) :
    Val.map UInt64.toNat (t := .list .quad)
      (gatedBatchWord.eval wordModel (encodeWord i)) =
      gatedBatchNat.eval natModel (encodeNat i) :=
  natToWord_fieldImage_correct gatedBatchField (encodeField i)

theorem gatedBatchWord_eval (i : Input) :
    gatedBatchWord.eval wordModel (encodeWord i) =
      Val.map fieldWord (t := .list .quad) (expectedRecords i) := by
  change ((gatedBatchField.lower fieldToNat).mapHandler natToWord).eval _ _ = _
  unfold encodeWord
  rw [lower_commutes, ← fieldToWord_correct gatedBatchField (encodeField i), gatedBatchField_eval]

theorem gatedBatchFoldNat_correct (i : Input) :
    gatedBatchFoldNat.eval natModel (encodeNat i) =
      Val.map Field17.toNat (t := .list .quad) (expectedRecords i) := by
  change (gatedBatchFoldField.lower fieldToNat).eval _ _ = _
  unfold encodeNat
  rw [← fieldToNat_correct gatedBatchFoldField (encodeField i),
    gatedBatchFoldField_correct, gatedBatchField_eval]

theorem gatedBatchFoldWord_eval (i : Input) :
    gatedBatchFoldWord.eval wordModel (encodeWord i) =
      Val.map fieldWord (t := .list .quad) (expectedRecords i) := by
  change ((gatedBatchFoldField.lower fieldToNat).mapHandler natToWord).eval _ _ = _
  unfold encodeWord
  rw [lower_commutes, ← fieldToWord_correct gatedBatchFoldField (encodeField i),
    gatedBatchFoldField_correct, gatedBatchField_eval]

theorem gatedBatchFoldWord_correct (i : Input) :
    Val.map UInt64.toNat (t := .list .quad)
      (gatedBatchFoldWord.eval wordModel (encodeWord i)) =
      Val.map Field17.toNat (t := .list .quad) (expectedRecords i) := by
  rw [gatedBatchFoldWord_eval, Val.fieldWord_roundtrip]

structure Witness where
  q0 : Quad Nat
  q1 : Quad Nat
  q2 : Quad Nat
  deriving Repr, DecidableEq

/-- Exact length check; missing and extra records are rejected, never defaulted. -/
def decodeNat : List (Quad Nat) → Option Witness
  | [q0, q1, q2] => some ⟨q0, q1, q2⟩
  | _ => none

def decodeField (xs : List (Quad Field17)) : Option Witness :=
  decodeNat (Val.map Field17.toNat (t := .list .quad) xs)

def decodeWord (xs : List (Quad UInt64)) : Option Witness :=
  decodeNat (Val.map UInt64.toNat (t := .list .quad) xs)

theorem decodeNat_wrong_length (xs : List (Quad Nat)) (h : xs.length ≠ 3) :
    decodeNat xs = none := by
  match xs with
  | [] | [_] | [_, _] => rfl
  | [_, _, _] => exact False.elim (h rfl)
  | _ :: _ :: _ :: _ :: _ => rfl

theorem decodeNat_complete_records (xs : List (Quad Nat)) (w : Witness)
    (h : decodeNat xs = some w) : xs = [w.q0, w.q1, w.q2] := by
  match xs with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => contradiction
  | [q0, q1, q2] => cases h; rfl

/-- Generator-independent canonical Nat encoding of two gated field equations.
The disabled rows are constrained to zero, not left unconstrained. -/
def RowRelation (enabled : Bool) (x c : Nat) (w : Quad Nat) : Prop :=
  w.square < 17 ∧ w.output < 17 ∧
    if enabled then w.square = (x * x) % 17 ∧ w.output = (w.square + c) % 17
    else w.square = 0 ∧ w.output = 0

def RecordsRelation (i : Input) (w : Witness) : Prop :=
  RowRelation i.enabled i.x0.toNat i.c.toNat w.q0 ∧
  RowRelation i.enabled i.x1.toNat i.c.toNat w.q1 ∧
  RowRelation i.enabled i.x2.toNat i.c.toNat w.q2

def Relation (i : Input) : Option Witness → Prop
  | none => False
  | some w => RecordsRelation i w

instance (b : Bool) (x c : Nat) (w : Quad Nat) : Decidable (RowRelation b x c w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (i : Input) (w : Witness) : Decidable (RecordsRelation i w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (i : Input) (w : Option Witness) : Decidable (Relation i w) :=
  match w with
  | none => inferInstanceAs (Decidable False)
  | some w => inferInstanceAs (Decidable (RecordsRelation i w))

def expectedOutput (enabled : Bool) (x c : Nat) : Nat :=
  if enabled then ((x * x) % 17 + c) % 17 else 0

def output (w : Option Witness) : Option (List Nat) :=
  w.map (fun w => [w.q0.output, w.q1.output, w.q2.output])

def Spec (i : Input) (o : Option (List Nat)) : Prop :=
  o = some [expectedOutput i.enabled i.x0.toNat i.c.toNat,
    expectedOutput i.enabled i.x1.toNat i.c.toNat,
    expectedOutput i.enabled i.x2.toNat i.c.toNat]

theorem row_sound (b : Bool) (x c : Nat) (w : Quad Nat) (h : RowRelation b x c w) :
    w.output = expectedOutput b x c := by
  cases b with
  | false => exact h.2.2.2
  | true => exact h.2.2.2.trans (congrArg (fun s => (s + c) % 17) h.2.2.1)

theorem sound (i : Input) (w : Option Witness) (_hi : True) (h : Relation i w) :
    Spec i (output w) := by
  cases w with
  | none => exact False.elim h
  | some w =>
    change some [w.q0.output, w.q1.output, w.q2.output] = _
    rw [row_sound _ _ _ _ h.1, row_sound _ _ _ _ h.2.1, row_sound _ _ _ _ h.2.2]

def circuit : Circuit Input (Option Witness) (Option (List Nat)) where
  Assumptions := fun _ => True
  Relation := Relation
  output := output
  Spec := Spec
  sound := sound

theorem none_rejected (i : Input) : ¬ Relation i none := fun h => h

def expectedWitness (i : Input) : Witness :=
  ⟨Val.map Field17.toNat (t := .quad) (expectedQuad i.enabled i.x0 i.c),
   Val.map Field17.toNat (t := .quad) (expectedQuad i.enabled i.x1 i.c),
   Val.map Field17.toNat (t := .quad) (expectedQuad i.enabled i.x2 i.c)⟩

theorem expectedQuad_relation (b : Bool) (x c : Field17) :
    RowRelation b x.toNat c.toNat (Val.map Field17.toNat (t := .quad) (expectedQuad b x c)) := by
  cases b with
  | false => exact ⟨(by decide : 0 < 17), (by decide : 0 < 17), rfl, rfl⟩
  | true => exact ⟨(Field17.mul x x).isLt, (Field17.add (Field17.mul x x) c).isLt, rfl, rfl⟩

theorem expectedWitness_relation (i : Input) : Relation i (some (expectedWitness i)) :=
  ⟨expectedQuad_relation _ _ _, expectedQuad_relation _ _ _, expectedQuad_relation _ _ _⟩

theorem source_generates (i : Input) :
    decodeField (gatedBatchField.eval fieldModel (encodeField i)) = some (expectedWitness i) := by
  rw [gatedBatchField_eval]
  rfl

theorem nat_generates (i : Input) :
    decodeNat (gatedBatchNat.eval natModel (encodeNat i)) = some (expectedWitness i) := by
  rw [gatedBatchNat_correct]
  rfl

theorem word_generates (i : Input) :
    decodeWord (gatedBatchWord.eval wordModel (encodeWord i)) = some (expectedWitness i) := by
  unfold decodeWord
  rw [gatedBatchWord_correct, gatedBatchNat_correct]
  rfl

theorem foldField_generates (i : Input) :
    decodeField (gatedBatchFoldField.eval fieldModel (encodeField i)) = some (expectedWitness i) := by
  rw [gatedBatchFoldField_correct]
  exact source_generates i

theorem foldNat_generates (i : Input) :
    decodeNat (gatedBatchFoldNat.eval natModel (encodeNat i)) = some (expectedWitness i) := by
  rw [gatedBatchFoldNat_correct]
  rfl

theorem foldWord_generates (i : Input) :
    decodeWord (gatedBatchFoldWord.eval wordModel (encodeWord i)) = some (expectedWitness i) := by
  unfold decodeWord
  rw [gatedBatchFoldWord_correct]
  rfl

def sourceWitgen : FormalWitgen circuit fieldModel Context (.list .quad) where
  program := gatedBatchField
  encodeInput := encodeField
  decodeWitness := decodeField
  correct := by
    intro i _
    change Relation i (decodeField (gatedBatchField.eval fieldModel (encodeField i)))
    rw [source_generates]
    exact expectedWitness_relation i

def foldFieldWitgen : FormalWitgen circuit fieldModel Context (.list .quad) where
  program := gatedBatchFoldField
  encodeInput := encodeField
  decodeWitness := decodeField
  correct := by
    intro i _
    change Relation i (decodeField (gatedBatchFoldField.eval fieldModel (encodeField i)))
    rw [foldField_generates]
    exact expectedWitness_relation i

def natWitgen : FormalWitgen circuit natModel Context (.list .quad) where
  program := gatedBatchNat
  encodeInput := encodeNat
  decodeWitness := decodeNat
  correct := by
    intro i _
    change Relation i (decodeNat (gatedBatchNat.eval natModel (encodeNat i)))
    rw [nat_generates]
    exact expectedWitness_relation i

def wordWitgen : FormalWitgen circuit wordModel Context (.list .quad) where
  program := gatedBatchWord
  encodeInput := encodeWord
  decodeWitness := decodeWord
  correct := by
    intro i _
    change Relation i (decodeWord (gatedBatchWord.eval wordModel (encodeWord i)))
    rw [word_generates]
    exact expectedWitness_relation i

def foldNatWitgen : FormalWitgen circuit natModel Context (.list .quad) where
  program := gatedBatchFoldNat
  encodeInput := encodeNat
  decodeWitness := decodeNat
  correct := by
    intro i _
    change Relation i (decodeNat (gatedBatchFoldNat.eval natModel (encodeNat i)))
    rw [foldNat_generates]
    exact expectedWitness_relation i

def foldWordWitgen : FormalWitgen circuit wordModel Context (.list .quad) where
  program := gatedBatchFoldWord
  encodeInput := encodeWord
  decodeWitness := decodeWord
  correct := by
    intro i _
    change Relation i (decodeWord (gatedBatchFoldWord.eval wordModel (encodeWord i)))
    rw [foldWord_generates]
    exact expectedWitness_relation i

theorem foldWord_generate_eq_source (i : Input) :
    foldWordWitgen.generate i = sourceWitgen.generate i :=
  (foldWord_generates i).trans (source_generates i).symm

theorem mathematicallyComplete : circuit.MathematicallyComplete := sourceWitgen.mathematicallyComplete

theorem source_completeOver :
    CompleteOver circuit fieldModel (t := .list .quad) encodeField decodeField :=
  sourceWitgen.completeOver

theorem nat_completeOver : CompleteOver circuit natModel (t := .list .quad) encodeNat decodeNat :=
  natWitgen.completeOver

theorem word_completeOver : CompleteOver circuit wordModel (t := .list .quad) encodeWord decodeWord :=
  wordWitgen.completeOver

namespace Slots
abbrev enabled : Nat := 0
abbrev x0 : Nat := 1
abbrev x1 : Nat := 2
abbrev x2 : Nat := 3
abbrev c : Nat := 4
abbrev square0 : Nat := 5
abbrev out0 : Nat := 6
abbrev square1 : Nat := 7
abbrev out1 : Nat := 8
abbrev square2 : Nat := 9
abbrev out2 : Nat := 10

def recordStarts : List Nat := [square0, square1, square2]
def layout : List Nat := [enabled, x0, x1, x2, c, square0, out0, square1, out1, square2, out2]
theorem noAliases : layout.Nodup := by decide
theorem covers : ∀ k : Fin 11, k.val ∈ layout := by decide
end Slots

abbrev Buffer := Vector Nat 11

theorem buffer_layout : Buffer = Vector Nat Slots.layout.length := rfl

theorem result_layout_size (i : Input) :
    (gatedBatchField.eval fieldModel (encodeField i)).length = Slots.recordStarts.length :=
  gatedBatchField_length i

def boolCell (b : Bool) : Nat := if b then 1 else 0

theorem boolCell_test (b : Bool) : (boolCell b == 1) = b := by cases b <;> rfl

def initial (i : Input) : Buffer :=
  ⟨#[boolCell i.enabled, i.x0.toNat, i.x1.toNat, i.x2.toNat, i.c.toNat, 0,0,0,0,0,0], rfl⟩

/-- Six unconditional stores: the disabled path overwrites stale cells too. -/
def populate (b : Buffer) (w : Witness) : Buffer :=
  let b := (b.set Slots.square0 w.q0.square).set Slots.out0 w.q0.output
  let b := (b.set Slots.square1 w.q1.square).set Slots.out1 w.q1.output
  (b.set Slots.square2 w.q2.square).set Slots.out2 w.q2.output

def populateDecoded (b : Buffer) (w : Option Witness) : Option Buffer :=
  w.map (populate b)

def Inputs (i : Input) (b : Buffer) : Prop :=
  b[Slots.enabled] = boolCell i.enabled ∧ b[Slots.x0] = i.x0.toNat ∧
  b[Slots.x1] = i.x1.toNat ∧ b[Slots.x2] = i.x2.toNat ∧ b[Slots.c] = i.c.toNat

def WitnessCells (b : Buffer) (w : Witness) : Prop :=
  b[Slots.square0] = w.q0.square ∧ b[Slots.out0] = w.q0.output ∧
  b[Slots.square1] = w.q1.square ∧ b[Slots.out1] = w.q1.output ∧
  b[Slots.square2] = w.q2.square ∧ b[Slots.out2] = w.q2.output

/-- Direct gated equations on the buffer. No generator or writer is referenced. -/
def Constraints (i : Input) (b : Buffer) : Prop :=
  Inputs i b ∧
  RowRelation (b[Slots.enabled] == 1) b[Slots.x0] b[Slots.c] ⟨b[Slots.square0], b[Slots.out0]⟩ ∧
  RowRelation (b[Slots.enabled] == 1) b[Slots.x1] b[Slots.c] ⟨b[Slots.square1], b[Slots.out1]⟩ ∧
  RowRelation (b[Slots.enabled] == 1) b[Slots.x2] b[Slots.c] ⟨b[Slots.square2], b[Slots.out2]⟩

instance (i : Input) (b : Buffer) : Decidable (Inputs i b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
instance (b : Buffer) (w : Witness) : Decidable (WitnessCells b w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
instance (i : Input) (b : Buffer) : Decidable (Constraints i b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem initial_inputs (i : Input) : Inputs i (initial i) := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem populate_inputs_unchanged (b : Buffer) (w : Witness) (k : Fin 5) :
    (populate b w)[k.val] = b[k.val] := by
  obtain ⟨k, hk⟩ := k
  match k with
  | 0 | 1 | 2 | 3 | 4 => simp [populate, Slots.square0, Slots.out0, Slots.square1, Slots.out1, Slots.square2, Slots.out2]
  | _ + 5 => omega

theorem populate_inputs (i : Input) (b : Buffer) (w : Witness) (h : Inputs i b) :
    Inputs i (populate b w) :=
  ⟨(populate_inputs_unchanged b w 0).trans h.1,
   (populate_inputs_unchanged b w 1).trans h.2.1,
   (populate_inputs_unchanged b w 2).trans h.2.2.1,
   (populate_inputs_unchanged b w 3).trans h.2.2.2.1,
   (populate_inputs_unchanged b w 4).trans h.2.2.2.2⟩

theorem populate_witnessCells (b : Buffer) (w : Witness) : WitnessCells (populate b w) w := by
  simp [WitnessCells, populate, Slots.square0, Slots.out0, Slots.square1, Slots.out1, Slots.square2, Slots.out2]

theorem constraints_of_cells (i : Input) (b : Buffer) (w : Witness)
    (hb : Inputs i b) (hc : WitnessCells b w) (hw : RecordsRelation i w) : Constraints i b := by
  refine ⟨hb, ?_⟩
  simpa only [RecordsRelation, RowRelation, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1,
    hc.2.2.2.2.2, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2, boolCell_test]
    using hw

theorem populate_constraints (i : Input) (b : Buffer) (w : Witness)
    (hb : Inputs i b) (hw : RecordsRelation i w) : Constraints i (populate b w) :=
  constraints_of_cells i _ w (populate_inputs i b w hb) (populate_witnessCells b w) hw

theorem honest_buffer (i : Input) : Constraints i (populate (initial i) (expectedWitness i)) :=
  populate_constraints i _ _ (initial_inputs i) (expectedWitness_relation i)

theorem disabled_populates_all (i : Input) (b : Buffer) (h : i.enabled = false) (k : Fin 6) :
    (populate b (expectedWitness i))[k.val + 5] = 0 := by
  obtain ⟨k, hk⟩ := k
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp [populate, Slots.square0, Slots.out0, Slots.square1, Slots.out1, Slots.square2, Slots.out2, expectedWitness, expectedQuad, h, Val.map, Field17.toNat]
  | _ + 6 => omega

theorem missing_square_rejected :
    ¬ Constraints ⟨true,3,4,16,4⟩ ⟨#[1,3,4,16,4,0,13,16,3,1,5], rfl⟩ := by decide

theorem disabled_stale_cell_rejected :
    ¬ Constraints ⟨false,3,4,16,4⟩ ⟨#[0,3,4,16,4,9,0,0,0,0,0], rfl⟩ := by decide

/-- Logical shape of the actual native results at every pipeline stage. -/
theorem native_record_shape (i : Input) :
    (gatedBatchField.eval fieldModel (encodeField i)).length = 3 ∧
    (gatedBatchFoldField.eval fieldModel (encodeField i)).length = 3 ∧
    (gatedBatchNat.eval natModel (encodeNat i)).length = 3 ∧
    (gatedBatchWord.eval wordModel (encodeWord i)).length = 3 ∧
    (gatedBatchFoldNat.eval natModel (encodeNat i)).length = 3 ∧
    (gatedBatchFoldWord.eval wordModel (encodeWord i)).length = 3 := by
  rw [gatedBatchFoldField_correct, gatedBatchField_eval, gatedBatchNat_correct,
    gatedBatchWord_eval, gatedBatchFoldNat_correct, gatedBatchFoldWord_eval]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem decodeField_wrong_length (xs : List (Quad Field17)) (h : xs.length ≠ 3) :
    decodeField xs = none :=
  decodeNat_wrong_length _ (by simpa only [Val.map, List.length_map] using h)

theorem decodeWord_wrong_length (xs : List (Quad UInt64)) (h : xs.length ≠ 3) :
    decodeWord xs = none :=
  decodeNat_wrong_length _ (by simpa only [Val.map, List.length_map] using h)

/-- Equivalence uses the actual six buffer cells, not a selected generator. -/
theorem constraints_iff (i : Input) (b : Buffer) :
    Constraints i b ↔ Inputs i b ∧ ∃ w, WitnessCells b w ∧ RecordsRelation i w := by
  constructor
  · intro h
    refine ⟨h.1, ⟨⟨b[5], b[6]⟩, ⟨b[7], b[8]⟩, ⟨b[9], b[10]⟩⟩,
      ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩, ?_⟩
    simpa only [RecordsRelation, h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1,
      h.1.2.2.2.2, boolCell_test] using h.2
  · rintro ⟨hb, w, hc, hw⟩
    exact constraints_of_cells i b w hb hc hw

theorem constraints_sound (i : Input) (b : Buffer) (h : Constraints i b) :
    Spec i (some [b[6], b[8], b[10]]) := by
  obtain ⟨_, w, hc, hw⟩ := (constraints_iff i b).1 h
  rw [hc.2.1, hc.2.2.2.1, hc.2.2.2.2.2]
  exact sound i (some w) trivial hw

theorem constraints_canonical (i : Input) (b : Buffer) (h : Constraints i b) :
    ∀ k : Fin 11, b[k.val] < 17 := by
  intro ⟨k, hk⟩
  match k with
  | 0 => rw [h.1.1]; cases i.enabled <;> decide
  | 1 => rw [h.1.2.1]; exact i.x0.isLt
  | 2 => rw [h.1.2.2.1]; exact i.x1.isLt
  | 3 => rw [h.1.2.2.2.1]; exact i.x2.isLt
  | 4 => rw [h.1.2.2.2.2]; exact i.c.isLt
  | 5 => exact h.2.1.1
  | 6 => exact h.2.1.2.1
  | 7 => exact h.2.2.1.1
  | 8 => exact h.2.2.1.2.1
  | 9 => exact h.2.2.2.1
  | 10 => exact h.2.2.2.2.1
  | _ + 11 => omega

/-- Any typed certificate must return Some and populate every witness cell. -/
theorem certified_buffer {S : Type} {F : Signature S} {V : S → Type}
    {M : Model F V} {Γ : List S} {t : S}
    (g : FormalWitgen circuit M Γ t) (i : Input) :
    ∃ w b, g.generate i = some w ∧
      populateDecoded (initial i) (g.generate i) = some b ∧
      WitnessCells b w ∧ Inputs i b ∧ Constraints i b := by
  have h : Relation i (g.generate i) := g.satisfies i trivial
  cases hg : g.generate i with
  | none => rw [hg] at h; exact False.elim h
  | some w =>
    rw [hg] at h
    refine ⟨w, populate (initial i) w, rfl, rfl, populate_witnessCells _ _,
      populate_inputs i _ _ (initial_inputs i), ?_⟩
    exact populate_constraints i _ _ (initial_inputs i) h

end Witgen.Batch
