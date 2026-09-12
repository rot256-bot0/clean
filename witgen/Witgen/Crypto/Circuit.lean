import Witgen.Crypto.Program
import Witgen.Circuits

namespace Witgen.Crypto

structure QuadInput (p : Nat) where
  x : Fin p
  y : Fin p
  deriving Repr, DecidableEq

namespace QuadCircuit

/-- Independent gate relation on *all* witness fields, not generator equality. -/
def Relation {p : Nat} (i : QuadInput p) (w : QuadWitness (Fin p)) : Prop :=
  w.square = Residue.mul i.x i.x ∧ w.output = Residue.add w.square i.y

def Spec {p : Nat} (i : QuadInput p) (output : Fin p) : Prop :=
  output = Residue.add (Residue.mul i.x i.x) i.y

theorem sound {p : Nat} (i : QuadInput p) (w : QuadWitness (Fin p))
    (h : Relation i w) : Spec i w.output := by
  unfold Spec
  rw [h.2, h.1]

def circuit (p : Nat) : Circuits.Circuit (QuadInput p) (QuadWitness (Fin p)) (Fin p) where
  Assumptions := fun _ => True
  Relation := Relation
  output := QuadWitness.output
  Spec := Spec
  sound := fun i w _ h => sound i w h

namespace Slots
abbrev x : Nat := 0
abbrev y : Nat := 1
abbrev square : Nat := 2
abbrev output : Nat := 3

def layout : List Nat := [x, y, square, output]
theorem noAliases : layout.Nodup := by decide
theorem covers : ∀ k : Fin 4, k.val ∈ layout := by decide
end Slots

/-- Every cell is an arbitrary-precision canonical natural, never a machine word. -/
abbrev Buffer := Vector Nat 4

theorem buffer_layout : Buffer = Vector Nat Slots.layout.length := rfl

def initial {p : Nat} (i : QuadInput p) : Buffer := ⟨#[i.x.val, i.y.val, 0, 0], rfl⟩

def populate {p : Nat} (b : Buffer) (w : QuadWitness (Fin p)) : Buffer :=
  (b.set Slots.square w.square.val).set Slots.output w.output.val

def Inputs {p : Nat} (i : QuadInput p) (b : Buffer) : Prop :=
  b[Slots.x] = i.x.val ∧ b[Slots.y] = i.y.val

def WitnessCells {p : Nat} (b : Buffer) (w : QuadWitness (Fin p)) : Prop :=
  b[Slots.square] = w.square.val ∧ b[Slots.output] = w.output.val

/-- Native complete-cell relation: bound inputs, canonical cells, square gate,
and addition gate. Correct output alone cannot satisfy a corrupt internal cell. -/
def Constraints {p : Nat} (i : QuadInput p) (b : Buffer) : Prop :=
  Inputs i b ∧ b[Slots.square] < p ∧ b[Slots.output] < p ∧
  b[Slots.square] = (b[Slots.x] * b[Slots.x]) % p ∧
  b[Slots.output] = (b[Slots.square] + b[Slots.y]) % p

instance {p : Nat} (i : QuadInput p) (b : Buffer) : Decidable (Inputs i b) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance {p : Nat} (i : QuadInput p) (b : Buffer) : Decidable (Constraints i b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem initial_inputs {p : Nat} (i : QuadInput p) : Inputs i (initial i) := ⟨rfl, rfl⟩

theorem populate_inputs_unchanged {p : Nat} (b : Buffer) (w : QuadWitness (Fin p)) :
    (populate b w)[0] = b[0] ∧ (populate b w)[1] = b[1] := by
  simp [populate, Slots.square, Slots.output]

theorem populate_inputs {p : Nat} (i : QuadInput p) (b : Buffer) (w : QuadWitness (Fin p))
    (hb : Inputs i b) : Inputs i (populate b w) :=
  ⟨(populate_inputs_unchanged b w).1.trans hb.1,
   (populate_inputs_unchanged b w).2.trans hb.2⟩

theorem populate_witnessCells {p : Nat} (b : Buffer) (w : QuadWitness (Fin p)) :
    WitnessCells (populate b w) w := by
  simp [WitnessCells, populate]

theorem constraints_of_cells {p : Nat} (i : QuadInput p) (b : Buffer)
    (w : QuadWitness (Fin p)) (hb : Inputs i b) (hc : WitnessCells b w)
    (hw : Relation i w) : Constraints i b := by
  refine ⟨hb, ?_, ?_, ?_, ?_⟩
  · rw [hc.1]; exact w.square.isLt
  · rw [hc.2]; exact w.output.isLt
  · simpa only [hc.1, hb.1, Residue.mul_val] using congrArg Fin.val hw.1
  · simpa only [hc.2, hc.1, hb.2, Residue.add_val] using congrArg Fin.val hw.2

theorem populate_constraints {p : Nat} (i : QuadInput p) (b : Buffer)
    (w : QuadWitness (Fin p)) (hb : Inputs i b) (hw : Relation i w) :
    Constraints i (populate b w) :=
  constraints_of_cells i _ w (populate_inputs i b w hb) (populate_witnessCells b w) hw

/-- Every accepted complete buffer reconstructs a full satisfying witness;
conversely every bound, encoded satisfying witness passes every gate. -/
theorem constraints_iff {p : Nat} (i : QuadInput p) (b : Buffer) :
    Constraints i b ↔ Inputs i b ∧ ∃ w, WitnessCells b w ∧ Relation i w := by
  constructor
  · intro h
    let w : QuadWitness (Fin p) := ⟨⟨b[2], h.2.1⟩, ⟨b[3], h.2.2.1⟩⟩
    have hs : w.square = Residue.mul i.x i.x := by
      apply Fin.ext
      change b[2] = (i.x.val * i.x.val) % p
      rw [← h.1.1]
      exact h.2.2.2.1
    have ho : w.output = Residue.add w.square i.y := by
      apply Fin.ext
      change b[3] = (b[2] + i.y.val) % p
      rw [← h.1.2]
      exact h.2.2.2.2
    exact ⟨h.1, w, ⟨rfl, rfl⟩, hs, ho⟩
  · rintro ⟨hb, w, hc, hw⟩
    exact constraints_of_cells i b w hb hc hw

theorem constraints_canonical {p : Nat} (i : QuadInput p) (b : Buffer)
    (h : Constraints i b) : ∀ k : Fin 4, b[k.val] < p := by
  intro ⟨k, hk⟩
  match k with
  | 0 => rw [h.1.1]; exact i.x.isLt
  | 1 => rw [h.1.2]; exact i.y.isLt
  | 2 => exact h.2.1
  | 3 => exact h.2.2.1
  | _ + 4 => omega

theorem constraints_sound {p : Nat} (i : QuadInput p) (b : Buffer)
    (h : Constraints i b) : b[3] = (Residue.add (Residue.mul i.x i.x) i.y).val := by
  obtain ⟨_, w, hc, hw⟩ := (constraints_iff i b).1 h
  exact hc.2.trans (congrArg Fin.val (sound i w hw))

/-- The native output paths have exactly the proved record field order. -/
def outputPaths : List (String × Nat) :=
  (schemaDesc .quad).fields.zip [Slots.square, Slots.output] |>.map fun (field, slot) =>
    (field.1, slot)

theorem outputPaths_exact : outputPaths = [("square", 2), ("output", 3)] := rfl

end QuadCircuit

def encodeField {p : Nat} (i : QuadInput p) : HList (Val (Fin p)) [.scalar, .scalar] :=
  .cons i.x (.cons i.y .nil)
def encodeNat {p : Nat} (i : QuadInput p) : HList (Val Nat) [.scalar, .scalar] :=
  .cons i.x.val (.cons i.y.val .nil)

def decodeNat {p : Nat} (hp : 0 < p) (w : QuadWitness Nat) : QuadWitness (Fin p) :=
  ⟨Residue.ofNat hp w.square, Residue.ofNat hp w.output⟩

theorem decode_graph {p : Nat} (hp : 0 < p) (x : QuadWitness (Fin p)) (y : QuadWitness Nat)
    (h : Graph Fin.val .quad x y) : x = decodeNat hp y := by
  change (⟨x.square.val, x.output.val⟩ : QuadWitness Nat) = y at h
  rw [← h]
  simp only [decodeNat, Residue.ofNat_val_id]

def quadFieldWitgen {p : Nat} (hp : 0 < p) :
    Circuits.FormalWitgen (QuadCircuit.circuit p) (fieldModel hp) [.scalar, .scalar] .quad where
  program := quadraticField
  encodeInput := encodeField
  decodeWitness := id
  correct := fun _ _ => ⟨rfl, rfl⟩

def quadNatWitgen {p : Nat} (hp : 0 < p) :
    Circuits.FormalWitgen (QuadCircuit.circuit p) natModel [.scalar, .scalar] .quad :=
  (quadFieldWitgen hp).lower (fieldNatLowering hp) encodeNat (decodeNat hp)
    (fun _ _ => ⟨rfl, rfl, trivial⟩) (decode_graph hp)

/-- The certified Nat generator exports the very AST produced by lowering. -/
theorem quadNat_program {p : Nat} (hp : 0 < p) :
    (quadNatWitgen hp).program = quadraticNat p := rfl

theorem quadNat_generate {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    (quadNatWitgen hp).generate i = (quadFieldWitgen hp).generate i :=
  Circuits.FormalWitgen.lower_generate (quadFieldWitgen hp) (fieldNatLowering hp)
    encodeNat (decodeNat hp) (fun _ _ => ⟨rfl, rfl, trivial⟩) (decode_graph hp) i trivial

/-- Exact raw Nat record equals the field record's canonical representatives:
no post-hoc modular normalization conceals a noncanonical exported value. -/
theorem quadNat_raw_canonical {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    (quadraticNat p).eval natModel (encodeNat i) =
      Val.map Fin.val ((quadFieldWitgen hp).generate i) :=
  (fieldToNat_correct hp quadraticField (encodeField i)).symm

theorem quad_full_buffer_agrees {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    QuadCircuit.populate (QuadCircuit.initial i) ((quadNatWitgen hp).generate i) =
      QuadCircuit.populate (QuadCircuit.initial i) ((quadFieldWitgen hp).generate i) := by
  rw [quadNat_generate]

theorem quad_field_buffer_correct {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    QuadCircuit.Constraints i
      (QuadCircuit.populate (QuadCircuit.initial i) ((quadFieldWitgen hp).generate i)) :=
  QuadCircuit.populate_constraints i _ _ (QuadCircuit.initial_inputs i)
    ((quadFieldWitgen hp).satisfies i trivial)

theorem quad_nat_buffer_correct {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    QuadCircuit.Constraints i
      (QuadCircuit.populate (QuadCircuit.initial i) ((quadNatWitgen hp).generate i)) := by
  rw [quad_full_buffer_agrees]
  exact quad_field_buffer_correct hp i

/-- Raw exporter ABI: no modular normalization or narrowing in any cell. -/
def encodeRawNat {p : Nat} (i : QuadInput p) (w : QuadWitness Nat) : QuadCircuit.Buffer :=
  ⟨#[i.x.val, i.y.val, w.square, w.output], rfl⟩

theorem quad_nat_raw_buffer {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    encodeRawNat i ((quadraticNat p).eval natModel (encodeNat i)) =
      QuadCircuit.populate (QuadCircuit.initial i) ((quadFieldWitgen hp).generate i) := by
  rw [quadNat_raw_canonical hp]
  rfl

end Witgen.Crypto
