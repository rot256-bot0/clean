import Witgen.Core
import Witgen.Arithmetic

set_option autoImplicit false

/-! Circuit relations and full-record generator certificates, independent of any
concrete feature language or native backend. -/
namespace Witgen.Circuits

/-- Circuit soundness quantifies over every satisfying witness, not a generator. -/
structure Circuit (Input Witness Output : Type) where
  Assumptions : Input → Prop
  Relation : Input → Witness → Prop
  output : Witness → Output
  Spec : Input → Output → Prop
  sound : ∀ i w, Assumptions i → Relation i w → Spec i (output w)

section Generic
variable {Input Witness Output : Type}

/-- Feature-independent existence of a full satisfying witness. -/
def Circuit.MathematicallyComplete (C : Circuit Input Witness Output) : Prop :=
  ∀ i, C.Assumptions i → ∃ w, C.Relation i w

/-- Actual typed syntax, explicit semantic adapters, and the full relation proof.
Adapters belong to the semantic boundary; no claim is made that an arbitrary
adapter is a cost-free codec or implementable by the declared features. -/
structure FormalWitgen (C : Circuit Input Witness Output)
    {S : Type} {F : Signature S} {V : S → Type}
    (M : Model F V) (Γ : List S) (t : S) where
  program : Program F Γ t
  encodeInput : Input → HList V Γ
  decodeWitness : V t → Witness
  correct : ∀ i, C.Assumptions i →
    C.Relation i (decodeWitness (program.eval M (encodeInput i)))

/-- Completeness relative to exact features/model AND a fixed boundary ABI.
The adapters are parameters, not existential witnesses: otherwise arbitrary
host computation in an encoder/decoder could masquerade as an empty-feature
implementation. Native admission must separately implement this fixed ABI. -/
def CompleteOver (C : Circuit Input Witness Output)
    {S : Type} {F : Signature S} {V : S → Type} (M : Model F V)
    {Γ : List S} {t : S}
    (encodeInput : Input → HList V Γ) (decodeWitness : V t → Witness) : Prop :=
  ∃ p : Program F Γ t, ∀ i, C.Assumptions i →
    C.Relation i (decodeWitness (p.eval M (encodeInput i)))

namespace FormalWitgen
variable {C : Circuit Input Witness Output}
  {S : Type} {F G : Signature S} {V W : S → Type}
  {M : Model F V} {N : Model G W} {Γ : List S} {t : S}

def generate (g : FormalWitgen C M Γ t) (i : Input) : Witness :=
  g.decodeWitness (g.program.eval M (g.encodeInput i))

theorem satisfies (g : FormalWitgen C M Γ t) (i : Input)
    (hi : C.Assumptions i) : C.Relation i (g.generate i) := g.correct i hi

theorem spec (g : FormalWitgen C M Γ t) (i : Input)
    (hi : C.Assumptions i) : C.Spec i (C.output (g.generate i)) :=
  C.sound i _ hi (g.satisfies i hi)

theorem mathematicallyComplete (g : FormalWitgen C M Γ t) :
    C.MathematicallyComplete := fun i hi => ⟨g.generate i, g.satisfies i hi⟩

theorem completeOver (g : FormalWitgen C M Γ t) :
    CompleteOver C M g.encodeInput g.decodeWitness :=
  ⟨g.program, g.correct⟩

/-- Transport the exact program and whole-witness correctness. Related output
adapters must agree on every witness field, not only the public output. -/
def lower (g : FormalWitgen C M Γ t)
    {R : ∀ s, V s → W s → Prop} (L : CertifiedLowering M N R)
    (encodeInput : Input → HList W Γ) (decodeWitness : W t → Witness)
    (input_related : ∀ i, C.Assumptions i → HList.Rel R (g.encodeInput i) (encodeInput i))
    (decode_related : ∀ x y, R t x y → g.decodeWitness x = decodeWitness y) :
    FormalWitgen C N Γ t where
  program := L.run g.program
  encodeInput := encodeInput
  decodeWitness := decodeWitness
  correct := by
    intro i hi
    have h := decode_related _ _ (L.correct g.program _ _ (input_related i hi))
    rw [← h]
    exact g.correct i hi

theorem lower_generate (g : FormalWitgen C M Γ t)
    {R : ∀ s, V s → W s → Prop} (L : CertifiedLowering M N R)
    (encodeInput : Input → HList W Γ) (decodeWitness : W t → Witness)
    (input_related : ∀ i, C.Assumptions i → HList.Rel R (g.encodeInput i) (encodeInput i))
    (decode_related : ∀ x y, R t x y → g.decodeWitness x = decodeWitness y)
    (i : Input) (hi : C.Assumptions i) :
    (g.lower L encodeInput decodeWitness input_related decode_related).generate i =
      g.generate i :=
  (decode_related _ _ (L.correct g.program _ _ (input_related i hi))).symm

end FormalWitgen
end Generic

namespace Quadratic
open Arithmetic

structure Input where
  x : Field17
  y : Field17
  deriving Repr, DecidableEq

/-- Both internal cells are part of the witness boundary. -/
structure Witness where
  square : Field17
  output : Field17
  deriving Repr, DecidableEq

def Assumptions (_i : Input) : Prop := True

def Relation (i : Input) (w : Witness) : Prop :=
  Field17.MulRel i.x i.x w.square ∧ Field17.AddRel w.square i.y w.output

def Spec (i : Input) (output : Field17) : Prop :=
  output = Field17.add (Field17.mul i.x i.x) i.y

theorem sound (i : Input) (w : Witness) (_hi : Assumptions i)
    (h : Relation i w) : Spec i w.output := by
  have hs := Field17.mul_sound h.1
  have ho := Field17.add_sound h.2
  unfold Spec
  rw [ho, hs]

def circuit : Circuit Input Witness Field17 where
  Assumptions := Assumptions
  Relation := Relation
  output := Witness.output
  Spec := Spec
  sound := sound

def gen (i : Input) : Witness :=
  let square := Field17.mul i.x i.x
  ⟨square, Field17.add square i.y⟩

theorem gen_correct (i : Input) : Relation i (gen i) :=
  ⟨Field17.mul_correct i.x i.x, Field17.add_correct _ i.y⟩

theorem mathematicallyComplete : circuit.MathematicallyComplete :=
  fun i _ => ⟨gen i, gen_correct i⟩

namespace Slots
abbrev x : Nat := 0
abbrev y : Nat := 1
abbrev square : Nat := 2
abbrev output : Nat := 3

def layout : List Nat := [x, y, square, output]

theorem noAliases : layout.Nodup := by decide
theorem covers : ∀ k : Fin 4, k.val ∈ layout := by decide
end Slots

/-- Exactly four canonical-field Nat cells, backed by an actual Array. -/
abbrev Buffer := Vector Nat 4

theorem buffer_layout : Buffer = Vector Nat Slots.layout.length := rfl

def initial (i : Input) : Buffer := ⟨#[i.x.toNat, i.y.toNat, 0, 0], rfl⟩

/-- A pure writer: only the two reserved internal witness cells are updated. -/
def populate (b : Buffer) (w : Witness) : Buffer :=
  (b.set Slots.square w.square.toNat).set Slots.output w.output.toNat

def Inputs (i : Input) (b : Buffer) : Prop :=
  b[Slots.x] = i.x.toNat ∧ b[Slots.y] = i.y.toNat

def WitnessCells (b : Buffer) (w : Witness) : Prop :=
  b[Slots.square] = w.square.toNat ∧ b[Slots.output] = w.output.toNat

/-- Independent gates on the complete buffer, not equality to a chosen writer.
Input binding and canonical witness ranges forbid modular integer aliases. -/
def Constraints (i : Input) (b : Buffer) : Prop :=
  Inputs i b ∧ b[Slots.square] < 17 ∧ b[Slots.output] < 17 ∧
  b[Slots.square] = (b[Slots.x] * b[Slots.x]) % 17 ∧
  b[Slots.output] = (b[Slots.square] + b[Slots.y]) % 17

instance (i : Input) (b : Buffer) : Decidable (Inputs i b) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (i : Input) (b : Buffer) : Decidable (Constraints i b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem initial_inputs (i : Input) : Inputs i (initial i) := ⟨rfl, rfl⟩

theorem populate_inputs_unchanged (b : Buffer) (w : Witness) :
    (populate b w)[0] = b[0] ∧ (populate b w)[1] = b[1] := by
  simp [populate, Slots.square, Slots.output]

theorem populate_inputs (i : Input) (b : Buffer) (w : Witness) (hb : Inputs i b) :
    Inputs i (populate b w) :=
  ⟨(populate_inputs_unchanged b w).1.trans hb.1,
   (populate_inputs_unchanged b w).2.trans hb.2⟩

theorem populate_witnessCells (b : Buffer) (w : Witness) :
    WitnessCells (populate b w) w := by
  simp [WitnessCells, populate]

theorem constraints_of_cells (i : Input) (b : Buffer) (w : Witness)
    (hb : Inputs i b) (hc : WitnessCells b w) (hw : Relation i w) : Constraints i b := by
  refine ⟨hb, ?_, ?_, ?_, ?_⟩
  · rw [hc.1]
    exact Field17.toNat_lt w.square
  · rw [hc.2]
    exact Field17.toNat_lt w.output
  · simpa only [hc.1, hb.1, Field17.mul_toNat] using
      congrArg Field17.toNat (Field17.mul_sound hw.1)
  · simpa only [hc.2, hc.1, hb.2, Field17.add_toNat] using
      congrArg Field17.toNat (Field17.add_sound hw.2)

theorem populate_constraints (i : Input) (b : Buffer) (w : Witness)
    (hb : Inputs i b) (hw : Relation i w) : Constraints i (populate b w) :=
  constraints_of_cells i _ w (populate_inputs i b w hb) (populate_witnessCells b w) hw

theorem honest_buffer (i : Input) : Constraints i (populate (initial i) (gen i)) :=
  populate_constraints i _ _ (initial_inputs i) (gen_correct i)

/-- Every accepting buffer decodes to the full independently specified relation. -/
theorem constraints_iff (i : Input) (b : Buffer) :
    Constraints i b ↔ Inputs i b ∧ ∃ w, WitnessCells b w ∧ Relation i w := by
  constructor
  · intro h
    let w : Witness := ⟨⟨b[2], h.2.1⟩, ⟨b[3], h.2.2.1⟩⟩
    have hs : w.square = Field17.mul i.x i.x := by
      apply Fin.ext
      change b[2] = (i.x.toNat * i.x.toNat) % 17
      rw [← h.1.1]
      exact h.2.2.2.1
    have ho : w.output = Field17.add w.square i.y := by
      apply Fin.ext
      change b[3] = (b[2] + i.y.toNat) % 17
      rw [← h.1.2]
      exact h.2.2.2.2
    refine ⟨h.1, w, ⟨rfl, rfl⟩, ?_, ?_⟩
    · rw [hs]
      exact Field17.mul_correct _ _
    · rw [ho]
      exact Field17.add_correct _ _
  · rintro ⟨hb, w, hc, hw⟩
    exact constraints_of_cells i b w hb hc hw

theorem constraints_canonical (i : Input) (b : Buffer) (h : Constraints i b) :
    ∀ k : Fin 4, b[k.val] < 17 := by
  intro ⟨k, hk⟩
  match k with
  | 0 => rw [h.1.1]; exact Field17.toNat_lt i.x
  | 1 => rw [h.1.2]; exact Field17.toNat_lt i.y
  | 2 => exact h.2.1
  | 3 => exact h.2.2.1
  | _ + 4 => omega

theorem constraints_sound (i : Input) (b : Buffer) (h : Constraints i b) :
    b[3] = (Field17.add (Field17.mul i.x i.x) i.y).toNat := by
  obtain ⟨_, w, hc, hw⟩ := (constraints_iff i b).1 h
  exact hc.2.trans (congrArg Field17.toNat (sound i w trivial hw))

theorem certified_buffer {S : Type} {F : Signature S} {V : S → Type}
    {M : Model F V} {Γ : List S} {t : S}
    (g : FormalWitgen circuit M Γ t) (i : Input) :
    Constraints i (populate (initial i) (g.generate i)) :=
  populate_constraints i _ _ (initial_inputs i) (g.satisfies i trivial)

theorem swapped_rejected : ¬ Constraints ⟨3, 4⟩ ⟨#[3, 4, 13, 9], rfl⟩ := by decide

/-- The public output is correct, but the required square cell was not written. -/
theorem missing_square_rejected : ¬ Constraints ⟨3, 4⟩ ⟨#[3, 4, 0, 13], rfl⟩ := by decide

theorem alias_rejected : ¬ Constraints ⟨3, 4⟩ ⟨#[3, 4, 26, 13], rfl⟩ := by decide

end Quadratic

namespace ModMul
open Arithmetic

structure Input where
  a : Nat
  b : Nat
  n : Nat
  deriving Repr, DecidableEq

abbrev Witness := MulModWitness

def Assumptions (i : Input) : Prop :=
  0 < i.n ∧ i.n ≤ 16 ∧ i.a < i.n ∧ i.b < i.n

instance (i : Input) : Decidable (Assumptions i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Two field257 gates with a canonical product and reduced quotient/remainder.
The range constraints are essential for lifting the gates to Nat equalities. -/
def Relation (i : Input) (w : Witness) : Prop :=
  w.product < 257 ∧ w.quotient < i.n ∧ w.remainder < i.n ∧
  w.product % 257 = (i.a * i.b) % 257 ∧
  w.product % 257 = (w.quotient * i.n + w.remainder) % 257

instance (i : Input) (w : Witness) : Decidable (Relation i w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def Spec (i : Input) (output : Nat) : Prop := output = (i.a * i.b) % i.n

theorem natRelation (i : Input) (w : Witness) (hi : Assumptions i)
    (h : Relation i w) : MulModRel i.a i.b i.n w :=
  mulModRel_of_field257 hi.2.1 hi.2.2.1 hi.2.2.2
    h.2.1 h.2.2.1 h.1 h.2.2.2.1 h.2.2.2.2

theorem sound (i : Input) (w : Witness) (hi : Assumptions i)
    (h : Relation i w) : Spec i w.remainder :=
  mulMod_sound (natRelation i w hi h)

def circuit : Circuit Input Witness Nat where
  Assumptions := Assumptions
  Relation := Relation
  output := MulModWitness.remainder
  Spec := Spec
  sound := sound

def gen (i : Input) : Witness := genMulMod i.a i.b i.n

theorem gen_correct (i : Input) (hi : Assumptions i) : Relation i (gen i) := by
  have h := genMulMod_correct i.a i.b i.n hi.1
  refine ⟨product_lt_257 hi.2.1 hi.2.2.1 hi.2.2.2, ?_, h.2.2, rfl, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hi.1).2
      (Nat.mul_lt_mul_of_lt_of_lt hi.2.2.1 hi.2.2.2)
  · exact congrArg (fun v => v % 257) h.2.1

theorem mathematicallyComplete : circuit.MathematicallyComplete :=
  fun i hi => ⟨gen i, gen_correct i hi⟩

namespace Slots
abbrev a : Nat := 0
abbrev b : Nat := 1
abbrev n : Nat := 2
abbrev product : Nat := 3
abbrev quotient : Nat := 4
abbrev remainder : Nat := 5

def layout : List Nat := [a, b, n, product, quotient, remainder]

theorem noAliases : layout.Nodup := by decide
theorem covers : ∀ k : Fin 6, k.val ∈ layout := by decide
end Slots

/-- Exactly six Nat cells encoding canonical field257 values when constrained. -/
abbrev Buffer := Vector Nat 6

theorem buffer_layout : Buffer = Vector Nat Slots.layout.length := rfl

def initial (i : Input) : Buffer := ⟨#[i.a, i.b, i.n, 0, 0, 0], rfl⟩

def populate (b : Buffer) (w : Witness) : Buffer :=
  ((b.set Slots.product w.product).set Slots.quotient w.quotient).set Slots.remainder w.remainder

def Inputs (i : Input) (b : Buffer) : Prop :=
  b[Slots.a] = i.a ∧ b[Slots.b] = i.b ∧ b[Slots.n] = i.n

def WitnessCells (b : Buffer) (w : Witness) : Prop :=
  b[Slots.product] = w.product ∧ b[Slots.quotient] = w.quotient ∧
  b[Slots.remainder] = w.remainder

/-- The complete field gates, explicit ranges, and exact input bindings.
The input domain is included, so every satisfying cell is canonical modulo 257. -/
def Constraints (i : Input) (b : Buffer) : Prop :=
  Assumptions i ∧ Inputs i b ∧
  b[Slots.product] < 257 ∧ b[Slots.quotient] < b[Slots.n] ∧
  b[Slots.remainder] < b[Slots.n] ∧
  b[Slots.product] % 257 = (b[Slots.a] * b[Slots.b]) % 257 ∧
  b[Slots.product] % 257 = (b[Slots.quotient] * b[Slots.n] + b[Slots.remainder]) % 257

instance (i : Input) (b : Buffer) : Decidable (Inputs i b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (i : Input) (b : Buffer) : Decidable (Constraints i b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem initial_inputs (i : Input) : Inputs i (initial i) := ⟨rfl, rfl, rfl⟩

theorem populate_inputs_unchanged (b : Buffer) (w : Witness) :
    (populate b w)[0] = b[0] ∧ (populate b w)[1] = b[1] ∧
    (populate b w)[2] = b[2] := by
  simp [populate, Slots.product, Slots.quotient, Slots.remainder]

theorem populate_inputs (i : Input) (b : Buffer) (w : Witness) (hb : Inputs i b) :
    Inputs i (populate b w) :=
  ⟨(populate_inputs_unchanged b w).1.trans hb.1,
   (populate_inputs_unchanged b w).2.1.trans hb.2.1,
   (populate_inputs_unchanged b w).2.2.trans hb.2.2⟩

theorem populate_witnessCells (b : Buffer) (w : Witness) :
    WitnessCells (populate b w) w := by
  simp [WitnessCells, populate, Slots.product, Slots.quotient, Slots.remainder]

theorem constraints_of_cells (i : Input) (b : Buffer) (w : Witness)
    (hi : Assumptions i) (hb : Inputs i b) (hc : WitnessCells b w)
    (hw : Relation i w) : Constraints i b := by
  refine ⟨hi, hb, ?_⟩
  simpa only [Relation, hc.1, hc.2.1, hc.2.2, hb.1, hb.2.1, hb.2.2] using hw

theorem populate_constraints (i : Input) (b : Buffer) (w : Witness)
    (hi : Assumptions i) (hb : Inputs i b) (hw : Relation i w) :
    Constraints i (populate b w) :=
  constraints_of_cells i _ w hi (populate_inputs i b w hb) (populate_witnessCells b w) hw

theorem honest_buffer (i : Input) (hi : Assumptions i) :
    Constraints i (populate (initial i) (gen i)) :=
  populate_constraints i _ _ hi (initial_inputs i) (gen_correct i hi)

theorem constraints_iff (i : Input) (b : Buffer) :
    Constraints i b ↔ Assumptions i ∧ Inputs i b ∧
      ∃ w, WitnessCells b w ∧ Relation i w := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ⟨b[3], b[4], b[5]⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
    simpa only [Relation, h.2.1.1, h.2.1.2.1, h.2.1.2.2] using h.2.2
  · rintro ⟨hi, hb, w, hc, hw⟩
    exact constraints_of_cells i b w hi hb hc hw

theorem constraints_canonical (i : Input) (b : Buffer) (h : Constraints i b) :
    ∀ k : Fin 6, b[k.val] < 257 := by
  obtain ⟨hi, hb, hp, hq, hr, _, _⟩ := h
  have hn : b[2] < 257 := by
    rw [hb.2.2]
    have := hi.2.1
    omega
  intro ⟨k, hk⟩
  match k with
  | 0 =>
    rw [hb.1]
    exact Nat.lt_trans hi.2.2.1 (by simpa only [hb.2.2] using hn)
  | 1 =>
    rw [hb.2.1]
    exact Nat.lt_trans hi.2.2.2 (by simpa only [hb.2.2] using hn)
  | 2 => exact hn
  | 3 => exact hp
  | 4 => exact Nat.lt_trans hq hn
  | 5 => exact Nat.lt_trans hr hn
  | _ + 6 => omega

theorem constraints_sound (i : Input) (b : Buffer) (h : Constraints i b) :
    b[5] = (i.a * i.b) % i.n := by
  obtain ⟨hi, _, w, hc, hw⟩ := (constraints_iff i b).1 h
  exact hc.2.2.trans (sound i w hi hw)

theorem certified_buffer {S : Type} {F : Signature S} {V : S → Type}
    {M : Model F V} {Γ : List S} {t : S}
    (g : FormalWitgen circuit M Γ t) (i : Input) (hi : Assumptions i) :
    Constraints i (populate (initial i) (g.generate i)) :=
  populate_constraints i _ _ hi (initial_inputs i) (g.satisfies i hi)

theorem swapped_rejected :
    ¬ Constraints ⟨15, 15, 16⟩ ⟨#[15, 15, 16, 225, 1, 14], rfl⟩ := by decide

/-- A correct output cannot compensate for an unpopulated product cell. -/
theorem missing_product_rejected :
    ¬ Constraints ⟨15, 15, 16⟩ ⟨#[15, 15, 16, 0, 14, 1], rfl⟩ := by decide

theorem alias_rejected :
    ¬ Constraints ⟨15, 15, 16⟩ ⟨#[15, 15, 16, 482, 14, 1], rfl⟩ := by decide

end ModMul
end Witgen.Circuits
