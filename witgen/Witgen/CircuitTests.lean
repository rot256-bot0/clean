import Witgen.Circuits

#check Witgen.Circuits.Quadratic.buffer_layout
#check Witgen.Circuits.ModMul.buffer_layout

set_option autoImplicit false

namespace Witgen.CircuitTests
open Witgen Circuits

namespace Generic

def identityCircuit : Circuit Nat Nat Nat where
  Assumptions := fun _ => True
  Relation := fun i w => w = i
  output := id
  Spec := fun i o => o = i
  sound := fun _ _ _ h => h

def NoFeatures : Signature Unit := fun _ _ _ => Empty
abbrev Values : Unit → Type := fun _ => Nat

def model : Model NoFeatures Values where
  eval := fun op => nomatch op

def generator : FormalWitgen identityCircuit model [()] () where
  program := .ret .zero
  encodeInput := fun i => .cons i .nil
  decodeWitness := id
  correct := fun _ _ => rfl

example (i : Nat) : generator.generate i = i := rfl
example (i : Nat) : identityCircuit.Relation i (generator.generate i) :=
  generator.satisfies i trivial
example : CompleteOver identityCircuit model generator.encodeInput generator.decodeWitness :=
  generator.completeOver
example : identityCircuit.MathematicallyComplete := generator.mathematicallyComplete

def identityLowering : CertifiedLowering model model (fun _ x y => x = y) where
  run := id
  correct := by
    intro Γ t p xs ys h
    have heq : xs = ys := by
      clear p
      induction xs with
      | nil => cases ys; rfl
      | cons x xs ih =>
        cases ys with
        | cons y ys =>
          obtain ⟨rfl, ht⟩ := h
          rw [ih ys ht]
    cases heq
    rfl

def transported : FormalWitgen identityCircuit model [()] () :=
  generator.lower identityLowering generator.encodeInput id
    (fun _ _ => ⟨rfl, trivial⟩) (fun _ _ h => h)

example (i : Nat) : transported.generate i = generator.generate i :=
  generator.lower_generate identityLowering generator.encodeInput id
    (fun _ _ => ⟨rfl, trivial⟩) (fun _ _ h => h) i trivial

def incrementCircuit : Circuit Nat Nat Nat where
  Assumptions := fun _ => True
  Relation := fun i w => w = i + 1
  output := id
  Spec := fun i o => o = i + 1
  sound := fun _ _ _ h => h

def plainInput (i : Nat) : HList Values [()] := .cons i .nil
def plainOutput (n : Values ()) : Nat := n

/-- Fixed ABI: an empty feature program cannot hide arithmetic in an adapter. -/
theorem no_hidden_arithmetic :
    ¬ CompleteOver incrementCircuit model plainInput plainOutput := by
  rintro ⟨p, h⟩
  have h0 := h 0 trivial
  cases p with
  | ret r =>
    cases r with
    | zero => simp [Program.eval, Var.get, plainInput, plainOutput, incrementCircuit] at h0
    | succ r => cases r
  | let_ op _ _ _ => cases op

#print axioms no_hidden_arithmetic

end Generic

namespace QuadraticTests
open Arithmetic

example (i : Quadratic.Input) : Quadratic.Relation i (Quadratic.gen i) :=
  Quadratic.gen_correct i
example (i : Quadratic.Input) (w : Quadratic.Witness)
    (h : Quadratic.Relation i w) :
    w.output = Field17.add (Field17.mul i.x i.x) i.y :=
  Quadratic.sound i w trivial h
example : Quadratic.circuit.MathematicallyComplete := Quadratic.mathematicallyComplete
example : Quadratic.gen ⟨3, 4⟩ = ⟨9, 13⟩ := rfl
example : Quadratic.gen ⟨16, 16⟩ = ⟨1, 0⟩ := rfl

end QuadraticTests

namespace QuadraticBufferTests
open Quadratic

example (b : Buffer) (w : Witness) :
    (populate b w)[0] = b[0] ∧ (populate b w)[1] = b[1] :=
  populate_inputs_unchanged b w
example (b : Buffer) (w : Witness) : WitnessCells (populate b w) w :=
  populate_witnessCells b w
example (i : Input) (b : Buffer) (w : Witness)
    (hb : Inputs i b) (hw : Relation i w) : Constraints i (populate b w) :=
  populate_constraints i b w hb hw
example (i : Input) : Constraints i (populate (initial i) (gen i)) :=
  honest_buffer i
example : (populate (initial ⟨3, 4⟩) (gen ⟨3, 4⟩)).toArray = #[3, 4, 9, 13] := rfl
example : ¬ Constraints ⟨3, 4⟩ ⟨#[3, 4, 13, 9], rfl⟩ := swapped_rejected
example : ¬ Constraints ⟨3, 4⟩ ⟨#[3, 4, 0, 13], rfl⟩ := missing_square_rejected
example : ¬ Constraints ⟨3, 4⟩ ⟨#[3, 4, 26, 13], rfl⟩ := alias_rejected

end QuadraticBufferTests

namespace ModMulTests

example (i : ModMul.Input) (hi : ModMul.Assumptions i) :
    ModMul.Relation i (ModMul.gen i) := ModMul.gen_correct i hi
example (i : ModMul.Input) (w : ModMul.Witness)
    (hi : ModMul.Assumptions i) (h : ModMul.Relation i w) :
    Arithmetic.MulModRel i.a i.b i.n w := ModMul.natRelation i w hi h
example (i : ModMul.Input) (w : ModMul.Witness)
    (hi : ModMul.Assumptions i) (h : ModMul.Relation i w) :
    w.remainder = (i.a * i.b) % i.n := ModMul.sound i w hi h
example : ModMul.circuit.MathematicallyComplete := ModMul.mathematicallyComplete
example : ModMul.gen ⟨15, 15, 16⟩ = ⟨225, 14, 1⟩ := rfl
example : ModMul.Relation ⟨0, 0, 1⟩ (ModMul.gen ⟨0, 0, 1⟩) :=
  ModMul.gen_correct _ (by decide)
example : ¬ ModMul.Assumptions ⟨1, 1, 0⟩ := by decide
example : ¬ ModMul.Assumptions ⟨16, 16, 17⟩ := by decide
example : ¬ ModMul.Relation ⟨15, 15, 16⟩ ⟨482, 14, 1⟩ := by decide

end ModMulTests

namespace ModMulBufferTests
open ModMul

example (b : Buffer) (w : Witness) :
    (populate b w)[0] = b[0] ∧ (populate b w)[1] = b[1] ∧
    (populate b w)[2] = b[2] := populate_inputs_unchanged b w
example (b : Buffer) (w : Witness) : WitnessCells (populate b w) w :=
  populate_witnessCells b w
example (i : Input) (b : Buffer) (w : Witness)
    (hi : Assumptions i) (hb : Inputs i b) (hw : Relation i w) :
    Constraints i (populate b w) := populate_constraints i b w hi hb hw
example (i : Input) (hi : Assumptions i) :
    Constraints i (populate (initial i) (gen i)) := honest_buffer i hi
example : (populate (initial ⟨15, 15, 16⟩) (gen ⟨15, 15, 16⟩)).toArray =
    #[15, 15, 16, 225, 14, 1] := rfl
example : ¬ Constraints ⟨15, 15, 16⟩ ⟨#[15, 15, 16, 225, 1, 14], rfl⟩ := swapped_rejected
example : ¬ Constraints ⟨15, 15, 16⟩ ⟨#[15, 15, 16, 0, 14, 1], rfl⟩ := missing_product_rejected
example : ¬ Constraints ⟨15, 15, 16⟩ ⟨#[15, 15, 16, 482, 14, 1], rfl⟩ := alias_rejected
example : ¬ Constraints ⟨0, 0, 16⟩ ⟨#[0, 0, 16, 0, 16, 1], rfl⟩ := by decide

end ModMulBufferTests

namespace CorrespondenceTests

example (i : Quadratic.Input) (b : Quadratic.Buffer) :
    Quadratic.Constraints i b ↔ Quadratic.Inputs i b ∧
      ∃ w, Quadratic.WitnessCells b w ∧ Quadratic.Relation i w :=
  Quadratic.constraints_iff i b
example (i : Quadratic.Input) (b : Quadratic.Buffer) (h : Quadratic.Constraints i b) :
    ∀ k : Fin 4, b[k.val] < 17 := Quadratic.constraints_canonical i b h
example (i : Quadratic.Input) (b : Quadratic.Buffer) (h : Quadratic.Constraints i b) :
    b[3] = (Arithmetic.Field17.add (Arithmetic.Field17.mul i.x i.x) i.y).toNat :=
  Quadratic.constraints_sound i b h
example (i : ModMul.Input) (b : ModMul.Buffer) :
    ModMul.Constraints i b ↔ ModMul.Assumptions i ∧ ModMul.Inputs i b ∧
      ∃ w, ModMul.WitnessCells b w ∧ ModMul.Relation i w :=
  ModMul.constraints_iff i b
example (i : ModMul.Input) (b : ModMul.Buffer) (h : ModMul.Constraints i b) :
    ∀ k : Fin 6, b[k.val] < 257 := ModMul.constraints_canonical i b h
example (i : ModMul.Input) (b : ModMul.Buffer) (h : ModMul.Constraints i b) :
    b[5] = (i.a * i.b) % i.n := ModMul.constraints_sound i b h

example {S : Type} {F : Signature S} {V : S → Type} {M : Model F V}
    {Γ : List S} {t : S} (g : FormalWitgen Quadratic.circuit M Γ t)
    (i : Quadratic.Input) :
    Quadratic.Constraints i (Quadratic.populate (Quadratic.initial i) (g.generate i)) :=
  Quadratic.certified_buffer g i
example {S : Type} {F : Signature S} {V : S → Type} {M : Model F V}
    {Γ : List S} {t : S} (g : FormalWitgen ModMul.circuit M Γ t)
    (i : ModMul.Input) (hi : ModMul.Assumptions i) :
    ModMul.Constraints i (ModMul.populate (ModMul.initial i) (g.generate i)) :=
  ModMul.certified_buffer g i hi

end CorrespondenceTests

-- Executed examples, distinct from the kernel-checked universal theorems above.
#eval (Quadratic.populate (Quadratic.initial ⟨3, 4⟩) (Quadratic.gen ⟨3, 4⟩)).toArray
#eval (ModMul.populate (ModMul.initial ⟨15, 15, 16⟩) (ModMul.gen ⟨15, 15, 16⟩)).toArray

#print axioms FormalWitgen.spec
#print axioms FormalWitgen.mathematicallyComplete
#print axioms FormalWitgen.completeOver
#print axioms FormalWitgen.lower
#print axioms FormalWitgen.lower_generate
#print axioms Quadratic.sound
#print axioms Quadratic.gen_correct
#print axioms Quadratic.mathematicallyComplete
#print axioms Quadratic.populate_inputs_unchanged
#print axioms Quadratic.populate_witnessCells
#print axioms Quadratic.populate_constraints
#print axioms Quadratic.constraints_iff
#print axioms Quadratic.constraints_canonical
#print axioms Quadratic.constraints_sound
#print axioms Quadratic.honest_buffer
#print axioms Quadratic.certified_buffer
#print axioms Quadratic.swapped_rejected
#print axioms Quadratic.missing_square_rejected
#print axioms Quadratic.alias_rejected
#print axioms ModMul.natRelation
#print axioms ModMul.sound
#print axioms ModMul.gen_correct
#print axioms ModMul.mathematicallyComplete
#print axioms ModMul.populate_inputs_unchanged
#print axioms ModMul.populate_witnessCells
#print axioms ModMul.populate_constraints
#print axioms ModMul.constraints_iff
#print axioms ModMul.constraints_canonical
#print axioms ModMul.constraints_sound
#print axioms ModMul.honest_buffer
#print axioms ModMul.certified_buffer
#print axioms ModMul.swapped_rejected
#print axioms ModMul.missing_product_rejected
#print axioms ModMul.alias_rejected

end Witgen.CircuitTests
