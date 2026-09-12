import Witgen.Demo
import Witgen.Pipeline
import Witgen.Circuits

set_option autoImplicit false

namespace Witgen.Integration
open Demo Circuits

abbrev FI := Arithmetic.Field17

def quadFieldInput (i : Quadratic.Input) : HList (Val FI) [.scalar, .scalar] :=
  .cons i.x (.cons i.y .nil)

def quadFieldOutput (w : Quad FI) : Quadratic.Witness :=
  ⟨w.square, w.output⟩

theorem quadraticField_generates (i : Quadratic.Input) :
    quadFieldOutput (quadraticField.eval fieldModel (quadFieldInput i)) = Quadratic.gen i := by
  unfold quadFieldInput
  rw [quadraticField_eval]
  rfl

/-- The certificate contains the actual exported typed IR, not a host generator. -/
def quadraticFieldWitgen :
    FormalWitgen Quadratic.circuit fieldModel [.scalar, .scalar] .quad where
  program := quadraticField
  encodeInput := quadFieldInput
  decodeWitness := quadFieldOutput
  correct := by
    intro i _
    change Quadratic.Relation i
      (quadFieldOutput (quadraticField.eval fieldModel (quadFieldInput i)))
    rw [quadraticField_generates]
    exact Quadratic.gen_correct i

theorem quadraticField_buffer (i : Quadratic.Input) :
    Quadratic.Constraints i
      (Quadratic.populate (Quadratic.initial i) (quadraticFieldWitgen.generate i)) :=
  Quadratic.certified_buffer quadraticFieldWitgen i

theorem quadraticField_completeOver :
    CompleteOver Quadratic.circuit fieldModel (t := .quad) quadFieldInput quadFieldOutput :=
  quadraticFieldWitgen.completeOver

def quadNatInput (i : Quadratic.Input) : HList (Val Nat) [.scalar, .scalar] :=
  .cons i.x.toNat (.cons i.y.toNat .nil)

def quadNatOutput (w : Quad Nat) : Quadratic.Witness :=
  ⟨Arithmetic.Field17.ofNat w.square, Arithmetic.Field17.ofNat w.output⟩

def quadWordInput (i : Quadratic.Input) : HList (Val UInt64) [.scalar, .scalar] :=
  .cons (fieldWord i.x) (.cons (fieldWord i.y) .nil)

def quadWordOutput (w : Quad UInt64) : Quadratic.Witness :=
  ⟨Arithmetic.Field17.ofNat w.square.toNat, Arithmetic.Field17.ofNat w.output.toNat⟩

def fieldNatLowering : CertifiedLowering fieldModel natModel (Graph Arithmetic.Field17.toNat) :=
  .ofTemplate fieldModel natModel fieldToNat (Graph Arithmetic.Field17.toNat) fieldToNat_law

/-- The run field is the actual two-step syntax pipeline, not a replacement oracle. -/
def fieldWordPipeline : CertifiedLowering fieldModel wordModel (Graph fieldWord) where
  run := fun p => (p.lower fieldToNat).mapHandler natToWord
  correct := by
    intro Γ t p xs ys hr
    rw [lower_commutes]
    exact Program.eval_lower_related fieldToWord fieldModel wordModel
      (Graph fieldWord) fieldToWord_law p xs ys hr

def quadraticNatWitgen :
    FormalWitgen Quadratic.circuit natModel [.scalar, .scalar] .quad :=
  quadraticFieldWitgen.lower fieldNatLowering quadNatInput quadNatOutput
    (by intro i _; exact ⟨rfl, rfl, trivial⟩)
    (by
      intro x y h
      change Val.map Arithmetic.Field17.toNat x = y at h
      subst y
      change quadFieldOutput x = quadNatOutput (Val.map Arithmetic.Field17.toNat x)
      simp only [quadFieldOutput, quadNatOutput, Val.map, Arithmetic.Field17.ofNat_toNat])

def quadraticWordWitgen :
    FormalWitgen Quadratic.circuit wordModel [.scalar, .scalar] .quad :=
  quadraticFieldWitgen.lower fieldWordPipeline quadWordInput quadWordOutput
    (by intro i _; exact ⟨rfl, rfl, trivial⟩)
    (by
      intro x y h
      change Val.map fieldWord x = y at h
      subst y
      change quadFieldOutput x = quadWordOutput (Val.map fieldWord x)
      simp only [quadFieldOutput, quadWordOutput, Val.map,
        fieldWord_toNat, Arithmetic.Field17.ofNat_toNat])

theorem quadraticNat_program : quadraticNatWitgen.program = quadraticNat := rfl
theorem quadraticWord_program : quadraticWordWitgen.program = quadraticWord := rfl

theorem quadraticWord_buffer (i : Quadratic.Input) :
    Quadratic.Constraints i
      (Quadratic.populate (Quadratic.initial i) (quadraticWordWitgen.generate i)) :=
  Quadratic.certified_buffer quadraticWordWitgen i

theorem quadraticNat_buffer (i : Quadratic.Input) :
    Quadratic.Constraints i
      (Quadratic.populate (Quadratic.initial i) (quadraticNatWitgen.generate i)) :=
  Quadratic.certified_buffer quadraticNatWitgen i

/-- Explicit bounds ensure the native checked output conversion succeeds. -/
theorem quadraticNat_canonical (i : Quadratic.Input) :
    (quadraticNat.eval natModel (quadNatInput i)).square < 17 ∧
    (quadraticNat.eval natModel (quadNatInput i)).output < 17 := by
  unfold quadNatInput
  rw [quadraticNat_correct]
  exact ⟨(Arithmetic.Field17.mul i.x i.x).isLt,
    (Arithmetic.Field17.add (Arithmetic.Field17.mul i.x i.x) i.y).isLt⟩

def modMulNatInput (i : Circuits.ModMul.Input) :
    HList (Val Nat) [.scalar, .scalar, .scalar] :=
  .cons i.a (.cons i.b (.cons i.n .nil))

def modMulWordInput (i : Circuits.ModMul.Input) :
    HList (Val UInt64) [.scalar, .scalar, .scalar] :=
  .cons (UInt64.ofNat i.a) (.cons (UInt64.ofNat i.b) (.cons (UInt64.ofNat i.n) .nil))

def modMulWordOutput (w : Demo.ModMul UInt64) : Circuits.ModMul.Witness :=
  (Val.map UInt64.toNat (t := .modmul) w).toArithmetic

theorem modMulNat_generates (i : Circuits.ModMul.Input) :
    (modMulNat.eval natModel (modMulNatInput i)).toArithmetic = Circuits.ModMul.gen i := rfl

theorem modMulWord_generates (i : Circuits.ModMul.Input) (hi : Circuits.ModMul.Assumptions i) :
    modMulWordOutput (modMulWord.eval wordModel (modMulWordInput i)) = Circuits.ModMul.gen i := by
  have hn : Arithmetic.SmallModulus i.n :=
    ⟨hi.1, Nat.le_trans hi.2.1 (by decide)⟩
  unfold modMulWordOutput modMulWordInput
  rw [modMulWord_small_correct hn hi.2.2.1 hi.2.2.2]
  rfl

def modMulNatWitgen :
    FormalWitgen Circuits.ModMul.circuit natModel [.scalar, .scalar, .scalar] .modmul where
  program := modMulNat
  encodeInput := modMulNatInput
  decodeWitness := Demo.ModMul.toArithmetic
  correct := by
    intro i hi
    change Circuits.ModMul.Relation i ((modMulNat.eval natModel (modMulNatInput i)).toArithmetic)
    rw [modMulNat_generates]
    exact Circuits.ModMul.gen_correct i hi

def modMulWordWitgen :
    FormalWitgen Circuits.ModMul.circuit wordModel [.scalar, .scalar, .scalar] .modmul where
  program := modMulWord
  encodeInput := modMulWordInput
  decodeWitness := modMulWordOutput
  correct := by
    intro i hi
    change Circuits.ModMul.Relation i (modMulWordOutput (modMulWord.eval wordModel (modMulWordInput i)))
    rw [modMulWord_generates i hi]
    exact Circuits.ModMul.gen_correct i hi

theorem modMulNat_buffer (i : Circuits.ModMul.Input) (hi : Circuits.ModMul.Assumptions i) :
    Circuits.ModMul.Constraints i
      (Circuits.ModMul.populate (Circuits.ModMul.initial i) (modMulNatWitgen.generate i)) :=
  Circuits.ModMul.certified_buffer modMulNatWitgen i hi

theorem modMulWord_buffer (i : Circuits.ModMul.Input) (hi : Circuits.ModMul.Assumptions i) :
    Circuits.ModMul.Constraints i
      (Circuits.ModMul.populate (Circuits.ModMul.initial i) (modMulWordWitgen.generate i)) :=
  Circuits.ModMul.certified_buffer modMulWordWitgen i hi

end Witgen.Integration
