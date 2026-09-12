import Witgen.Crypto.Circuit

open Witgen Witgen.Crypto

example {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    QuadCircuit.Relation i ((quadFieldWitgen hp).generate i) :=
  (quadFieldWitgen hp).satisfies i trivial

example {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    QuadCircuit.Relation i ((quadNatWitgen hp).generate i) :=
  (quadNatWitgen hp).satisfies i trivial

example {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    QuadCircuit.populate (QuadCircuit.initial i) ((quadNatWitgen hp).generate i) =
      QuadCircuit.populate (QuadCircuit.initial i) ((quadFieldWitgen hp).generate i) :=
  quad_full_buffer_agrees hp i

example {p : Nat} (i : QuadInput p) (b : QuadCircuit.Buffer) :
    QuadCircuit.Constraints i b ↔ QuadCircuit.Inputs i b ∧
      ∃ w, QuadCircuit.WitnessCells b w ∧ QuadCircuit.Relation i w :=
  QuadCircuit.constraints_iff i b

-- Raw lowering cells already match; no decoder/modulo fixup is allowed.
example {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    encodeRawNat i ((quadraticNat p).eval natModel (encodeNat i)) =
      QuadCircuit.populate (QuadCircuit.initial i) ((quadFieldWitgen hp).generate i) :=
  quad_nat_raw_buffer hp i

-- Retaining the correct public output while corrupting the internal square
-- must be rejected by the independently defined complete-buffer relation.
def boundaryInput : QuadInput bn254Modulus :=
  ⟨Residue.ofNat bn254Positive (bn254Modulus - 1),
   Residue.ofNat bn254Positive (bn254Modulus - 2)⟩
example : ¬ QuadCircuit.Constraints boundaryInput
    ⟨#[bn254Modulus - 1, bn254Modulus - 2, 0, bn254Modulus - 1], rfl⟩ := by decide
example : QuadCircuit.Constraints boundaryInput
    ⟨#[bn254Modulus - 1, bn254Modulus - 2, 1, bn254Modulus - 1], rfl⟩ := by decide
