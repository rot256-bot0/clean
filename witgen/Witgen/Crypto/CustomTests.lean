import Witgen.Crypto.Custom

open Witgen Witgen.Crypto

example {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    (envelopeField.eval (fieldModel hp) (encodeField i)).trace =
      (quadFieldWitgen hp).generate i := envelopeField_trace hp i

example {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    encodeRawNat i (((envelopeNat p).eval natModel (encodeNat i)).trace) =
      QuadCircuit.populate (QuadCircuit.initial i) ((quadFieldWitgen hp).generate i) :=
  envelopeNat_raw_buffer hp i

example : (((envelopeNat bn254Modulus).eval natModel
    (.cons (bn254Modulus - 1) (.cons (bn254Modulus - 2) .nil))).trace).square = 1 := by decide
