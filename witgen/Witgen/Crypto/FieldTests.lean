import Witgen.Crypto.Field

open Witgen.Crypto

-- Full-width modulus-boundary inputs, not renamed small-field examples.
example : bn254Modulus =
    21888242871839275222246405745257275088548364400416034343698204186575808495617 := rfl
example : (Residue.add (Residue.ofNat bn254Positive (bn254Modulus - 1))
    (Residue.ofNat bn254Positive 2)).val = 1 := by decide
example : (Residue.mul (Residue.ofNat bn254Positive (bn254Modulus - 1))
    (Residue.ofNat bn254Positive (bn254Modulus - 1))).val = 1 := by decide
example : (Residue.ofNat bn254Positive (2 ^ 128)).val = 2 ^ 128 := by decide
example {p : Nat} (a b : Fin p) :
    (Residue.mul a b).val = a.val * b.val % p := rfl
