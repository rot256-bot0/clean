import Witgen.Typed.FieldInverses

open Witgen.Typed
example (f : FieldId) : Nat.Prime (modulus f) := modulus_prime f
example : Residue.inv (Residue.ofNat (by decide : 0 < 7) 0) = Residue.ofNat (by decide) 0 := Residue.inv_zero _
example : Residue.mul (Residue.ofNat (by decide : 0 < 7) 3)
    (Residue.inv (Residue.ofNat (by decide : 0 < 7) 3)) = Residue.ofNat (by decide) 1 :=
  Residue.mul_inv_of_prime (by decide) _ (by decide)
example : Residue.add (Residue.ofNat (by decide : 0 < 7) 3)
    (Residue.neg (Residue.ofNat (by decide : 0 < 7) 3)) = Residue.ofNat (by decide) 0 := by decide
example (f : FieldId) (a : FieldValue f) (h : a.val ≠ 0) :
    Residue.mul a (Residue.inv a) = Residue.ofNat (modulus_pos f) 1 :=
  Residue.mul_inv f a h
