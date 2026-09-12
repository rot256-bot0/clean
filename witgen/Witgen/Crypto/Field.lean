import Witgen.Core

/-! Canonical modular arithmetic, generic in a positive modulus. This file does
not assert primality or provide an algebraic `Field` instance. BN254's parameter
is sourced from arkworks 0.4.0 `fields/fr.rs`, not its different base-field prime:
https://docs.rs/ark-bn254/0.4.0/src/ark_bn254/fields/fr.rs.html . -/
namespace Witgen.Crypto

/-- BN254 scalar modulus (arkworks `Fr`, not `Fq`). -/
def bn254Modulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

theorem bn254Positive : 0 < bn254Modulus := by decide

abbrev BN254 := Fin bn254Modulus

namespace Residue

def ofNat {p : Nat} (hp : 0 < p) (n : Nat) : Fin p := ⟨n % p, Nat.mod_lt n hp⟩

def add {p : Nat} (a b : Fin p) : Fin p :=
  ofNat (Nat.zero_lt_of_lt a.isLt) (a.val + b.val)

def mul {p : Nat} (a b : Fin p) : Fin p :=
  ofNat (Nat.zero_lt_of_lt a.isLt) (a.val * b.val)

@[simp] theorem ofNat_val {p : Nat} (hp : 0 < p) (n : Nat) :
    (ofNat hp n).val = n % p := rfl
@[simp] theorem add_val {p : Nat} (a b : Fin p) :
    (add a b).val = (a.val + b.val) % p := rfl
@[simp] theorem mul_val {p : Nat} (a b : Fin p) :
    (mul a b).val = (a.val * b.val) % p := rfl
@[simp] theorem ofNat_val_id {p : Nat} (hp : 0 < p) (a : Fin p) :
    ofNat hp a.val = a := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt a.isLt

end Residue
end Witgen.Crypto
