import Witgen.Typed.Types
import Witgen.PrimeCertificates
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

namespace Witgen.Typed

theorem modulus_prime (f : FieldId) : Nat.Prime (modulus f) := by
  fin_cases f
  · exact PrimeCertificates.bn254Scalar_prime
  · exact PrimeCertificates.secpBase_prime
  · exact PrimeCertificates.secpScalar_prime

/-- Mathematical modular inverse on natural representatives. -/
def inverseNat (p a : Nat) : Nat := ((a : ZMod p)⁻¹).val

namespace Residue

def neg {p : Nat} (a : Fin p) : Fin p :=
  ofNat (Nat.zero_lt_of_lt a.isLt) (p - a.val)

def sub {p : Nat} (a b : Fin p) : Fin p := add a (neg b)

theorem sub_eq_add_neg {p : Nat} (a b : Fin p) : sub a b = add a (neg b) := rfl

@[simp] theorem sub_val {p : Nat} (a b : Fin p) :
    (sub a b).val = (a.val + p - b.val) % p := by
  simp only [sub, add, neg, ofNat]
  rw [Nat.add_mod_mod, Nat.add_sub_assoc (Nat.le_of_lt b.isLt)]

theorem sub_self {p : Nat} (a : Fin p) :
    sub a a = ofNat (Nat.zero_lt_of_lt a.isLt) 0 := by
  apply Fin.ext
  simp [sub_val, ofNat]

def inv {p : Nat} (a : Fin p) : Fin p :=
  letI : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt a.isLt)⟩
  ⟨inverseNat p a.val, ZMod.val_lt _⟩

@[simp] theorem inv_val {p : Nat} (a : Fin p) : (inv a).val = inverseNat p a.val := rfl

@[simp] theorem inv_zero {p : Nat} (hp : 0 < p) : inv (ofNat hp 0) = ofNat hp 0 := by
  apply Fin.ext
  simp [inv, inverseNat, ofNat, ZMod.inv_zero]

theorem add_neg {p : Nat} (a : Fin p) : add a (neg a) = ofNat (Nat.zero_lt_of_lt a.isLt) 0 := by
  apply Fin.ext
  simp only [add, neg, ofNat]
  rw [Nat.add_mod_mod, Nat.add_sub_of_le (Nat.le_of_lt a.isLt)]
  simp

theorem mul_inv_of_prime {p : Nat} (hp : Nat.Prime p) (a : Fin p) (h : a.val ≠ 0) :
    mul a (inv a) = ofNat hp.pos 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have ha : (a.val : ZMod p) ≠ 0 := by
    intro hz
    have hh := congrArg ZMod.val hz
    exact h (by simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt] using hh)
  have hx := congrArg ZMod.val (mul_inv_cancel₀ ha)
  apply Fin.ext
  simpa [mul, inv, inverseNat, ofNat, ZMod.val_mul, ZMod.val_natCast, ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt a.isLt] using hx

theorem mul_inv (f : FieldId) (a : FieldValue f) (h : a.val ≠ 0) :
    mul a (inv a) = ofNat (modulus_pos f) 1 := mul_inv_of_prime (modulus_prime f) a h

end Residue
end Witgen.Typed
