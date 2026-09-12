import Witgen.U64.Primitives

namespace Witgen.U64

/-- Little-endian, fixed four-limb representation. -/
structure Word4 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  deriving DecidableEq, Repr

namespace Word4

/-- Reference/proof model. Not called by executable field arithmetic. -/
def decode (a : Word4) : Nat :=
  a.l0.toNat + radix * a.l1.toNat + radix^2 * a.l2.toNat + radix^3 * a.l3.toNat

/-- ABI/reference conversion, not an arithmetic implementation. -/
def encode (n : Nat) : Word4 :=
  ⟨UInt64.ofNat n, UInt64.ofNat (n / radix), UInt64.ofNat (n / radix^2),
    UInt64.ofNat (n / radix^3)⟩

def Canonical (p : Nat) (a : Word4) : Prop := a.decode < p

theorem decode_lt (a : Word4) : a.decode < capacity := by
  have h0 := a.l0.toNat_lt
  have h1 := a.l1.toNat_lt
  have h2 := a.l2.toNat_lt
  have h3 := a.l3.toNat_lt
  simp only [decode, radix, capacity]
  omega

theorem decode_encode (n : Nat) : (encode n).decode = n % capacity := by
  simp only [encode, decode, UInt64.toNat_ofNat', radix, capacity]
  omega

theorem decode_encode_of_lt {n : Nat} (h : n < capacity) : (encode n).decode = n := by
  rw [decode_encode, Nat.mod_eq_of_lt h]

def zero : Word4 := ⟨0, 0, 0, 0⟩

@[simp] theorem decode_zero : zero.decode = 0 := rfl

def addCarry (a b : Word4) : Word4 × Bool :=
  let s0 := adc a.l0 b.l0 false
  let s1 := adc a.l1 b.l1 s0.2
  let s2 := adc a.l2 b.l2 s1.2
  let s3 := adc a.l3 b.l3 s2.2
  (⟨s0.1, s1.1, s2.1, s3.1⟩, s3.2)

def subBorrow (a b : Word4) : Word4 × Bool :=
  let s0 := sbb a.l0 b.l0 false
  let s1 := sbb a.l1 b.l1 s0.2
  let s2 := sbb a.l2 b.l2 s1.2
  let s3 := sbb a.l3 b.l3 s2.2
  (⟨s0.1, s1.1, s2.1, s3.1⟩, s3.2)

theorem addCarry_correct (a b : Word4) :
    (addCarry a b).1.decode + capacity * bit (addCarry a b).2 = a.decode + b.decode := by
  have h0 := adc_correct a.l0 b.l0 false
  have h1 := adc_correct a.l1 b.l1 (adc a.l0 b.l0 false).2
  have h2 := adc_correct a.l2 b.l2 (adc a.l1 b.l1 (adc a.l0 b.l0 false).2).2
  have h3 := adc_correct a.l3 b.l3
    (adc a.l2 b.l2 (adc a.l1 b.l1 (adc a.l0 b.l0 false).2).2).2
  simp only [addCarry, decode, capacity, radix]
  simp only [radix, show bit false = 0 from rfl] at h0
  simp only [radix] at h1 h2 h3
  omega

theorem subBorrow_correct (a b : Word4) :
    (subBorrow a b).1.decode + b.decode = a.decode + capacity * bit (subBorrow a b).2 := by
  have h0 := sbb_correct a.l0 b.l0 false
  have h1 := sbb_correct a.l1 b.l1 (sbb a.l0 b.l0 false).2
  have h2 := sbb_correct a.l2 b.l2 (sbb a.l1 b.l1 (sbb a.l0 b.l0 false).2).2
  have h3 := sbb_correct a.l3 b.l3
    (sbb a.l2 b.l2 (sbb a.l1 b.l1 (sbb a.l0 b.l0 false).2).2).2
  simp only [subBorrow, decode, capacity, radix]
  simp only [radix, show bit false = 0 from rfl] at h0
  simp only [radix] at h1 h2 h3
  omega

/-- Correct also when the unreduced sum overflows all four limbs. -/
def Add (p a b : Word4) : Word4 :=
  let s := addCarry a b
  let d := subBorrow s.1 p
  if s.2 || !d.2 then d.1 else s.1

/-- The arithmetic fact behind the carry-or-no-borrow selection rule.
No assumption that x+y fits in 256 bits (or that p < 2^255). -/
theorem reduce_once {P X Y S D C : Nat} {carry borrow : Bool}
    (_hp : 0 < P) (hpC : P < C) (hx : X < P) (hy : Y < P)
    (hS : S + C * bit carry = X + Y)
    (hD : D + P = S + C * bit borrow) (hdC : D < C) :
    (if carry || !borrow then D else S) = (X + Y) % P ∧
      (if carry || !borrow then D else S) < P := by
  cases carry <;> cases borrow <;> simp only [bit, Bool.false_eq_true,
    ↓reduceIte, Bool.not_false, Bool.not_true,
    Bool.false_or, Bool.true_or, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at *
  · have hd : D < P := by omega
    have he : X + Y = D + P := by omega
    exact ⟨by rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hd], hd⟩
  · have hs : S < P := by omega
    have he : X + Y = S := by omega
    exact ⟨by rw [he, Nat.mod_eq_of_lt hs], hs⟩
  · omega
  · have hd : D < P := by omega
    have he : X + Y = D + P := by omega
    exact ⟨by rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hd], hd⟩

theorem Add_correct (p a b : Word4) (hp : 0 < p.decode)
    (ha : Canonical p.decode a) (hb : Canonical p.decode b) :
    (Add p a b).decode = (a.decode + b.decode) % p.decode ∧
      Canonical p.decode (Add p a b) := by
  have h := reduce_once hp (decode_lt p) ha hb
    (addCarry_correct a b) (subBorrow_correct (addCarry a b).1 p)
    (decode_lt (subBorrow (addCarry a b).1 p).1)
  simpa only [Add, Canonical, apply_ite decode] using h

end Word4
end Witgen.U64
