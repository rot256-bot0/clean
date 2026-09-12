import Std

namespace Witgen.U64

abbrev radix : Nat := 2^64
abbrev capacity : Nat := 2^256

def bit (b : Bool) : Nat := if b then 1 else 0

theorem bit_le (b : Bool) : bit b ≤ 1 := by cases b <;> decide

/-- Concrete wrapping word addition and overflow comparison. -/
def addc (a b : UInt64) : UInt64 × Bool :=
  let s := a + b
  (s, decide (s < a))

/-- Concrete wrapping word subtraction and unsigned borrow comparison. -/
def subb (a b : UInt64) : UInt64 × Bool :=
  (a - b, decide (a < b))

def adc (a b : UInt64) (c : Bool) : UInt64 × Bool :=
  let s := addc a b
  let t := addc s.1 (if c then 1 else 0)
  (t.1, s.2 || t.2)

def sbb (a b : UInt64) (c : Bool) : UInt64 × Bool :=
  let s := subb a b
  let t := subb s.1 (if c then 1 else 0)
  (t.1, s.2 || t.2)

theorem addc_correct (a b : UInt64) :
    (addc a b).1.toNat + radix * bit (addc a b).2 = a.toNat + b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [addc, UInt64.toNat_add, bit, radix, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  split <;> omega

theorem subb_correct (a b : UInt64) :
    (subb a b).1.toNat + b.toNat = a.toNat + radix * bit (subb a b).2 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [subb, UInt64.toNat_sub, bit, radix, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
  split <;> omega

theorem bit_or (a b : Bool) (h : bit a + bit b ≤ 1) :
    bit (a || b) = bit a + bit b := by
  cases a <;> cases b <;> simp_all [bit]

theorem toNat_bit (c : Bool) : (if c then (1 : UInt64) else 0).toNat = bit c := by
  cases c <;> rfl

theorem adc_correct (a b : UInt64) (c : Bool) :
    (adc a b c).1.toNat + radix * bit (adc a b c).2 =
      a.toNat + b.toNat + bit c := by
  have h₁ := addc_correct a b
  have h₂ := addc_correct (addc a b).1 (if c then 1 else 0)
  rw [toNat_bit] at h₂
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := bit_le c
  have hsum : bit (addc a b).2 +
      bit (addc (addc a b).1 (if c then 1 else 0)).2 ≤ 1 := by
    simp only [radix] at h₁ h₂
    omega
  simp only [adc, bit_or _ _ hsum, Nat.mul_add]
  simp only [radix] at h₁ h₂ ⊢
  omega

theorem sbb_correct (a b : UInt64) (c : Bool) :
    (sbb a b c).1.toNat + b.toNat + bit c =
      a.toNat + radix * bit (sbb a b c).2 := by
  have h₁ := subb_correct a b
  have h₂ := subb_correct (subb a b).1 (if c then 1 else 0)
  rw [toNat_bit] at h₂
  have hb := b.toNat_lt
  have ht := (subb (subb a b).1 (if c then 1 else 0)).1.toNat_lt
  have hc := bit_le c
  have hsum : bit (subb a b).2 +
      bit (subb (subb a b).1 (if c then 1 else 0)).2 ≤ 1 := by
    simp only [radix] at h₁ h₂
    omega
  simp only [sbb, bit_or _ _ hsum, Nat.mul_add]
  simp only [radix] at h₁ h₂ ⊢
  omega

end Witgen.U64
