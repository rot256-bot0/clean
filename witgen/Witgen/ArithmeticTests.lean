import Witgen.Arithmetic

set_option autoImplicit false

namespace Witgen.Arithmetic.Tests

-- Slice 1: canonical residues and the independently stated Nat congruence.
example (a : Nat) : (Field17.ofNat a).toNat < 17 :=
  Field17.toNat_lt _

example (a b : Nat) :
    (Field17.add (Field17.ofNat a) (Field17.ofNat b)).toNat = (a + b) % 17 :=
  Field17.add_ofNat_toNat a b

example (a b : Nat) :
    (Field17.mul (Field17.ofNat a) (Field17.ofNat b)).toNat = (a * b) % 17 :=
  Field17.mul_ofNat_toNat a b

example : (Field17.add (Field17.ofNat 16) (Field17.ofNat 3)).toNat = 2 := by decide
example : (Field17.mul (Field17.ofNat 16) (Field17.ofNat 16)).toNat = 1 := by decide

example (a b : Field17) : Field17.AddRel a b (Field17.add a b) :=
  Field17.add_correct a b
example (a b : Field17) : Field17.MulRel a b (Field17.mul a b) :=
  Field17.mul_correct a b

-- Slice 2: bounded, lossless word arithmetic; divisors must be positive.
example (n : Nat) (hn : FitsU64 n) : (UInt64.ofNat n).toNat = n :=
  u64_ofNat_toNat hn

example (a b : Nat) (ha : FitsU64 a) (hb : FitsU64 b) (hs : FitsU64 (a + b)) :
    (UInt64.ofNat a + UInt64.ofNat b).toNat = a + b :=
  u64_add_toNat ha hb hs

example (a b : Nat) (ha : FitsU64 a) (hb : FitsU64 b) (hp : FitsU64 (a * b)) :
    (UInt64.ofNat a * UInt64.ofNat b).toNat = a * b :=
  u64_mul_toNat ha hb hp

example (a b : Nat) (ha : FitsU64 a) (hb : FitsU64 b) (hpos : 0 < b) :
    (UInt64.ofNat a / UInt64.ofNat b).toNat = a / b :=
  u64_div_toNat ha hb hpos

example (a b : Nat) (ha : FitsU64 a) (hb : FitsU64 b) (hpos : 0 < b) :
    (UInt64.ofNat a % UInt64.ofNat b).toNat = a % b :=
  u64_mod_toNat ha hb hpos

example (b : Nat) (hb : FitsU64 b) (hpos : 0 < b) : UInt64.ofNat b ≠ 0 :=
  u64_ofNat_ne_zero hb hpos

example : (UInt64.ofNat 16 * UInt64.ofNat 16).toNat = 256 :=
  u64_mul_toNat (by decide) (by decide) (by decide)
example : (UInt64.ofNat 256 / UInt64.ofNat 17).toNat = 15 :=
  u64_div_toNat (by decide) (by decide) (by decide)
example : (UInt64.ofNat 256 % UInt64.ofNat 17).toNat = 1 :=
  u64_mod_toNat (by decide) (by decide) (by decide)

-- No accidental claim that all Nat values are losslessly representable.
example (a : Nat) (ha : UInt64.size ≤ a) : (UInt64.ofNat a).toNat ≠ a :=
  u64_ofNat_not_exact ha

-- Slice 3: the full witness relation is independent of its generator.
example (a b n : Nat) (hn : 0 < n) : MulModRel a b n (genMulMod a b n) :=
  genMulMod_correct a b n hn

example (a b n : Nat) (w : MulModWitness) (h : MulModRel a b n w) :
    w.product = a * b ∧ w.product = w.quotient * n + w.remainder ∧ w.remainder < n := h

example (a b n : Nat) (w : MulModWitness) (h : MulModRel a b n w) :
    w.remainder = (a * b) % n := mulMod_sound h

example (p q r n : Nat) (heq : p = q * n + r) (hr : r < n) : r = p % n :=
  remainder_eq_mod_of_eq heq hr

example : genMulMod 16 16 17 = ⟨256, 15, 1⟩ := by decide
example : MulModRel 16 16 17 ⟨256, 15, 1⟩ := by decide
example : MulModRel 0 0 1 (genMulMod 0 0 1) := genMulMod_correct 0 0 1 (by decide)
example (a b : Nat) : ¬ ∃ w, MulModRel a b 0 w := mulMod_zero_modulus a b

example (a b n r : Nat) (hr : r ≠ (a * b) % n) :
    ¬ MulModRel a b n { genMulMod a b n with remainder := r } :=
  mulMod_wrong_remainder hr

example : ¬ MulModRel 16 16 17 ⟨256, 1, 15⟩ := mulMod_swapped_slots_rejected
example : ¬ MulModRel 16 16 17 ⟨255, 15, 1⟩ := mulMod_wrong_product_rejected

-- Slice 4: small moduli (up to 2^32) discharge every word precondition.
example : SmallModulus 17 := by decide
example : SmallModulus (2 ^ 32) := by decide
example : ¬ SmallModulus 0 := by decide
example : ¬ SmallModulus (2 ^ 32 + 1) := by decide

example (n : Nat) (hn : SmallModulus n) : FitsU64 n := small_modulus_fits hn
example (a n : Nat) (hn : SmallModulus n) (ha : a < n) : FitsU64 a :=
  lt_small_modulus_fits hn ha
example (a b n : Nat) (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    FitsU64 (a + b) := add_fits_of_small_modulus hn ha hb
example (a b n : Nat) (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    FitsU64 (a * b) := mul_fits_of_small_modulus hn ha hb

example (a b n : Nat) (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    FitsU64 (genMulMod a b n).product ∧
    (genMulMod a b n).quotient < n ∧ (genMulMod a b n).remainder < n :=
  genMulMod_bounds hn ha hb

example (a b n : Nat) (w : MulModWitness) (hrel : MulModRel a b n w)
    (hp : FitsU64 w.product) :
    FitsU64 (w.quotient * n) ∧ FitsU64 (w.quotient * n + w.remainder) :=
  mulMod_intermediates_fit hrel hp

example (a b n : Nat) (ha : FitsU64 a) (hb : FitsU64 b)
    (hn : FitsU64 n) (hp : FitsU64 (a * b)) (hpos : 0 < n) :
    (genMulModU64 (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat n)).toNat =
      genMulMod a b n := genMulModU64_correct ha hb hn hp hpos

example (a b n : Nat) (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    (genMulModU64 (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat n)).toNat =
      genMulMod a b n := genMulModU64_small_correct hn ha hb

example (a b n : Nat) (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    MulModRel a b n
      (genMulModU64 (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat n)).toNat :=
  genMulModU64_small_satisfies hn ha hb

-- Inclusive modulus upper bound remains safe for the largest reduced factors.
example : FitsU64 ((2 ^ 32 - 1) * (2 ^ 32 - 1)) :=
  mul_fits_of_small_modulus (n := 2 ^ 32) (by decide) (by decide) (by decide)

example : (genMulModU64 16 16 17).toNat = ⟨256, 15, 1⟩ := by decide

-- Slice 5: field relation soundness and composed word lowering.
example (a b c : Field17) (h : Field17.AddRel a b c) : c = Field17.add a b :=
  Field17.add_sound h
example (a b c : Field17) (h : Field17.MulRel a b c) : c = Field17.mul a b :=
  Field17.mul_sound h

example (a b : Field17) :
    ((UInt64.ofNat a.toNat + UInt64.ofNat b.toNat) % UInt64.ofNat 17).toNat =
      (Field17.add a b).toNat := Field17.add_u64 a b
example (a b : Field17) :
    ((UInt64.ofNat a.toNat * UInt64.ofNat b.toNat) % UInt64.ofNat 17).toNat =
      (Field17.mul a b).toNat := Field17.mul_u64 a b

-- A small kernel enumeration confirms the prime-field nonzero inverse property.
example (a : Field17) (ha : a.toNat ≠ 0) :
    ∃ b : Field17, Field17.mul a b = Field17.ofNat 1 := Field17.nonzero_has_inverse a ha

-- Slice 6: lift field257 modular gates only with explicit no-wrap bounds.
example (x y p : Nat) (hx : x < p) (hy : y < p) (heq : x % p = y % p) : x = y :=
  nat_eq_of_mod_eq_of_lt hx hy heq

example (q r n : Nat) (hq : q < n) (hr : r < n) : q * n + r < n * n :=
  quotient_remainder_lt_square hq hr

example (a b n : Nat) (hn : n ≤ 16) (ha : a < n) (hb : b < n) : a * b < 257 :=
  product_lt_257 hn ha hb

example (q r n : Nat) (hn : n ≤ 16) (hq : q < n) (hr : r < n) : q * n + r < 257 :=
  quotient_remainder_lt_257 hn hq hr

example (a b n q r : Nat) (hn : n ≤ 16) (ha : a < n) (hb : b < n)
    (hq : q < n) (hr : r < n) (heq : (a * b) % 257 = (q * n + r) % 257) :
    a * b = q * n + r := field257_mulmod_nat_eq hn ha hb hq hr heq

example (a b n q r : Nat) (hn : n ≤ 16) (ha : a < n) (hb : b < n)
    (hq : q < n) (hr : r < n) (heq : (a * b) % 257 = (q * n + r) % 257) :
    r = (a * b) % n := field257_mulmod_sound hn ha hb hq hr heq

example (a b n : Nat) (w : MulModWitness) (hn : n ≤ 16) (ha : a < n) (hb : b < n)
    (hq : w.quotient < n) (hr : w.remainder < n) (hp : w.product < 257)
    (hmul : w.product % 257 = (a * b) % 257)
    (hqr : w.product % 257 = (w.quotient * n + w.remainder) % 257) :
    MulModRel a b n w := mulModRel_of_field257 hn ha hb hq hr hp hmul hqr

example : (15 * 15 : Nat) = 14 * 16 + 1 :=
  field257_mulmod_nat_eq (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
example : (1 : Nat) = (15 * 15) % 16 :=
  field257_mulmod_sound (q := 14) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- Modular equality alone cannot be treated as integer equality.
example : (0 : Nat) % 257 = 257 % 257 ∧ (0 : Nat) ≠ 257 := field257_wrap_counterexample

end Witgen.Arithmetic.Tests

-- All public arithmetic theorem dependencies, inspected by the receipt harness.
#print axioms Witgen.Arithmetic.Field17.toNat_lt
#print axioms Witgen.Arithmetic.Field17.ofNat_toNat
#print axioms Witgen.Arithmetic.Field17.ofNat_toNat_eq
#print axioms Witgen.Arithmetic.Field17.add_toNat
#print axioms Witgen.Arithmetic.Field17.mul_toNat
#print axioms Witgen.Arithmetic.Field17.add_ofNat_toNat
#print axioms Witgen.Arithmetic.Field17.mul_ofNat_toNat
#print axioms Witgen.Arithmetic.Field17.add_correct
#print axioms Witgen.Arithmetic.Field17.mul_correct
#print axioms Witgen.Arithmetic.u64_ofNat_toNat
#print axioms Witgen.Arithmetic.u64_add_toNat
#print axioms Witgen.Arithmetic.u64_mul_toNat
#print axioms Witgen.Arithmetic.u64_div_toNat
#print axioms Witgen.Arithmetic.u64_mod_toNat
#print axioms Witgen.Arithmetic.u64_ofNat_ne_zero
#print axioms Witgen.Arithmetic.u64_ofNat_not_exact
#print axioms Witgen.Arithmetic.genMulMod_correct
#print axioms Witgen.Arithmetic.remainder_eq_mod_of_eq
#print axioms Witgen.Arithmetic.mulMod_sound
#print axioms Witgen.Arithmetic.mulMod_zero_modulus
#print axioms Witgen.Arithmetic.mulMod_wrong_remainder
#print axioms Witgen.Arithmetic.mulMod_swapped_slots_rejected
#print axioms Witgen.Arithmetic.mulMod_wrong_product_rejected
#print axioms Witgen.Arithmetic.small_modulus_fits
#print axioms Witgen.Arithmetic.lt_small_modulus_fits
#print axioms Witgen.Arithmetic.add_fits_of_small_modulus
#print axioms Witgen.Arithmetic.mul_fits_of_small_modulus
#print axioms Witgen.Arithmetic.genMulMod_bounds
#print axioms Witgen.Arithmetic.mulMod_intermediates_fit
#print axioms Witgen.Arithmetic.genMulModU64_correct
#print axioms Witgen.Arithmetic.genMulModU64_small_correct
#print axioms Witgen.Arithmetic.genMulModU64_small_satisfies
#print axioms Witgen.Arithmetic.Field17.add_sound
#print axioms Witgen.Arithmetic.Field17.mul_sound
#print axioms Witgen.Arithmetic.Field17.add_u64
#print axioms Witgen.Arithmetic.Field17.mul_u64
#print axioms Witgen.Arithmetic.Field17.nonzero_has_inverse
#print axioms Witgen.Arithmetic.nat_eq_of_mod_eq_of_lt
#print axioms Witgen.Arithmetic.quotient_remainder_lt_square
#print axioms Witgen.Arithmetic.product_lt_257
#print axioms Witgen.Arithmetic.quotient_remainder_lt_257
#print axioms Witgen.Arithmetic.field257_mulmod_nat_eq
#print axioms Witgen.Arithmetic.field257_mulmod_sound
#print axioms Witgen.Arithmetic.mulModRel_of_field257
#print axioms Witgen.Arithmetic.field257_wrap_counterexample
