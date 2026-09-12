import Std

set_option autoImplicit false

/-! Arithmetic support independent of the typed IR and all native backends. -/
namespace Witgen.Arithmetic

/-- Canonical residues modulo the prime 17. No opaque native-field representation. -/
abbrev Field17 := Fin 17

namespace Field17

def toNat (x : Field17) : Nat := x.val

def ofNat (a : Nat) : Field17 := ⟨a % 17, Nat.mod_lt _ (by decide)⟩

def add (a b : Field17) : Field17 := ofNat (a.toNat + b.toNat)
def mul (a b : Field17) : Field17 := ofNat (a.toNat * b.toNat)

/-- Integer congruence constraints, independent of the arithmetic generator. -/
def AddRel (a b c : Field17) : Prop :=
  ∃ q : Nat, a.toNat + b.toNat = q * 17 + c.toNat

def MulRel (a b c : Field17) : Prop :=
  ∃ q : Nat, a.toNat * b.toNat = q * 17 + c.toNat

theorem toNat_lt (a : Field17) : a.toNat < 17 := a.isLt

@[simp] theorem ofNat_toNat (a : Field17) : ofNat a.toNat = a := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt a.isLt

@[simp] theorem ofNat_toNat_eq (a : Nat) : (ofNat a).toNat = a % 17 := rfl

@[simp] theorem add_toNat (a b : Field17) :
    (add a b).toNat = (a.toNat + b.toNat) % 17 := rfl

@[simp] theorem mul_toNat (a b : Field17) :
    (mul a b).toNat = (a.toNat * b.toNat) % 17 := rfl

theorem add_ofNat_toNat (a b : Nat) :
    (add (ofNat a) (ofNat b)).toNat = (a + b) % 17 :=
  (Nat.add_mod a b 17).symm

theorem mul_ofNat_toNat (a b : Nat) :
    (mul (ofNat a) (ofNat b)).toNat = (a * b) % 17 :=
  (Nat.mul_mod a b 17).symm

theorem add_correct (a b : Field17) : AddRel a b (add a b) :=
  ⟨(a.toNat + b.toNat) / 17, (Nat.div_add_mod' _ _).symm⟩

theorem mul_correct (a b : Field17) : MulRel a b (mul a b) :=
  ⟨(a.toNat * b.toNat) / 17, (Nat.div_add_mod' _ _).symm⟩

end Field17

/-- The source Nat has an exact, non-wrapping UInt64 representation. -/
def FitsU64 (n : Nat) : Prop := n < UInt64.size

instance (n : Nat) : Decidable (FitsU64 n) := inferInstanceAs (Decidable (n < UInt64.size))

theorem u64_ofNat_toNat {n : Nat} (hn : FitsU64 n) :
    (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' hn

theorem u64_add_toNat {a b : Nat} (ha : FitsU64 a) (hb : FitsU64 b)
    (hs : FitsU64 (a + b)) :
    (UInt64.ofNat a + UInt64.ofNat b).toNat = a + b := by
  rw [UInt64.toNat_add, u64_ofNat_toNat ha, u64_ofNat_toNat hb]
  exact Nat.mod_eq_of_lt hs

theorem u64_mul_toNat {a b : Nat} (ha : FitsU64 a) (hb : FitsU64 b)
    (hp : FitsU64 (a * b)) :
    (UInt64.ofNat a * UInt64.ofNat b).toNat = a * b := by
  rw [UInt64.toNat_mul, u64_ofNat_toNat ha, u64_ofNat_toNat hb]
  exact Nat.mod_eq_of_lt hp

/-- Positivity is part of the backend contract: Lean's division is total at zero,
whereas a native backend may trap. The equality alone needs only representability. -/
theorem u64_div_toNat {a b : Nat} (ha : FitsU64 a) (hb : FitsU64 b)
    (_hpos : 0 < b) :
    (UInt64.ofNat a / UInt64.ofNat b).toNat = a / b := by
  rw [UInt64.toNat_div, u64_ofNat_toNat ha, u64_ofNat_toNat hb]

theorem u64_mod_toNat {a b : Nat} (ha : FitsU64 a) (hb : FitsU64 b)
    (_hpos : 0 < b) :
    (UInt64.ofNat a % UInt64.ofNat b).toNat = a % b := by
  rw [UInt64.toNat_mod, u64_ofNat_toNat ha, u64_ofNat_toNat hb]

theorem u64_ofNat_ne_zero {b : Nat} (hb : FitsU64 b) (hpos : 0 < b) :
    UInt64.ofNat b ≠ 0 := by
  intro h
  have hz := congrArg UInt64.toNat h
  rw [u64_ofNat_toNat hb] at hz
  exact (Nat.ne_of_gt hpos) hz

/-- Negative boundary control: this API does not lower arbitrary bignums. -/
theorem u64_ofNat_not_exact {a : Nat} (ha : UInt64.size ≤ a) :
    (UInt64.ofNat a).toNat ≠ a := by
  intro h
  have ht := (UInt64.ofNat a).toNat_lt
  rw [h] at ht
  exact (Nat.not_lt_of_ge ha) ht

/-- Every internal value required by the Nat modular-multiplication relation. -/
structure MulModWitness where
  product : Nat
  quotient : Nat
  remainder : Nat
  deriving Repr, DecidableEq

/-- A circuit relation, not equality to a chosen generator. In particular, the
product cell is constrained as well as the output remainder cell.

Inspired by zk-golf `MulMod.lean` lines 14–22 and 176–203 at
`fb9e89a5de99022a53089f0d11a18331c4c321a3`. This is the mathematical Nat
relation, not the full RSA limb/carry circuit or its implementation binding. -/
def MulModRel (a b n : Nat) (w : MulModWitness) : Prop :=
  w.product = a * b ∧
  w.product = w.quotient * n + w.remainder ∧
  w.remainder < n

instance (a b n : Nat) (w : MulModWitness) : Decidable (MulModRel a b n w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A total witness generator. Certification requires a positive modulus. -/
def genMulMod (a b n : Nat) : MulModWitness :=
  let product := a * b
  ⟨product, product / n, product % n⟩

theorem genMulMod_correct (a b n : Nat) (hn : 0 < n) :
    MulModRel a b n (genMulMod a b n) :=
  ⟨rfl, (Nat.div_add_mod' (a * b) n).symm, Nat.mod_lt _ hn⟩

/-- Euclidean remainder uniqueness from an unchanged integer equation and range. -/
theorem remainder_eq_mod_of_eq {p q r n : Nat}
    (heq : p = q * n + r) (hr : r < n) : r = p % n := by
  rw [heq, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
    Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr]

/-- Sound for *any* witness satisfying the relation; no generator is mentioned. -/
theorem mulMod_sound {a b n : Nat} {w : MulModWitness}
    (h : MulModRel a b n w) : w.remainder = (a * b) % n := by
  have hr := remainder_eq_mod_of_eq h.2.1 h.2.2
  rw [h.1] at hr
  exact hr

theorem mulMod_zero_modulus (a b : Nat) : ¬ ∃ w, MulModRel a b 0 w := by
  rintro ⟨w, h⟩
  exact Nat.not_lt_zero w.remainder h.2.2

theorem mulMod_wrong_remainder {a b n r : Nat} (hr : r ≠ (a * b) % n) :
    ¬ MulModRel a b n { genMulMod a b n with remainder := r } := by
  intro h
  exact hr (mulMod_sound h)

/-- Wrong-slot control: quotient and remainder interchanged. -/
theorem mulMod_swapped_slots_rejected : ¬ MulModRel 16 16 17 ⟨256, 1, 15⟩ := by
  decide

/-- Internal-cell control: even a correct output cannot mask a wrong product. -/
theorem mulMod_wrong_product_rejected : ¬ MulModRel 16 16 17 ⟨255, 15, 1⟩ := by
  decide

/-- A convenient sufficient bound; the modulus may be exactly 2^32. -/
def SmallModulus (n : Nat) : Prop := 0 < n ∧ n ≤ 2 ^ 32

instance (n : Nat) : Decidable (SmallModulus n) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem small_modulus_fits {n : Nat} (hn : SmallModulus n) : FitsU64 n :=
  Nat.lt_of_le_of_lt hn.2 (by decide)

theorem lt_small_modulus_fits {a n : Nat} (hn : SmallModulus n) (ha : a < n) :
    FitsU64 a := Nat.lt_trans ha (small_modulus_fits hn)

theorem add_fits_of_small_modulus {a b n : Nat}
    (hn : SmallModulus n) (ha : a < n) (hb : b < n) : FitsU64 (a + b) :=
  Nat.lt_trans (Nat.lt_of_lt_of_le (Nat.add_lt_add ha hb)
    (Nat.add_le_add hn.2 hn.2)) (by decide)

theorem mul_fits_of_small_modulus {a b n : Nat}
    (hn : SmallModulus n) (ha : a < n) (hb : b < n) : FitsU64 (a * b) := by
  have ha' : a < 2 ^ 32 := Nat.lt_of_lt_of_le ha hn.2
  have hb' : b < 2 ^ 32 := Nat.lt_of_lt_of_le hb hn.2
  exact Nat.mul_lt_mul_of_lt_of_lt ha' hb'

theorem genMulMod_bounds {a b n : Nat}
    (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    FitsU64 (genMulMod a b n).product ∧
    (genMulMod a b n).quotient < n ∧ (genMulMod a b n).remainder < n := by
  refine ⟨mul_fits_of_small_modulus hn ha hb, ?_, Nat.mod_lt _ hn.1⟩
  exact (Nat.div_lt_iff_lt_mul hn.1).2 (Nat.mul_lt_mul_of_lt_of_lt ha hb)

/-- The RHS multiplication and addition in a valid circuit relation also cannot
wrap if its product cell fits. This covers relation checking, not only generation. -/
theorem mulMod_intermediates_fit {a b n : Nat} {w : MulModWitness}
    (hrel : MulModRel a b n w) (hp : FitsU64 w.product) :
    FitsU64 (w.quotient * n) ∧ FitsU64 (w.quotient * n + w.remainder) := by
  have hsum : FitsU64 (w.quotient * n + w.remainder) := by
    rw [← hrel.2.1]
    exact hp
  exact ⟨Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hsum, hsum⟩

/-- The same explicit three-cell witness record with word-valued slots. -/
structure MulModWordWitness where
  product : UInt64
  quotient : UInt64
  remainder : UInt64
  deriving Repr, DecidableEq

def MulModWordWitness.toNat (w : MulModWordWitness) : MulModWitness :=
  ⟨w.product.toNat, w.quotient.toNat, w.remainder.toNat⟩

def genMulModU64 (a b n : UInt64) : MulModWordWitness :=
  let product := a * b
  ⟨product, product / n, product % n⟩

/-- Full-record correspondence, not only output equality. This proves Lean
UInt64 semantics; it does not certify a Rust emitter, compiler, or native library. -/
theorem genMulModU64_correct {a b n : Nat}
    (ha : FitsU64 a) (hb : FitsU64 b) (hn : FitsU64 n)
    (hp : FitsU64 (a * b)) (_hpos : 0 < n) :
    (genMulModU64 (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat n)).toNat =
      genMulMod a b n := by
  simp only [genMulModU64, MulModWordWitness.toNat, genMulMod,
    UInt64.toNat_div, UInt64.toNat_mod, u64_mul_toNat ha hb hp, u64_ofNat_toNat hn]

theorem genMulModU64_small_correct {a b n : Nat}
    (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    (genMulModU64 (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat n)).toNat =
      genMulMod a b n :=
  genMulModU64_correct (lt_small_modulus_fits hn ha) (lt_small_modulus_fits hn hb)
    (small_modulus_fits hn) (mul_fits_of_small_modulus hn ha hb) hn.1

/-- End-to-end certification against the same independently defined relation. -/
theorem genMulModU64_small_satisfies {a b n : Nat}
    (hn : SmallModulus n) (ha : a < n) (hb : b < n) :
    MulModRel a b n
      (genMulModU64 (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat n)).toNat := by
  rw [genMulModU64_small_correct hn ha hb]
  exact genMulMod_correct a b n hn.1

namespace Field17

/-- Integer congruence plus canonical representation determines the field output. -/
theorem add_sound {a b c : Field17} (h : AddRel a b c) : c = add a b := by
  obtain ⟨q, hq⟩ := h
  apply Fin.ext
  exact remainder_eq_mod_of_eq hq c.isLt

theorem mul_sound {a b c : Field17} (h : MulRel a b c) : c = mul a b := by
  obtain ⟨q, hq⟩ := h
  apply Fin.ext
  exact remainder_eq_mod_of_eq hq c.isLt

/-- Field17 → canonical Nat → non-wrapping word addition and reduction. -/
theorem add_u64 (a b : Field17) :
    ((UInt64.ofNat a.toNat + UInt64.ofNat b.toNat) % UInt64.ofNat 17).toNat =
      (add a b).toNat := by
  have hn : SmallModulus 17 := by decide
  rw [UInt64.toNat_mod,
    u64_add_toNat (a := a.toNat) (b := b.toNat)
      (lt_small_modulus_fits hn a.isLt) (lt_small_modulus_fits hn b.isLt)
      (add_fits_of_small_modulus hn a.isLt b.isLt),
    u64_ofNat_toNat (small_modulus_fits hn)]
  rfl

/-- Field17 → canonical Nat → non-wrapping word multiplication and reduction. -/
theorem mul_u64 (a b : Field17) :
    ((UInt64.ofNat a.toNat * UInt64.ofNat b.toNat) % UInt64.ofNat 17).toNat =
      (mul a b).toNat := by
  have hn : SmallModulus 17 := by decide
  rw [UInt64.toNat_mod,
    u64_mul_toNat (a := a.toNat) (b := b.toNat)
      (lt_small_modulus_fits hn a.isLt) (lt_small_modulus_fits hn b.isLt)
      (mul_fits_of_small_modulus hn a.isLt b.isLt),
    u64_ofNat_toNat (small_modulus_fits hn)]
  rfl

/-- Small finite kernel proof: every nonzero residue has a multiplicative inverse.
No finite-field library, primality oracle, or native decision procedure is used. -/
theorem nonzero_has_inverse (a : Field17) (ha : a.toNat ≠ 0) :
    ∃ b : Field17, mul a b = ofNat 1 := by
  have h : ∀ x : Field17, x.toNat ≠ 0 → ∃ y : Field17, mul x y = ofNat 1 := by decide
  exact h a ha

end Field17

/-- Equality of canonical modular residues reflects Nat equality. -/
theorem nat_eq_of_mod_eq_of_lt {x y p : Nat}
    (hx : x < p) (hy : y < p) (heq : x % p = y % p) : x = y := by
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at heq

/-- Reduced quotient and remainder make the whole RHS smaller than n squared. -/
theorem quotient_remainder_lt_square {q r n : Nat} (hq : q < n) (hr : r < n) :
    q * n + r < n * n := by
  calc
    q * n + r < q * n + n := Nat.add_lt_add_left hr _
    _ = (q + 1) * n := (Nat.succ_mul q n).symm
    _ ≤ n * n := Nat.mul_le_mul_right n hq

theorem product_lt_257 {a b n : Nat} (hn : n ≤ 16) (ha : a < n) (hb : b < n) :
    a * b < 257 :=
  Nat.lt_trans (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt ha hb)
    (Nat.mul_le_mul hn hn)) (by decide)

theorem quotient_remainder_lt_257 {q r n : Nat}
    (hn : n ≤ 16) (hq : q < n) (hr : r < n) : q * n + r < 257 :=
  Nat.lt_trans (Nat.lt_of_lt_of_le (quotient_remainder_lt_square hq hr)
    (Nat.mul_le_mul hn hn)) (by decide)

/-- No-wrap lifting for the concrete field257 circuit slice. Positivity of n
is already implied by each strict operand/range bound. The gate is an equality
modulo 257; the conclusion is the unchanged integer relation, not just congruence. -/
theorem field257_mulmod_nat_eq {a b n q r : Nat}
    (hn : n ≤ 16) (ha : a < n) (hb : b < n) (hq : q < n) (hr : r < n)
    (heq : (a * b) % 257 = (q * n + r) % 257) : a * b = q * n + r :=
  nat_eq_of_mod_eq_of_lt (product_lt_257 hn ha hb)
    (quotient_remainder_lt_257 hn hq hr) heq

theorem field257_mulmod_sound {a b n q r : Nat}
    (hn : n ≤ 16) (ha : a < n) (hb : b < n) (hq : q < n) (hr : r < n)
    (heq : (a * b) % 257 = (q * n + r) % 257) : r = (a * b) % n :=
  remainder_eq_mod_of_eq (field257_mulmod_nat_eq hn ha hb hq hr heq) hr

/-- Lift two field gates with a canonical product cell to the complete Nat witness
relation. A field-cell representation must supply hp; otherwise product aliases
separated by 257 would satisfy the modular gates but fail the Nat relation. -/
theorem mulModRel_of_field257 {a b n : Nat} {w : MulModWitness}
    (hn : n ≤ 16) (ha : a < n) (hb : b < n)
    (hq : w.quotient < n) (hr : w.remainder < n) (hp : w.product < 257)
    (hmul : w.product % 257 = (a * b) % 257)
    (hqr : w.product % 257 = (w.quotient * n + w.remainder) % 257) :
    MulModRel a b n w :=
  ⟨nat_eq_of_mod_eq_of_lt hp (product_lt_257 hn ha hb) hmul,
   nat_eq_of_mod_eq_of_lt hp (quotient_remainder_lt_257 hn hq hr) hqr, hr⟩

/-- A guard against dropping the representation/no-wrap premises. -/
theorem field257_wrap_counterexample :
    (0 : Nat) % 257 = 257 % 257 ∧ (0 : Nat) ≠ 257 := by decide

end Witgen.Arithmetic
