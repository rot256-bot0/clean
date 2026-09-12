import Witgen.U64.Word4

namespace Witgen.U64

/-- Shift and mask on an actual UInt64, not on decoded field naturals. -/
def wordBit (a : UInt64) (i : Nat) : Bool :=
  decide (((a >>> UInt64.ofNat i) &&& 1) = 1)

theorem wordBit_correct (a : UInt64) {i : Nat} (hi : i < 64) :
    wordBit a i = a.toNat.testBit i := by
  have hi' : i < UInt64.size := by change i < 2^64; omega
  simp only [wordBit, ← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat_of_lt' hi', show (1 : UInt64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt hi, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq]

namespace Word4

/-- Total 256-bit selection: out-of-range indices are false, never wrapped. -/
def bitAt (a : Word4) (i : Nat) : Bool :=
  if i < 64 then wordBit a.l0 i
  else if i < 128 then wordBit a.l1 (i-64)
  else if i < 192 then wordBit a.l2 (i-128)
  else if i < 256 then wordBit a.l3 (i-192)
  else false

theorem bitAt_out_of_range (a : Word4) {i : Nat} (hi : 256 ≤ i) :
    bitAt a i = false := by
  simp only [bitAt, show ¬i < 64 by omega, show ¬i < 128 by omega,
    show ¬i < 192 by omega, show ¬i < 256 by omega, ↓reduceIte]

theorem bitAt_correct (a : Word4) {i : Nat} (hi : i < 256) :
    bitAt a i = a.decode.testBit i := by
  have hd : a.decode = radix * (radix * (radix * a.l3.toNat + a.l2.toNat) + a.l1.toNat) + a.l0.toNat := by
    simp only [decode, radix]; omega
  rw [hd, Nat.testBit_two_pow_mul_add _ a.l0.toNat_lt]
  by_cases h0 : i < 64
  · simp only [bitAt, h0, ↓reduceIte, wordBit_correct a.l0 h0]
  · simp only [bitAt, h0, ↓reduceIte]
    rw [Nat.testBit_two_pow_mul_add _ a.l1.toNat_lt]
    by_cases h1 : i < 128
    · have h1' : i-64 < 64 := by omega
      simp only [h1, h1', ↓reduceIte, wordBit_correct a.l1 h1']
    · have h1' : ¬i-64 < 64 := by omega
      simp only [h1, h1', ↓reduceIte]
      rw [Nat.testBit_two_pow_mul_add _ a.l2.toNat_lt]
      have he : i-64-64 = i-128 := by omega
      rw [he]
      by_cases h2 : i < 192
      · have h2' : i-128 < 64 := by omega
        simp only [h2, h2', ↓reduceIte, wordBit_correct a.l2 h2']
      · have h2' : ¬i-128 < 64 := by omega
        have h3 : i-192 < 64 := by omega
        have he' : i-128-64 = i-192 := by omega
        simp only [h2, h2', he', hi, ↓reduceIte, wordBit_correct a.l3 h3]

/-- High-to-low binary multiplication. Each recursive step consumes one bit;
`n` is only a bounded loop index. Field data stays in four UInt64 limbs. -/
def mulLoop (p a b : Word4) : Nat → Word4 → Word4
  | 0, r => r
  | n+1, r =>
    let d := Add p r r
    let next := if bitAt a n then Add p d b else d
    mulLoop p a b n next

def Mul (p a b : Word4) : Word4 := mulLoop p a b 256 zero

def Square (p a : Word4) : Word4 := Mul p a a

/-- Constructive radix decomposition, avoiding the choice-dependent Std
`Nat.mod_pow_succ` lemma. Only Euclidean division identities are used. -/
theorem mod_double (x m : Nat) (hm : 0 < m) :
    x % (m*2) = x%m + m*(x/m%2) := by
  have hr0 := Nat.mod_lt x hm
  have hb := Nat.mod_lt (x/m) (show 0 < 2 by decide)
  have hr : x%m + m*(x/m%2) < m*2 := by
    have hcases : x/m%2 = 0 ∨ x/m%2 = 1 := by omega
    rcases hcases with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero]; omega
    · rw [h, Nat.mul_one]; omega
  have he : x = (x/m/2)*(m*2) + (x%m + m*(x/m%2)) := by
    calc
      x = x%m + m*(x/m) := (Nat.mod_add_div x m).symm
      _ = x%m + m*(x/m%2 + 2*(x/m/2)) :=
        congrArg (fun y => x%m + m*y) (Nat.mod_add_div (x/m) 2).symm
      _ = _ := by
        simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm]
  calc
    x % (m*2) = ((x/m/2)*(m*2) + (x%m + m*(x/m%2))) % (m*2) := congrArg (· % (m*2)) he
    _ = x%m + m*(x/m%2) := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr]

theorem mod_two_pow_succ (x n : Nat) :
    x % 2^(n+1) = x%2^n + 2^n*(x/2^n%2) := by
  rw [Nat.pow_succ]
  exact mod_double x (2^n) (Nat.two_pow_pos n)

/-- Modular Horner step, isolated from the word representation. -/
theorem horner_identity (r b a n p : Nat) :
    (((r+r + b * (a / 2^n % 2)) % p) * 2^n + b * (a % 2^n)) % p =
      (r * 2^(n+1) + b * (a % 2^(n+1))) % p := by
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod]
  congr 1
  rw [mod_two_pow_succ, Nat.pow_succ, Nat.add_mul, Nat.add_mul, Nat.mul_add]
  simp only [Nat.mul_comm, Nat.mul_left_comm,
    Nat.two_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Structural invariant, valid for all prefixes and all positive 256-bit moduli. -/
theorem mulLoop_correct (p a b : Word4) (hp : 0 < p.decode)
    (hb : Canonical p.decode b) (n : Nat) (hn : n ≤ 256) (r : Word4)
    (hr : Canonical p.decode r) :
    (mulLoop p a b n r).decode =
      (r.decode * 2^n + b.decode * (a.decode % 2^n)) % p.decode ∧
    Canonical p.decode (mulLoop p a b n r) := by
  induction n generalizing r with
  | zero =>
    refine ⟨?_, hr⟩
    simp only [mulLoop, Nat.pow_zero, Nat.mul_one, Nat.mod_one,
      Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hr]
  | succ n ih =>
    have hd := Add_correct p r r hp hr hr
    have hdb := Add_correct p (Add p r r) b hp hd.2 hb
    have hbit := bitAt_correct a (show n < 256 by omega)
    have hm : bit (bitAt a n) = a.decode / 2^n % 2 := by
      rw [hbit, Nat.testBit_eq_decide_div_mod_eq]
      have hlt := Nat.mod_lt (a.decode / 2^n) (show 0 < 2 by decide)
      simp only [bit, decide_eq_true_eq]
      split <;> omega
    let next := if bitAt a n then Add p (Add p r r) b else Add p r r
    have hnext : Canonical p.decode next := by
      dsimp [next]; split
      · exact hdb.2
      · exact hd.2
    have he : next.decode =
        (r.decode+r.decode + b.decode * (a.decode / 2^n % 2)) % p.decode := by
      rw [← hm]
      dsimp [next]
      cases bitAt a n <;> simp only [bit, Bool.false_eq_true, ↓reduceIte,
        Nat.mul_zero, Nat.add_zero, Nat.mul_one]
      · exact hd.1
      · rw [hdb.1, hd.1, Nat.mod_add_mod]
    have hi := ih (by omega) next hnext
    refine ⟨?_, hi.2⟩
    change (mulLoop p a b n next).decode = _
    rw [hi.1, he, horner_identity]

theorem Mul_correct (p a b : Word4) (hp : 0 < p.decode)
    (_ha : Canonical p.decode a) (hb : Canonical p.decode b) :
    (Mul p a b).decode = (a.decode * b.decode) % p.decode ∧
      Canonical p.decode (Mul p a b) := by
  have h := mulLoop_correct p a b hp hb 256 (by decide) zero hp
  simpa only [Mul, decode_zero, Nat.zero_mul, Nat.zero_add,
    Nat.mod_eq_of_lt (decode_lt a), Nat.mul_comm] using h

theorem Square_correct (p a : Word4) (hp : 0 < p.decode)
    (ha : Canonical p.decode a) :
    (Square p a).decode = (a.decode * a.decode) % p.decode ∧
      Canonical p.decode (Square p a) := Mul_correct p a a hp ha ha

end Word4
end Witgen.U64
