import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum

namespace Witgen.Primality

/-- A radix digit and its claimed reduced power. All claims are checked below. -/
abbrev PowStep := Nat × Nat

def traceExponent : Nat → List PowStep → Nat
  | e, [] => e
  | e, (digit, _) :: rest => traceExponent (e * 16 + digit) rest

def traceValue : Nat → List PowStep → Nat
  | r, [] => r
  | _, (_, value) :: rest => traceValue value rest

/-- Explicit intermediate residues avoid deeply normalizing a recursive power.
No native-decision procedure or trusted external result is used by the proofs. -/
def checkTrace (p a : Nat) : Nat → List PowStep → Bool
  | _, [] => true
  | r, (digit, value) :: rest =>
    decide (digit < 16) && decide (value = (r ^ 16 * a ^ digit) % p) &&
      checkTrace p a value rest

theorem checkTrace_correct (p a r e : Nat) (steps : List PowStep)
    (hr : r = a ^ e % p) (hc : checkTrace p a r steps = true) :
    traceValue r steps = a ^ traceExponent e steps % p := by
  induction steps generalizing r e with
  | nil => exact hr
  | cons step rest ih =>
    rcases step with ⟨digit, value⟩
    simp only [checkTrace, Bool.and_eq_true, decide_eq_true_eq] at hc
    apply ih value (e * 16 + digit) ?_ hc.2
    rw [hc.1.2, hr, Nat.pow_add, Nat.pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]

theorem trace_power (p a e v : Nat) (steps : List PowStep)
    (hc : checkTrace p a (1 % p) steps = true)
    (he : traceExponent 0 steps = e) (hv : traceValue (1 % p) steps = v) :
    (a : ZMod p) ^ e = v := by
  have h := checkTrace_correct p a (1 % p) 0 steps (by simp) hc
  rw [he, hv] at h
  have hcast := congrArg (fun n : Nat => (n : ZMod p)) h
  simpa only [ZMod.natCast_mod, Nat.cast_pow] using hcast.symm

theorem trace_power_ne_one (p a e v : Nat) (steps : List PowStep)
    (hc : checkTrace p a (1 % p) steps = true)
    (he : traceExponent 0 steps = e) (hv : traceValue (1 % p) steps = v)
    (hne : v % p ≠ 1 % p) : (a : ZMod p) ^ e ≠ 1 := by
  intro h
  have hv1 : (v : ZMod p) = 1 := (trace_power p a e v steps hc he hv).symm.trans h
  have hvcast : (v : ZMod p) = ((1 : Nat) : ZMod p) := by
    simpa only [Nat.cast_one] using hv1
  exact hne ((ZMod.natCast_eq_natCast_iff' v 1 p).mp hvcast)

theorem prime_mem_factors (q : Nat) (hq : q.Prime) (factors : List Nat)
    (hpr : ∀ r ∈ factors, r.Prime) (hd : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil => exact False.elim (hq.not_dvd_one (by simpa using hd))
  | cons r rest ih =>
    rcases hq.dvd_mul.mp hd with hqr | hrest
    · rcases (Nat.dvd_prime (hpr r (by simp))).mp hqr with h1 | hqr
      · exact False.elim (hq.ne_one h1)
      · simp [hqr]
    · exact List.mem_cons_of_mem r (ih (fun s hs => hpr s (List.mem_cons_of_mem r hs)) hrest)

end Witgen.Primality
