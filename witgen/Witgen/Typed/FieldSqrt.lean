import Witgen.Typed.FieldInverses
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace Witgen.Typed
namespace FieldSqrt

/-- Smaller natural representative of the two signs. -/
def canonical {p : Nat} (a : ZMod p) : ZMod p :=
  if a.val ≤ (-a).val then a else -a

@[simp] theorem canonical_sq {p : Nat} (a : ZMod p) : (canonical a)^2 = a^2 := by
  unfold canonical
  split <;> simp_all

theorem canonical_le {p : Nat} (a : ZMod p) :
    (canonical a).val ≤ (-(canonical a)).val := by
  unfold canonical
  split <;> simp_all
  omega

/-- Bounded splitting of p-1 into 2^s*q. -/
def splitTwos : Nat → Nat → Nat × Nat
  | 0, q => (0, q)
  | fuel+1, q => if q % 2 = 0 then
      let (s,r) := splitTwos fuel (q/2)
      (s+1,r)
    else (0,q)

/-- Bounded Tonelli-Shanks accelerator. Its output is always checked by sqrt.
Failure does not imply nonsquareness: the complete fallback handles it. -/
def tonelliLoop {p : Nat} : Nat → Nat → ZMod p → ZMod p → ZMod p → ZMod p
  | 0, _, _, _, r => r
  | fuel+1, m, c, t, r =>
    if t = 1 then r else
    let i := ((List.range m).find? (fun i => t^(2^i) = 1)).getD m
    let b := c^(2^(m-i-1))
    tonelliLoop fuel i (b*b) (t*b*b) (r*b)

def candidate (f : FieldId) (a : ZMod (modulus f)) : ZMod (modulus f) :=
  let p := modulus f
  let (s,q) := splitTwos 256 (p-1)
  let z : ZMod p := if f = bn254Fr then 5 else if f = secpBase then 3 else 5
  tonelliLoop s s (z^q) (a^q) (a^((q+1)/2))

private theorem exists_root (f : FieldId) (a : ZMod (modulus f))
    (h : a = 0 ∨ a^(modulus f / 2) = 1) : ∃ r : Fin (modulus f), (r.val : ZMod (modulus f))^2 = a := by
  letI : Fact (modulus f).Prime := ⟨modulus_prime f⟩
  have hs : IsSquare a := by
    rcases h with h | h
    · subst a; exact ⟨0, by simp⟩
    · by_cases hz : a = 0
      · subst a; exact ⟨0, by simp⟩
      · exact (ZMod.euler_criterion (modulus f) hz).mpr h
  obtain ⟨r, hr⟩ := (isSquare_iff_exists_sq a).mp hs
  exact ⟨⟨r.val, ZMod.val_lt r⟩, by simpa using hr.symm⟩

/-- Complete semantics with a checked fast path. The linear finite-search fallback
is only evaluated if Euler accepts but the bounded accelerator's square check fails.
The search is proof-free: Euler's classical existence proof belongs only in the
correctness theorems, not in this executable definition or the shared field model.
No universal performance claim for that accelerator is part of this definition. -/
def sqrt (f : FieldId) (a : ZMod (modulus f)) : Option (ZMod (modulus f)) :=
  if a = 0 ∨ a^(modulus f / 2) = 1 then
    let r := candidate f a
    if r^2 = a then some (canonical r) else
      (Fin.find? (fun r : Fin (modulus f) => decide ((r.val : ZMod (modulus f))^2 = a))).map
        (fun r => canonical (r.val : ZMod (modulus f)))
  else none

theorem sqrt_sound (f : FieldId) (a r : ZMod (modulus f)) (h : sqrt f a = some r) :
    r^2 = a ∧ r.val ≤ (-r).val := by
  unfold sqrt at h
  split at h
  · rename_i he
    dsimp only at h
    split at h
    · cases h
      exact ⟨by simp_all, canonical_le _⟩
    · rw [Fin.find?_decide_eq_dite, dif_pos (exists_root f a he)] at h
      cases h
      exact ⟨by rw [canonical_sq]; exact Fin.find_spec (exists_root f a he), canonical_le _⟩
  · contradiction

theorem sqrt_none_iff (f : FieldId) (a : ZMod (modulus f)) :
    sqrt f a = none ↔ ¬ ∃ r, r^2 = a := by
  letI : Fact (modulus f).Prime := ⟨modulus_prime f⟩
  constructor
  · intro hn ⟨r,hr⟩
    have he : a = 0 ∨ a^(modulus f/2) = 1 := by
      by_cases hz : a = 0
      · exact Or.inl hz
      · exact Or.inr ((ZMod.euler_criterion (modulus f) hz).mp
          ((isSquare_iff_exists_sq a).mpr ⟨r,hr.symm⟩))
    simp only [sqrt, if_pos he] at hn
    split at hn
    · contradiction
    · rw [Fin.find?_decide_eq_dite, dif_pos (exists_root f a he)] at hn
      contradiction
  · intro hn
    cases hs : sqrt f a with
    | none => rfl
    | some r => exact False.elim (hn ⟨r, (sqrt_sound f a r hs).1⟩)

theorem canonical_unique (f : FieldId) (r s : ZMod (modulus f))
    (h : r^2 = s^2) (hr : r.val ≤ (-r).val) (hs : s.val ≤ (-s).val) : r = s := by
  letI : Fact (modulus f).Prime := ⟨modulus_prime f⟩
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp h with h | h
  · exact h
  · subst r
    simp only [neg_neg] at hr
    have he : (-s).val = s.val := Nat.le_antisymm hr hs
    exact ZMod.val_injective (modulus f) he

theorem sqrt_eq_some_iff (f : FieldId) (a r : ZMod (modulus f)) :
    sqrt f a = some r ↔ r^2 = a ∧ r.val ≤ (-r).val := by
  constructor
  · exact sqrt_sound f a r
  · intro ⟨hr,hc⟩
    cases hs : sqrt f a with
    | none => exact False.elim ((sqrt_none_iff f a).mp hs ⟨r,hr⟩)
    | some s =>
      have hh := sqrt_sound f a s hs
      rw [canonical_unique f s r (hh.1.trans hr.symm) hh.2 hc]

theorem sqrt_square (f : FieldId) (a : ZMod (modulus f)) :
    sqrt f (a^2) = some (canonical a) :=
  (sqrt_eq_some_iff f _ _).mpr ⟨canonical_sq a, canonical_le a⟩

@[simp] theorem sqrt_zero (f : FieldId) : sqrt f 0 = some 0 := by
  apply (sqrt_eq_some_iff f _ _).mpr
  simp

/-- Checked accelerator success implies the complete model never searches. -/
theorem sqrt_of_candidate (f : FieldId) (a : ZMod (modulus f))
    (h : (candidate f a)^2 = a) : sqrt f a = some (canonical (candidate f a)) :=
  (sqrt_eq_some_iff f _ _).mpr ⟨(canonical_sq _).trans h, canonical_le _⟩

theorem sqrt_none_of_euler (f : FieldId) (a : ZMod (modulus f))
    (h0 : a ≠ 0) (he : a^(modulus f/2) ≠ 1) : sqrt f a = none := by
  simp [sqrt, h0, he]

end FieldSqrt

/-- Natural target normalizes internally, including raw values at least p. -/
def sqrtNat (f : FieldId) (a : Nat) : Option Nat :=
  (FieldSqrt.sqrt f (a : ZMod (modulus f))).map ZMod.val

theorem sqrtNat_mod (f : FieldId) (a : Nat) : sqrtNat f (a % modulus f) = sqrtNat f a := by
  simp [sqrtNat]

namespace Residue

def sqrt {f : FieldId} (a : FieldValue f) : Option (FieldValue f) :=
  letI : NeZero (modulus f) := ⟨Nat.ne_of_gt (modulus_pos f)⟩
  (FieldSqrt.sqrt f (a.val : ZMod (modulus f))).map (fun r => ⟨r.val, ZMod.val_lt r⟩)

theorem sqrt_nat_rel {f : FieldId} (a : FieldValue f) :
    Option.Rel (fun r n => r.val = n) (sqrt a) (sqrtNat f a.val) := by
  unfold sqrt sqrtNat
  cases FieldSqrt.sqrt f (a.val : ZMod (modulus f)) <;> constructor
  rfl

private theorem cast_injective (f : FieldId) :
    Function.Injective (fun a : FieldValue f => (a.val : ZMod (modulus f))) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg ZMod.val h
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hh

private theorem cast_square {f : FieldId} (a : FieldValue f) :
    ((square a).val : ZMod (modulus f)) = (a.val : ZMod (modulus f))^2 := by
  simp [square, ofNat, Nat.cast_pow]

private theorem cast_neg {f : FieldId} (a : FieldValue f) :
    ((neg a).val : ZMod (modulus f)) = -(a.val : ZMod (modulus f)) := by
  simp [neg, ofNat, Nat.cast_sub (Nat.le_of_lt a.isLt)]

private theorem sqrt_map_cast {f : FieldId} (a : FieldValue f) :
    (sqrt a).map (fun r => (r.val : ZMod (modulus f))) =
      FieldSqrt.sqrt f (a.val : ZMod (modulus f)) := by
  letI : NeZero (modulus f) := ⟨Nat.ne_of_gt (modulus_pos f)⟩
  simp [sqrt, Option.map_map, Function.comp_def]

/-- Exact public source contract: sound, complete and canonical. -/
theorem sqrt_eq_some_iff {f : FieldId} (a r : FieldValue f) :
    sqrt a = some r ↔ square r = a ∧ r.val ≤ (neg r).val := by
  have hm := Option.map_inj_right (fun _ _ h => cast_injective f h)
    (o := sqrt a) (o' := some r)
  rw [sqrt_map_cast, Option.map_some, FieldSqrt.sqrt_eq_some_iff] at hm
  rw [← hm]
  have hv (b : FieldValue f) : (b.val : ZMod (modulus f)).val = b.val :=
    ZMod.val_natCast_of_lt b.isLt
  rw [← cast_square, ← cast_neg, hv r, hv (neg r)]
  exact and_congr ((cast_injective f).eq_iff) Iff.rfl

theorem sqrt_sound {f : FieldId} (a r : FieldValue f) (h : sqrt a = some r) :
    square r = a ∧ r.val ≤ (neg r).val := (sqrt_eq_some_iff a r).mp h

theorem sqrt_canonical_unique {f : FieldId} (a r s : FieldValue f)
    (hr : square r = a ∧ r.val ≤ (neg r).val)
    (hs : square s = a ∧ s.val ≤ (neg s).val) : r = s :=
  Option.some.inj (((sqrt_eq_some_iff a r).mpr hr).symm.trans
    ((sqrt_eq_some_iff a s).mpr hs))

theorem sqrt_none_iff {f : FieldId} (a : FieldValue f) :
    sqrt a = none ↔ ¬ ∃ r, square r = a := by
  have hm := Option.map_inj_right (fun _ _ h => cast_injective f h)
    (o := sqrt a) (o' := none)
  rw [sqrt_map_cast, Option.map_none, FieldSqrt.sqrt_none_iff] at hm
  rw [← hm]
  apply not_congr
  constructor
  · rintro ⟨r,hr⟩
    letI : NeZero (modulus f) := ⟨Nat.ne_of_gt (modulus_pos f)⟩
    refine ⟨⟨r.val, ZMod.val_lt r⟩, cast_injective f ?_⟩
    dsimp only
    rw [cast_square]
    simpa using hr
  · rintro ⟨r,hr⟩
    exact ⟨(r.val : ZMod (modulus f)), by rw [← cast_square, hr]⟩

@[simp] theorem sqrt_zero (f : FieldId) :
    sqrt (ofNat (modulus_pos f) 0) = some (ofNat (modulus_pos f) 0) := by
  apply (sqrt_eq_some_iff _ _).mpr
  constructor
  · apply Fin.ext; simp [square, ofNat]
  · simp [ofNat]

/-- Canonical root of a square, expressed with the actual source negation. -/
theorem sqrt_square {f : FieldId} (a : FieldValue f) :
    sqrt (square a) = some (if a.val ≤ (neg a).val then a else neg a) := by
  have hn : square (neg a) = square a := by
    apply cast_injective f
    dsimp only
    rw [cast_square, cast_square, cast_neg, neg_sq]
  have hnn : neg (neg a) = a := by
    apply cast_injective f
    dsimp only
    rw [cast_neg, cast_neg, neg_neg]
  apply (sqrt_eq_some_iff _ _).mpr
  split
  · rename_i h; exact ⟨rfl,h⟩
  · rename_i h
    exact ⟨hn, by rw [hnn]; omega⟩

end Residue
end Witgen.Typed
