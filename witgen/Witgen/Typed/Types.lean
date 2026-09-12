import Witgen.Core

namespace Witgen.Typed

/-- Library-owned finite identifiers; the index is part of every field operand type. -/
abbrev FieldId := Fin 3
def bn254Fr : FieldId := 0
def secpBase : FieldId := 1
def secpScalar : FieldId := 2

inductive Ty where
  | field (id : FieldId)
  | nat | bool | u64 | word4 | point
  | pair (left right : Ty)
  | option (element : Ty)
  deriving DecidableEq, Repr

def modulus (f : FieldId) : Nat :=
  if f = bn254Fr then
    21888242871839275222246405745257275088548364400416034343698204186575808495617
  else if f = secpBase then
    115792089237316195423570985008687907853269984665640564039457584007908834671663
  else
    115792089237316195423570985008687907852837564279074904382605163141518161494337

theorem modulus_pos (f : FieldId) : 0 < modulus f := by
  unfold modulus
  split <;> first | decide | (split <;> decide)

abbrev FieldValue (f : FieldId) := Fin (modulus f)

namespace Residue

def ofNat {p : Nat} (hp : 0 < p) (n : Nat) : Fin p := ⟨n % p, Nat.mod_lt n hp⟩
def add {p : Nat} (a b : Fin p) : Fin p := ofNat (Nat.zero_lt_of_lt a.isLt) (a.val + b.val)
def mul {p : Nat} (a b : Fin p) : Fin p := ofNat (Nat.zero_lt_of_lt a.isLt) (a.val * b.val)
/-- Dedicated square semantics, not an alias at the operation boundary. -/
def square {p : Nat} (a : Fin p) : Fin p := ofNat (Nat.zero_lt_of_lt a.isLt) (a.val ^ 2)

@[simp] theorem square_spec {p : Nat} (a : Fin p) :
    (square a).val = a.val ^ 2 % p := rfl

theorem square_eq_mul {p : Nat} (a : Fin p) : square a = mul a a := by
  apply Fin.ext
  simp [square, mul, ofNat, Nat.pow_succ]

end Residue

/-- Shared structural interpretation of pair/option sorts. Computational carriers
remain parameters: this does not add a mandatory primitive feature. -/
abbrev Value (fields : FieldId → Type) (words points : Type) : Ty → Type
  | .field f => fields f
  | .nat => Nat
  | .bool => Bool
  | .u64 => UInt64
  | .word4 => words
  | .point => points
  | .pair a b => Value fields words points a × Value fields words points b
  | .option a => Option (Value fields words points a)

/-- Field-only interpretation; the point sort has no point operations in this model. -/
abbrev FieldVal := Value FieldValue (UInt64 × UInt64 × UInt64 × UInt64) PUnit

end Witgen.Typed
