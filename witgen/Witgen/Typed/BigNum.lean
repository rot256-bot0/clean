import Witgen.Typed.Types
import Witgen.Authoring

namespace Witgen.Typed

/-- Optional arbitrary-precision natural-number operations on the existing `.nat` sort.
    There is no fixed width, overflow, sign, or implicit reduction. -/
inductive BigNumOp : Signature Ty where
  | const (n : Nat) : BigNumOp [] [] .nat
  | add : BigNumOp [.nat, .nat] [] .nat
  /-- Truncated Nat subtraction: `a - b = 0` when `a ≤ b`. -/
  | sub : BigNumOp [.nat, .nat] [] .nat
  | mul : BigNumOp [.nat, .nat] [] .nat
  | square : BigNumOp [.nat] [] .nat
  /-- `(quotient, remainder)`; total at divisor zero with result `(0, dividend)`. -/
  | divMod : BigNumOp [.nat, .nat] [] (.pair .nat .nat)
  | lt : BigNumOp [.nat, .nat] [] .bool
  /-- Zero-based bit index, static in the finite program. -/
  | bit (index : Nat) : BigNumOp [.nat] [] .bool
  | shl (amount : Nat) : BigNumOp [.nat] [] .nat
  | shr (amount : Nat) : BigNumOp [.nat] [] .nat
  /-- Dynamic zero-filling right shift; arbitrary-precision input, no machine-width wrap. -/
  | shrBy : BigNumOp [.nat, .nat] [] .nat

/-- Executable, choice-free semantics using Lean's arbitrary-precision Nat. -/
def bigNumModel : Model BigNumOp FieldVal where
  eval := fun op args _ => match op, args with
    | .const n, .nil => n
    | .add, .cons a (.cons b .nil) => a + b
    | .sub, .cons a (.cons b .nil) => a - b
    | .mul, .cons a (.cons b .nil) => a * b
    | .square, .cons a .nil => a * a
    | .divMod, .cons a (.cons b .nil) => (a / b, a % b)
    | .lt, .cons a (.cons b .nil) => a < b
    | .bit i, .cons a .nil => a.testBit i
    | .shl n, .cons a .nil => a <<< n
    | .shr n, .cons a .nil => a >>> n
    | .shrBy, h![a, n] => a >>> n

/-- Reconstruction is valid even at zero; the strict remainder bound needs nonzero. -/
theorem BigNumOp.divMod_reconstruct (a b : Nat) :
    let qr := bigNumModel.eval BigNumOp.divMod h![a, b] .nil
    b * qr.1 + qr.2 = a := Nat.div_add_mod a b

theorem BigNumOp.divMod_remainder_lt (a b : Nat) (hb : b ≠ 0) :
    (bigNumModel.eval BigNumOp.divMod h![a, b] .nil).2 < b :=
  Nat.mod_lt a (Nat.pos_of_ne_zero hb)

@[simp] theorem BigNumOp.divMod_zero (a : Nat) :
    bigNumModel.eval BigNumOp.divMod h![a, 0] .nil = (0, a) := by
  change (a / 0, a % 0) = (0, a)
  rw [Nat.div_zero, Nat.mod_zero]

theorem BigNumOp.sub_eq_zero_of_le (a b : Nat) (h : a ≤ b) :
    bigNumModel.eval BigNumOp.sub h![a, b] .nil = 0 := Nat.sub_eq_zero_of_le h

/-- Separate capability: crossing a field boundary must name the field in the signature. -/
inductive FieldBridgeOp (f : FieldId) : Signature Ty where
  | natToField : FieldBridgeOp f [.nat] [] (.field f)
  | fieldToNat : FieldBridgeOp f [.field f] [] .nat

/-- FromNat reduces modulo the field modulus; ToNat returns its canonical representative. -/
def fieldBridgeModel (f : FieldId) : Model (FieldBridgeOp f) FieldVal where
  eval := fun op args _ => match op, args with
    | .natToField, .cons n .nil => Residue.ofNat (modulus_pos f) n
    | .fieldToNat, .cons x .nil => x.val

@[simp] theorem FieldBridgeOp.field_nat_field (f : FieldId) (x : FieldValue f) :
    (fieldBridgeModel f).eval .natToField
      h![(fieldBridgeModel f).eval .fieldToNat h![x] .nil] .nil = x := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt x.isLt

@[simp] theorem FieldBridgeOp.nat_field_nat (f : FieldId) (n : Nat) :
    (fieldBridgeModel f).eval .fieldToNat
      h![(fieldBridgeModel f).eval .natToField h![n] .nil] .nil = n % modulus f := rfl

end Witgen.Typed

namespace Witgen.bignum
open Typed
variable {F : Signature Ty} {Γ : List Ty} [Has BigNumOp F]

def Const (n : Nat) : Step F Γ .nat := call (BigNumOp.const n) .nil .nil

def Add (a b : Var Γ .nat) : Step F Γ .nat := call BigNumOp.add h![a, b] .nil

/-- Natural subtraction, truncated at zero (not integer subtraction). -/
def Sub (a b : Var Γ .nat) : Step F Γ .nat := call BigNumOp.sub h![a, b] .nil

def Mul (a b : Var Γ .nat) : Step F Γ .nat := call BigNumOp.mul h![a, b] .nil

def Square (a : Var Γ .nat) : Step F Γ .nat := call BigNumOp.square h![a] .nil

/-- Project quotient/remainder using the existing `value.Fst`/`value.Snd` capability. -/
def DivMod (a b : Var Γ .nat) : Step F Γ (.pair .nat .nat) :=
  call BigNumOp.divMod h![a, b] .nil

def Lt (a b : Var Γ .nat) : Step F Γ .bool := call BigNumOp.lt h![a, b] .nil

def Bit (a : Var Γ .nat) (index : Nat) : Step F Γ .bool := call (BigNumOp.bit index) h![a] .nil

def Shl (a : Var Γ .nat) (amount : Nat) : Step F Γ .nat := call (BigNumOp.shl amount) h![a] .nil

def Shr (a : Var Γ .nat) (amount : Nat) : Step F Γ .nat := call (BigNumOp.shr amount) h![a] .nil

def ShrBy (a amount : Var Γ .nat) : Step F Γ .nat := call BigNumOp.shrBy h![a, amount] .nil

end Witgen.bignum

namespace Witgen.field
open Typed
variable {F : Signature Ty} {Γ : List Ty} {f : FieldId}

/-- Reduction into the explicitly selected field. -/
def FromNat (f : FieldId) [Has (FieldBridgeOp f) F] (n : Var Γ .nat) : Step F Γ (.field f) :=
  call (FieldBridgeOp.natToField (f := f)) h![n] .nil

/-- The field is inferred from the typed input; the result is canonical. -/
def ToNat [Has (FieldBridgeOp f) F] (x : Var Γ (.field f)) : Step F Γ .nat :=
  call (FieldBridgeOp.fieldToNat (f := f)) h![x] .nil

end Witgen.field
