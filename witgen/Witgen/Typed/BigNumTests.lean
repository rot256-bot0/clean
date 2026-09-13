import Witgen.Typed.BigNum
import Witgen.Typed.Field
import Witgen.Typed.Values

namespace Witgen.Typed.BigNumTests
open Witgen

def quotientRemainder {F : Signature Ty} [Has BigNumOp F] [Has ValueOp F] :
    Program F [.nat, .nat] (.pair .nat .nat) :=
  witgen [a, b] do
    let qr ← bignum.DivMod a b
    let q ← value.Fst qr
    let r ← value.Snd qr
    let out ← value.Pair q r
    return out

example : bigNumModel.eval BigNumOp.divMod h![37, 5] .nil = (7, 2) := rfl
example : bigNumModel.eval BigNumOp.divMod h![37, 0] .nil = (0, 37) := rfl

-- The second tracer uses every foundational arithmetic authoring helper.
def arithmetic {F : Signature Ty} [Has BigNumOp F] [Has ValueOp F] :
    Program F [.nat, .nat] (.pair .bool .nat) :=
  witgen [a, b] do
    let c ← bignum.Const 3
    let sum ← bignum.Add a c
    let diff ← bignum.Sub sum b
    let product ← bignum.Mul diff b
    let sq ← bignum.Square product
    let left ← bignum.Shl sq 64
    let right ← bignum.Shr left 64
    let low ← bignum.Bit right 0
    let out ← value.Pair low right
    return out

def less {F : Signature Ty} [Has BigNumOp F] : Program F [.nat, .nat] .bool :=
  witgen [a, b] do
    let out ← bignum.Lt a b
    return out

example : bigNumModel.eval (BigNumOp.const 11) .nil .nil = 11 := rfl
example : bigNumModel.eval BigNumOp.add h![37, 5] .nil = 42 := rfl
example : bigNumModel.eval BigNumOp.sub h![3, 5] .nil = 0 := rfl
example : bigNumModel.eval BigNumOp.mul h![7, 6] .nil = 42 := rfl
example : bigNumModel.eval BigNumOp.square h![7] .nil = 49 := rfl
example : bigNumModel.eval BigNumOp.lt h![3, 5] .nil = true := rfl
example : bigNumModel.eval (BigNumOp.bit 3) h![8] .nil = true := rfl
example : bigNumModel.eval (BigNumOp.bit 4) h![8] .nil = false := rfl
example : bigNumModel.eval (BigNumOp.shl 4) h![3] .nil = 48 := rfl
example : bigNumModel.eval (BigNumOp.shr 4) h![49] .nil = 3 := rfl

/-- Generic finite authoring: quotient and remainder reduced to the selected field,
    combined by field arithmetic, then returned in canonical Nat form. -/
def hybrid {F : Signature Ty} (f : FieldId) [Has BigNumOp F] [Has ValueOp F]
    [Has (FieldBridgeOp f) F] [Has (FieldOp f) F] : Program F [.nat, .nat] .nat :=
  witgen [a, b] do
    let qr ← bignum.DivMod a b
    let q ← value.Fst qr
    let r ← value.Snd qr
    let qf ← field.FromNat f q
    let rf ← field.FromNat f r
    let sum ← field.Add qf rf
    let out ← field.ToNat sum
    return out

example (f : FieldId) (x : FieldValue f) :
    (fieldBridgeModel f).eval FieldBridgeOp.fieldToNat h![x] .nil = x.val := rfl

#check BigNumOp.divMod_reconstruct
#check BigNumOp.divMod_remainder_lt
#check BigNumOp.divMod_zero
#check BigNumOp.sub_eq_zero_of_le
#check FieldBridgeOp.field_nat_field
#check FieldBridgeOp.nat_field_nat

inductive Feature : Signature Ty where
  | big (op : BigNumOp args shapes t) : Feature args shapes t
  | bridge (f : FieldId) (op : FieldBridgeOp f args shapes t) : Feature args shapes t
  | field (f : FieldId) (op : FieldOp f args shapes t) : Feature args shapes t
  | value (op : ValueOp args shapes t) : Feature args shapes t

instance : Has BigNumOp Feature where
  inject := .big
  injective := by intro args shapes t a b h; cases h; rfl
instance (f : FieldId) : Has (FieldBridgeOp f) Feature where
  inject := .bridge f
  injective := by intro args shapes t a b h; cases h; rfl
instance (f : FieldId) : Has (FieldOp f) Feature where
  inject := .field f
  injective := by intro args shapes t a b h; cases h; rfl
instance : Has ValueOp Feature where
  inject := .value
  injective := by intro args shapes t a b h; cases h; rfl

def model : Model Feature FieldVal where
  eval := fun op args regions => match op with
    | .big op => bigNumModel.eval op args regions
    | .bridge f op => (fieldBridgeModel f).eval op args regions
    | .field f op => (fieldModel f).eval op args regions
    | .value op => (ValueOp.model FieldValue _ (fun _ => PUnit)).eval op args regions

theorem hybrid_correct (f : FieldId) (a b : Nat) :
    (hybrid (F := Feature) f).eval model h![a, b] = (a / b + a % b) % modulus f := by
  change (a / b % modulus f + a % b % modulus f) % modulus f = _
  exact (Nat.add_mod (a / b) (a % b) (modulus f)).symm

/-- Named authoring is exactly the existing finite AST, not an opaque callback. -/
theorem divMod_named_is_finite :
    quotientRemainder (F := Feature) =
      .let_ (.big .divMod) h![.zero, .succ .zero] .nil
        (.let_ (.value (.fst .nat .nat)) h![.zero] .nil
          (.let_ (.value (.snd .nat .nat)) h![.succ .zero] .nil
            (.let_ (.value (.pair .nat .nat)) h![.succ .zero, .zero] .nil (.ret .zero)))) := rfl

example : (hybrid (F := Feature) bn254Fr).eval model h![37, 5] = 9 := rfl

/--
error: Application type mismatch: The argument
  b
has type
  Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpScalar)
but is expected to have type
  Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpBase)
in the application
  field.Add a b
-/
#guard_msgs in
example (a : Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpBase))
    (b : Var [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpScalar)) :
    Step Feature [Ty.field secpBase, Ty.field secpScalar] (Ty.field secpBase) := field.Add a b

/--
error: Type mismatch
  field.FromNat secpBase n
has type
  Step Feature [Ty.nat] (Ty.field secpBase)
but is expected to have type
  Step Feature [Ty.nat] (Ty.field secpScalar)
-/
#guard_msgs in
example (n : Var [Ty.nat] Ty.nat) : Step Feature [Ty.nat] (Ty.field secpScalar) :=
  field.FromNat (F := Feature) secpBase n

#eval do
  let q := 2^2048 - 1
  let b := 2^2048 - 159
  let r := 12345
  let a := q*b+r
  unless a.testBit 4095 && !(a.testBit 4096) do
    throw (IO.userError "control must have exactly 4096 bits")
  let qr := (quotientRemainder (F := Feature)).eval model h![a,b]
  unless qr == (q,r) do throw (IO.userError "4096-bit constructed division mismatch")
  let cases := [(0,0),(0,7),(7,0),(7,1),(7,7),(3,5),(37,5),(a,b),(a,0),(a,a),(a,1)]
  for (x,y) in cases do
    let out := (quotientRemainder (F := Feature)).eval model h![x,y]
    unless y*out.1+out.2 == x do throw (IO.userError "division reconstruction")
    unless out == (x/y,x%y) do throw (IO.userError "quotient/remainder mismatch")
    if y == 0 then
      unless out == (0,x) do throw (IO.userError "zero-divisor semantics")
    else
      unless out.2 < y do throw (IO.userError "remainder bound")
    let arith := (arithmetic (F := Feature)).eval model h![x,y]
    let expected : Nat := ((x+3-y)*y)^2
    unless arith == (expected.testBit 0,expected) do
      throw (IO.userError "arithmetic / static limb-shift mismatch")
    unless (less (F := Feature)).eval model h![x,y] == (x < y) do
      throw (IO.userError "less-than mismatch")
    for f in [bn254Fr,secpBase,secpScalar] do
      let out := (hybrid (F := Feature) f).eval model h![x,y]
      unless out == (x/y+x%y) % modulus f do
        throw (IO.userError "hybrid field bridge mismatch")
      let reduced := (fieldBridgeModel f).eval .natToField h![x] .nil
      let canonical := (fieldBridgeModel f).eval .fieldToNat h![reduced] .nil
      unless canonical == x % modulus f && canonical < modulus f do
        throw (IO.userError "canonical field representative mismatch")
      unless (fieldBridgeModel f).eval .natToField h![canonical] .nil == reduced do
        throw (IO.userError "field roundtrip mismatch")
  unless bigNumModel.eval (BigNumOp.bit 4095) h![a] .nil do
    throw (IO.userError "high bit missing")
  unless !(bigNumModel.eval (BigNumOp.bit 4096) h![a] .nil) do
    throw (IO.userError "out-of-range bit nonzero")
  unless bigNumModel.eval (BigNumOp.shr 4096) h![a] .nil == 0 do
    throw (IO.userError "overshift must be zero")
  unless bigNumModel.eval (BigNumOp.shl 0) h![a] .nil == a do
    throw (IO.userError "zero left-shift mismatch")
  unless bigNumModel.eval (BigNumOp.shr 0) h![a] .nil == a do
    throw (IO.userError "zero right-shift mismatch")
  IO.println s!"4096-bit controls passed: {cases.length} division/arithmetic cases, {cases.length * 3} hybrid/bridge cases; bit and shift boundaries"

def dynamicShift {F : Signature Ty} [Has BigNumOp F] : Program F [.nat, .nat] .nat :=
  witgen [a, bits] do
    let shifted ← bignum.ShrBy a bits
    return shifted

example : (dynamicShift (F := Feature)).eval model h![512, 8] = 2 := rfl
example : (dynamicShift (F := Feature)).eval model h![512, 1024] = 0 := rfl

end Witgen.Typed.BigNumTests
