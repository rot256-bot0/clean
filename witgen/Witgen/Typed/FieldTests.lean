import Witgen.Typed.Field

namespace Witgen.Typed.Tests
open Witgen

example : secpBase ≠ secpScalar := by decide
example : Ty.field secpBase ≠ Ty.field secpScalar := by decide

def square {f : FieldId} : Program (FieldOp f) [.field f] (.field f) :=
  witgen [x] do
    let y ← field.Square x
    return y

example (x : FieldValue secpScalar) :
    (square (f := secpScalar)).eval (fieldModel secpScalar) (.cons x .nil) =
      Residue.square x := rfl

example : (Residue.square (Residue.ofNat (modulus_pos secpScalar) 3)).val = 9 := by decide

example (f : FieldId) : squareFallback f FieldOp.square .nil =
    (.let_ FieldOp.mul h![.zero, .zero] .nil (.ret .zero) :
      Program (FieldOp f) [.field f] (.field f)) := rfl

def abstractCapability {F : Signature Ty} {f : FieldId} [Has (FieldOp f) F] :
    Program F [.field f, .field f] (.field f) :=
  witgen [a,b] do
    let p ← field.Mul a b
    let q ← field.Square p
    let r ← field.Add p q
    return r

end Witgen.Typed.Tests
