import Witgen.Typed.NatMethods
import Witgen.Typed.SqrtTests
namespace Witgen.Typed.SqrtTests
open Witgen
example (f : FieldId) (a : Nat) :
    NatMethods.model.eval (NatMethods.Op.sqrt f) h![a] .nil = sqrtNat f a := rfl
example (f : FieldId) (a : FieldValue f) :
    Option.Rel (fun r n => r.val = n) (Residue.sqrt a)
      (((sqrtOnly (F := FieldOp f) f).mapHandler (NatMethods.handler f)).eval
        ((NatMethods.library f).model NatMethods.model) h![a.val]) :=
  (NatMethods.lowering f).correct (sqrtOnly (F := FieldOp f) f) h![a] h![a.val] ⟨rfl,trivial⟩
#eval do
  for f in [bn254Fr,secpBase,secpScalar] do
    let p := modulus f
    for n in ([0,1,2,4,p-1,p-2,2^128+17,2^200+17,(p-1)/2,(2^200+17)^2] : List Nat) do
      let expected := sqrtNat f n
      for raw in [n,n+p,n+2*p] do
        let out := NatMethods.model.eval (NatMethods.Op.sqrt f) h![raw] .nil
        unless out == expected do
          throw (IO.userError s!"raw Nat sqrt mismatch: field={f.val} input={raw}")
    let source := fieldCodec (FieldOp.sqrt (f := f))
    let target := NatMethods.codec (NatMethods.Op.sqrt f)
    let sourceExpected := Lean.Json.mkObj [("op", .str "field.sqrt"), ("static", fieldJson f)]
    let targetExpected := Lean.Json.mkObj [("op", .str "nat.field.sqrt"), ("static", fieldJson f)]
    unless source == sourceExpected && target == targetExpected do
      throw (IO.userError s!"sqrt codec metadata mismatch: field={f.val}")
    unless typeJson (.option (.field f)) == Lean.Json.mkObj [("option",fieldJson f)] do
      throw (IO.userError s!"sqrt result codec mismatch: field={f.val}")
  IO.println "sqrt raw Nat and exact source/target/result codec checks passed (all fields)"
end Witgen.Typed.SqrtTests
