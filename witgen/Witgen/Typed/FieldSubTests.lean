import Witgen.Typed.NatMethods
namespace Witgen.Typed.FieldSubTests
open Witgen

def subOnly {F : Signature Ty} (f : FieldId) [Has (FieldOp f) F] :
    Program F [.field f,.field f] (.field f) :=
  witgen [a,b] do
    let r ← field.Sub a b
    return r

theorem lowering_correct (f : FieldId) (a b : FieldValue f) :
    (((subOnly (F := FieldOp f) f).mapHandler (NatMethods.handler f)).eval
      ((NatMethods.library f).model NatMethods.model) h![a.val,b.val]) = (Residue.sub a b).val :=
  ((NatMethods.lowering f).correct (subOnly (F := FieldOp f) f) h![a,b] h![a.val,b.val]
    ⟨rfl,rfl,trivial⟩).symm

#eval do
  for f in [bn254Fr,secpBase,secpScalar] do
    let p := modulus f
    for (a,b) in ([(0,0),(0,1),(1,0),(1,1),(p-1,1),(0,p-1),(p-1,p-1),
        (2^200+17,2^128+17)] : List (Nat × Nat)) do
      let expected := (a+p-b)%p
      let x := Residue.ofNat (modulus_pos f) a
      let y := Residue.ofNat (modulus_pos f) b
      let out := (subOnly (F := FieldOp f) f).eval (fieldModel f) h![x,y]
      unless out.val == expected do
        throw (IO.userError s!"sub source mismatch: field={f.val}")
      let raw := NatMethods.model.eval (NatMethods.Op.sub f) h![a+p,b+2*p] .nil
      unless raw == expected do
        throw (IO.userError s!"sub raw Nat mismatch: field={f.val}")
  IO.println "sub zero/self/wrap/fullwidth/raw Nat checks passed (all fields)"
end Witgen.Typed.FieldSubTests
