import Witgen.Typed.Secp

namespace Witgen.secp256k1
abbrev Base : Typed.FieldId := Typed.secpBase
abbrev Scalar : Typed.FieldId := Typed.secpScalar
end Witgen.secp256k1

namespace Witgen.curve
abbrev Add := @Witgen.secp.Add
abbrev Scale := @Witgen.secp.Scale
abbrev Inv := @Witgen.secp.Inv
abbrev Generator := @Witgen.secp.Generator
abbrev Identity := @Witgen.secp.Identity
abbrev X := @Witgen.secp.X
end Witgen.curve

namespace Witgen.Typed.Public
open Witgen

/-- Operand tags select mathematical fields, not their backend representations. -/
def mixed : Program Secp.Feature
    [.field secp256k1.Scalar, .field secp256k1.Scalar, .field secp256k1.Base]
    (.field secp256k1.Base) :=
  witgen [s, t, b] do
    let ss ← field.Square s
    let st ← field.Mul ss t
    let alpha ← field.Add st s
    let g ← curve.Generator
    let p ← curve.Scale alpha g
    let minusG ← curve.Inv g
    let q ← curve.Add p minusG
    let x ← curve.X q
    let gx ← curve.X g
    let bb ← field.Square b
    let bx ← field.Mul bb x
    let output ← field.Add bx gx
    return output

theorem mixed_eq : mixed = Secp.mixed := rfl

theorem mixed_correct (s t : FieldValue secpScalar) (b : FieldValue secpBase) :
    (mixed.eval Secp.model h![s,t,b]).val = Secp.mixedSpec s t b :=
  Secp.concrete_mixed_correct s t b

open Lean Methods in
def mixedJson : Except String Json :=
  moduleJson typeJson Secp.codec .nil "secp_mixed_fields" ["s","t","b"]
    (mixed.mapHandler Sum.inl)

end Witgen.Typed.Public
