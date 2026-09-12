import Witgen.Typed.Curve
import Witgen.Typed.Values

namespace Witgen.Typed.CurvePrograms
open Witgen

/-- Capability-polymorphic source; no concrete feature bundle leaks into callers. -/
def mixed {F : Signature Ty} (c : CurveId) [Has (CurveOp c) F]
    [Has (FieldOp c.scalar) F] [Has (FieldOp c.base) F] [Has ValueOp F] :
    Program F [.field c.scalar, .field c.scalar] (.option (.field c.base)) :=
  witgen [s,t] do
    let ss ← field.Square s
    let st ← field.Mul ss t
    let alpha ← field.Add st s
    let g ← curve.Generator c
    let p ← curve.Mul alpha g
    let minusG ← curve.Inv g
    let q ← curve.Add p minusG
    let xy ← curve.ToAffine q
    let result ← match xy with
      | none => value.None (.field c.base)
      | some coordinates =>
        let x ← value.Fst coordinates
        let y ← value.Snd coordinates
        let xx ← field.Square x
        let xxy ← field.Mul xx y
        let out ← field.Add xxy x
        value.Some out
    return result

def roundtrip {F : Signature Ty} (c : CurveId) [Has (CurveOp c) F] [Has ValueOp F] :
    Program F [.point c] (.option (.point c)) :=
  witgen [p] do
    let xy ← curve.ToAffine p
    let out ← match xy with
      | none => value.None (.point c)
      | some coordinates => curve.FromAffine c coordinates
    return out

def curveEq {F : Signature Ty} (c : CurveId) [Has (CurveOp c) F] :
    Program F [.point c, .point c] .bool :=
  witgen [p,q] do
    let out ← curve.Eq p q
    return out

def curveMSM {F : Signature Ty} (c : CurveId) [Has (CurveOp c) F] :
    Program F [.list (.pair (.field c.scalar) (.point c))] (.point c) :=
  witgen [terms] do
    let out ← curve.MSM terms
    return out

def constructedMSM {F : Signature Ty} (c : CurveId) [Has (CurveOp c) F] [Has ValueOp F] :
    Program F [.field c.scalar, .point c] (.point c) :=
  witgen [s,p] do
    let term ← value.Pair s p
    let empty ← value.Nil (.pair (.field c.scalar) (.point c))
    let terms ← value.Cons term empty
    let out ← curve.MSM terms
    return out

end Witgen.Typed.CurvePrograms
