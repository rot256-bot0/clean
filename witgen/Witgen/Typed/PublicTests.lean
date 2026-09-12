import Witgen.Typed.Public

open Witgen Witgen.Typed
example : Public.mixed = Secp.mixed := rfl
example : secp256k1.Base ≠ secp256k1.Scalar := by decide
#check curve.Add
#check curve.Scale
#check curve.Inv
#check curve.ToAffine
#check curve.FromAffine
