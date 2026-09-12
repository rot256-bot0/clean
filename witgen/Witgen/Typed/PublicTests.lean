import Witgen.Typed.Public

open Witgen Witgen.Typed
example : Public.mixed (F := Secp.MixedFeature) secp256k1 = Secp.mixed := rfl
example : secp256k1.Base ≠ secp256k1.Scalar := by decide
#check curve.Add
#check curve.Mul
#check curve.Inv
#check curve.Eq
#check curve.MSM
#check curve.Const
#check curve.ToAffine
#check curve.FromAffine
