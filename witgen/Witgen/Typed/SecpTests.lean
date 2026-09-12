import Witgen.Typed.SecpFeature
import Witgen.Typed.CurveTypingTests
namespace Witgen.Typed.Secp.Tests
open Witgen
example [Fact (modulus secpBase).Prime] (p : Point) :
    secpModel.eval (CurveOp.inv (c := secp256k1)) (.cons p .nil) .nil = -p := rfl
example (Γ : List Ty) (s : Var Γ (.field secpScalar)) (p : Var Γ (.point secp256k1)) :
    Step (CurveOp secp256k1) Γ (.point secp256k1) := curve.Mul s p
end Witgen.Typed.Secp.Tests
