import Witgen.Typed.Curve

namespace Witgen.Typed.CurveNamedTests
open Witgen
-- Parent-owned Authoring.lean must recognize this closed static descriptor.
def eqOnly {F : Signature Ty} (c : CurveId) [Has (CurveOp c) F] :
    Program F [.point c, .point c] .bool :=
  witgen [p,q] do
    let result ← curve.Eq p q
    return result
end Witgen.Typed.CurveNamedTests
