import Witgen.Typed.Values
namespace Witgen.Typed.ValueTests
open Witgen
example : (ValueOp.model FieldValue (UInt64 × UInt64 × UInt64 × UInt64) PUnit).eval
    (ValueOp.pair Ty.nat Ty.bool) (.cons 7 (.cons true .nil)) .nil = (7, true) := rfl
end Witgen.Typed.ValueTests
