import Witgen.Authoring
import Witgen.StructTests

namespace Witgen.StructSetTests
open StructTests

def updatePair : Program (StructOp desc) [.pair, .number] .pair :=
  witgen [old, value] do
    let fresh ← struct.Set desc .pair "right" old value
    return fresh

def oldAndNew : Program (StructOp desc) [.pair, .number] .pair :=
  witgen [old, value] do
    let fresh ← struct.Set desc .pair "right" old value
    let before ← struct.Get desc .pair "right" old
    let after ← struct.Get desc .pair "right" fresh
    let result ← struct.Named desc .pair fields![left := before, right := after]
    return result

example : updatePair.eval (structModel repr) h![(3, 8), 11] = (3, 11) := rfl
example : oldAndNew.eval (structModel repr) h![(3, 8), 11] = (8, 11) := rfl

example (s : Nat × Nat) (x : Nat) :
    (repr .pair).unpack ((repr .pair).set (.there .here) s x) = h![s.1, x] := rfl

end Witgen.StructSetTests
