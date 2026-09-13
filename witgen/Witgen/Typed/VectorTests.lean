import Witgen.Typed.Vector

namespace Witgen.Typed.VectorTests
open Witgen

private def indices : Program VectorOp [] (.list .nat) :=
  witgen [] do
    let xs ← vector.Tabulate 5 h![] (witgen [i] do return i)
    return xs

private def pick : Program VectorOp [.list .nat, .nat, .nat] .nat :=
  witgen [xs, i, fallback] do
    let x ← vector.GetD xs i fallback
    return x

private def lastIndex : Program VectorOp [.nat] .nat :=
  witgen [initial] do
    let out ← vector.Fold 5 initial h![] (witgen [i, _acc] do return i)
    return out

example : indices.eval VectorOp.model .nil = [0, 1, 2, 3, 4] := by decide
example : pick.eval VectorOp.model h![[7, 8], 1, 99] = 8 := by decide
example : pick.eval VectorOp.model h![[7, 8], 4, 99] = 99 := by decide
example : lastIndex.eval VectorOp.model h![42] = 4 := by decide

#eval (do
  unless indices.eval VectorOp.model .nil == [0, 1, 2, 3, 4] do
    throw <| IO.userError "tabulate execution mismatch"
  unless lastIndex.eval VectorOp.model h![42] == 4 do
    throw <| IO.userError "fold execution mismatch"
  : IO Unit)

private def storage : Program VectorOp [.nat] (.list .nat) :=
  witgen [x] do
    let none ← vector.Empty .nat
    let one ← vector.Singleton x
    let two ← vector.Nats [8, 9]
    let a ← vector.Append none one
    let b ← vector.Append a two
    let c ← vector.Take 2 b
    let d ← vector.Drop 1 c
    let nested ← vector.Singleton d
    let flat ← vector.Flatten nested
    let result ← vector.Apply h![flat] (witgen [xs] do return xs)
    return result

example : storage.eval VectorOp.model h![7] = [8] := by decide

end Witgen.Typed.VectorTests
