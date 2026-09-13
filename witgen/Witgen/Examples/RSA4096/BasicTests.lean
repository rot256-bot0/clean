import Witgen.Examples.RSA4096.Basic

namespace Witgen.Examples.RSA4096
open Witgen.Typed

private def integration : Program Feature [.nat, .nat] Scalars :=
  witgen [a, b] do
    let qr ← bignum.DivMod a b
    let q ← value.Fst qr
    let r ← value.Snd qr
    let qf ← field.FromNat bn254Fr q
    let rf ← field.FromNat bn254Fr r
    let difference ← field.Sub qf rf
    let xs ← vector.Singleton difference
    return xs

example : (integration.eval model h![37, 5]).map Fin.val = [5] := by decide

end Witgen.Examples.RSA4096
