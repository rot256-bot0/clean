import Witgen.Examples.RSA4096.Codec

namespace Witgen.Examples.RSA4096
open Lean Typed Methods

#eval (do
  let a := codec (.big (.const (2^4096)))
  unless a.getObjValAs? String "op" == .ok "bignum.const" do
    throw (IO.userError "bignum tag")
  let stat := (a.getObjVal? "static").toOption.getD Json.null
  unless stat.getObjValAs? String "value" == .ok (toString (2^4096 : Nat)) do
    throw (IO.userError "wide literals must be decimal strings")
  let bridge := codec (.bridge .natToField)
  let metadata := (bridge.getObjVal? "static").toOption.getD Json.null
  unless metadata.getObjValAs? String "modulus" == .ok (toString (modulus bn254Fr)) do
    throw (IO.userError "field bridge metadata")
  let p : Program Feature [.nat, .nat] .nat :=
    witgen [a, bits] do
      let out ← bignum.ShrBy a bits
      return out
  let ast := programJson typeJson codec p
  unless ast.getObjValAs? String "op" == .ok "bignum.shr_by" do
    throw (IO.userError "actual typed AST export")
  : IO Unit)

end Witgen.Examples.RSA4096
