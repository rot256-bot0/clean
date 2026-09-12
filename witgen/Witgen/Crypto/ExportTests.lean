import Witgen.Crypto.Export

open Lean Witgen Witgen.Crypto

#eval do
  let modules ← CryptoExport.checkedModules
  unless modules.map Prod.fst == ["quad_bn254", "quad_nat", "envelope_bn254", "envelope_nat"] do
    throw (IO.userError "wrong exported program names")
  for (_, source) in modules do
    let semantics ← IO.ofExcept (source.getObjValAs? String "input_semantics")
    unless semantics == "bn254" do
      throw (IO.userError "missing BN254 input semantics")
    let modulus ← IO.ofExcept (source.getObjValAs? String "field_modulus")
    unless modulus == toString bn254Modulus do
      throw (IO.userError "modulus must be the exact decimal string")
  let cases ← CryptoExport.fixtureCases
  unless cases.size == 48 do throw (IO.userError "expected four ASTs on 12 boundary cases")
  for c in cases do
    let expected ← IO.ofExcept (c.getObjVal? "expected")
    let cells ← IO.ofExcept (expected.getObjValAs? (Array String) "cells")
    unless cells.size == 4 do throw (IO.userError "missing full witness cells")
  IO.println "crypto export: 4 ASTs, 48 full-layout decimal-string fixtures"
