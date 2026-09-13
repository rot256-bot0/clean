import Witgen.Examples.RSA4096.Program
import Witgen.Examples.RSA4096.Codec
import Witgen.Examples.RSA4096.IO

open Lean Witgen Witgen.Typed Witgen.Methods Witgen.Examples.RSA4096

private def checked {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok x => pure x
  | .error message => throw (IO.userError message)

private def saveJson (path : System.FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.compress ++ "\n")

def main (args : List String) : IO UInt32 := do
  match args with
  | ["run", input, output] =>
      let request ← checked (Json.parse (← IO.FS.readFile input))
      let (n, s, d) ← checked (parseInputs request)
      let cells := (witnessProgram (F := Feature)).eval model h![n, s, d]
      unless cells.length == 160527 do
        throw (IO.userError s!"wrong full witness length: {cells.length}")
      saveJson output (witnessJson cells)
      return 0
  | ["export", output] =>
      let encoded ← checked (moduleJson typeJson codec (Library.nil : Library Feature [])
        "rsa4096_hybrid" ["modulus", "signature", "digest"]
        ((witnessProgram (F := Feature)).mapHandler (fun op => .inl op)))
      saveJson output encoded
      return 0
  | _ =>
      (← IO.getStderr).putStrLn "usage: lean --run MainRSA.lean run INPUT.json OUTPUT.json | export OUTPUT.json"
      return 2
