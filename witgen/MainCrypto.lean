import Witgen.Crypto.Export

open Witgen.Crypto

/-- Crypto main: arbitrary-precision scalar inputs/cells, not the bounded toy suite. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["export", directory] => CryptoExport.exportAll directory; return 0
  | ["fixtures"] => CryptoExport.fixtures; return 0
  | ["fixtures", path] => CryptoExport.fixtures (some path); return 0
  | [] | ["demo"] => CryptoExport.demo; return 0
  | _ =>
    IO.eprintln "usage: MainCrypto.lean export DIR | fixtures [FILE] | demo"
    return 1
