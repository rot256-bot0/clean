import Witgen.U64.Tests

open Witgen.U64 Lean

def main (args : List String) : IO Unit := do
  let report ← Tests.run
  match args with
  | [] | ["test"] => pure ()
  | ["export", dir] =>
    IO.FS.createDirAll dir
    IO.FS.writeFile (System.FilePath.mk dir / "u64-shared.json") (bundleJson.pretty ++ "\n")
    IO.FS.writeFile (System.FilePath.mk dir / "u64-tests.json") (report.pretty ++ "\n")
  | _ => throw (IO.userError "usage: MainU64.lean [test | export DIRECTORY]")
  let keys := ["status","moduli","generic_pairs","generic_algorithm_checks","generic_body_checks",
    "field_pairs","field_caller_checks","overflow_negative_control"]
  let summary := Json.mkObj (keys.map fun key =>
    (key, (report.getObjVal? key).toOption.getD .null))
  IO.println summary.compress
