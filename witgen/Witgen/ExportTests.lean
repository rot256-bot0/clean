import Witgen.Export

open Witgen Demo

example : ((Export.programJson fieldInfo quadraticField).getObjValAs? String "op") =
    Except.ok "field.mul" := by rfl

example : ((Export.programJson fieldInfo quadraticField).getObjVal? "args") =
    Except.ok (Lean.toJson ([0, 0] : List Nat)) := by rfl

#eval (show IO Unit from do
  match (Export.programJson fieldInfo quadraticField).getObjValAs? (List Nat) "args" with
  | .ok values =>
    unless values == [0, 0] do throw (IO.userError "exported references differ")
  | .error message => throw (IO.userError message))

#eval (Export.programJson fieldInfo quadraticField).compress

example : (Export.valueJson (fun n : Nat => Lean.Json.str (toString n)) .quad
    (⟨9, 13⟩ : Quad Nat)).getObjValAs? String "output" = .ok "13" := rfl
