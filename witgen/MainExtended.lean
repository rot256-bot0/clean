import Witgen.Branching.Programs

namespace Witgen.ExtendedFixtures
open Lean Typed Methods

private def checked (value : Except String Json) : IO Json :=
  match value with
  | .ok x => pure x
  | .error e => throw (IO.userError e)

private def nativeModule {F : Signature Ty} {Γ : List Ty} {t : Ty}
    (codec : OpCodec F) (name : String) (inputs : List String) (p : Program F Γ t) : IO Json :=
  checked (moduleJson typeJson codec (Library.nil : Library F []) name inputs
    (p.mapHandler (fun op => .inl op)))

private def save (dir : System.FilePath) (name mode : String) (value : Json) : IO Json := do
  IO.FS.writeFile (dir / (name ++ ".json")) (value.compress ++ "\n")
  return Json.mkObj [("name", .str name), ("mode", .str mode)]

private def decimal (n : Nat) : Json := .str (toString n)
private def record (name : String) (inputs : Array Json) (expected : Nat) : Json :=
  Json.mkObj [("program", .str name), ("inputs", .arr inputs), ("expected", decimal expected)]

private def unaryInputs (f : FieldId) : List Nat :=
  ([0,1,2,modulus f-1,modulus f-2,2^200+17].map (· % modulus f)).eraseDups

private def pairs (f : FieldId) : List (Nat × Nat) :=
  [(0,0),(0,1),(1,0),(1,1),(modulus f-1,modulus f-1),(modulus f-1,1),
    (2^128+17,2^200+3)] |>.map (fun (a,b) => (a % modulus f,b % modulus f))

def exportAll (dir : System.FilePath) : IO Json := do
  IO.FS.createDirAll dir
  let mut entries : Array Json := #[]
  let mut rows : Array Json := #[]
  for f in [bn254Fr,secpBase,secpScalar] do
    let stem := "field_" ++ toString f.val
    let neg := Branching.negative (F := FieldOp f) f
    let inv := Branching.inverse (F := FieldOp f) f
    for (suffix,program) in [("neg",neg),("inv",inv)] do
      let sourceName := stem ++ "_" ++ suffix ++ "_native"
      let natName := stem ++ "_" ++ suffix ++ "_nat"
      entries := entries.push (← save dir sourceName "native"
        (← nativeModule fieldCodec sourceName ["x"] program))
      entries := entries.push (← save dir natName "nat" (← checked
        (moduleJson typeJson NatMethods.codec (NatMethods.library f) natName ["x"]
          (program.mapHandler (NatMethods.handler f)))))
      for n in unaryInputs f do
        let a := Residue.ofNat (modulus_pos f) n
        let expected := (program.eval (fieldModel f) h![a]).val
        rows := rows.push (record sourceName #[decimal n] expected)
        rows := rows.push (record natName #[decimal n] expected)
    let ifName := stem ++ "_conditional"
    let choose := Branching.conditional (F := Branching.Feature f) f
    entries := entries.push (← save dir ifName "native"
      (← nativeModule (Branching.codec f) ifName ["flag","a","b"] choose))
    for flag in [false,true] do
      for (a,b) in pairs f do
        let fa := Residue.ofNat (modulus_pos f) a
        let fb := Residue.ofNat (modulus_pos f) b
        let expected := (choose.eval (Branching.model f) h![flag,fa,fb]).val
        rows := rows.push (record ifName #[.bool flag,decimal a,decimal b] expected)
    let matchName := stem ++ "_match"
    let select := Branching.matchFallback (F := Branching.Feature f) f
    entries := entries.push (← save dir matchName "native"
      (← nativeModule (Branching.codec f) matchName ["input","fallback"] select))
    let options : List (Option Nat) := [none,some 0,some 1,some (modulus f-1),some (2^200+17)]
    for option in options do
      for fallback in [0,1,modulus f-1,2^128+9] do
        let value := option.map (Residue.ofNat (modulus_pos f))
        let fb := Residue.ofNat (modulus_pos f) fallback
        let expected := (select.eval (Branching.model f) h![value,fb]).val
        let arg := match value with | none => Json.null | some a => decimal a.val
        rows := rows.push (record matchName #[arg,decimal fb.val] expected)
  IO.FS.writeFile (dir / "reference.json") ((Json.mkObj [("cases", .arr rows)]).compress ++ "\n")
  IO.FS.writeFile (dir / "manifest.json") ((Json.mkObj [("programs", .arr entries)]).compress ++ "\n")
  return Json.mkObj [("programs", toJson entries.size), ("cases", toJson rows.size)]
end Witgen.ExtendedFixtures

def main (args : List String) : IO Unit := do
  match args with
  | ["export", dir] => IO.println ((← Witgen.ExtendedFixtures.exportAll dir).compress)
  | _ => throw (IO.userError "usage: MainExtended.lean export DIR")
