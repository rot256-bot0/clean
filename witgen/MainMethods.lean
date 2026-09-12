import Witgen.Typed.Public
import Witgen.Typed.U64Integration
import Witgen.U64.Tests

namespace Witgen.MethodFixtures
open Lean Typed Methods

private def checked (x : Except String Json) : IO Json := IO.ofExcept x
private def decimal (n : Nat) : Json := .str (toString n)

def nativeFieldJson (f : FieldId) : Except String Json :=
  moduleJson typeJson fieldCodec .nil ("field_" ++ toString f.val ++ "_native") ["a","b"]
    ((fieldProgram f).mapHandler Sum.inl)

def toAffineProgram : Program Secp.Feature [.point secp256k1]
    (.option (.pair (.field secpBase) (.field secpBase))) :=
  witgen [p] do
    let coordinates ← curve.ToAffine p
    return coordinates

def toAffineJson : Except String Json :=
  moduleJson typeJson Secp.codec .nil "secp_to_affine" ["point"]
    (toAffineProgram.mapHandler Sum.inl)

def roundtripJson : Except String Json :=
  moduleJson typeJson Secp.affineCodec .nil "secp_affine_roundtrip" ["point"]
    (Secp.roundtripProgram.mapHandler Sum.inl)

def inputPairs (p : Nat) : List (Nat × Nat) :=
  ([(0,0),(1,1),(p-1,p-1),(p-2,p-3),(p-1,1),
    (2^64,2^128+3),(2^200+7,2^192+9),(2^255-1,p-1),
    (p/2,p/3),(p-123456789,p-987654321),(2^253,2^250),(2^65+99,2^129+101)]
    |>.map fun (a,b) => (a%p,b%p)).eraseDups

def fixture (name mode : String) (inputs : Array Json) (output : Json) : Json :=
  Json.mkObj [("program",.str name),("mode",.str mode),("inputs",.arr inputs),("expected",output)]

def pairReference (xy : FieldValue secpBase × FieldValue secpBase) : Json :=
  .arr #[decimal xy.1.val, decimal xy.2.val]

def pointReference (p : Secp.Point) : Json :=
  match Secp.toAffine p with
  | none => Json.mkObj [("infinity",.bool true)]
  | some xy => Json.mkObj [("x",decimal xy.1.val),("y",decimal xy.2.val)]

def hex32 (n : Nat) : String :=
  String.ofList ((List.range 64).reverse.map fun i =>
    "0123456789abcdef".toList[(n / 16^i) % 16]!)

def pointInput (p : Secp.Point) : Json :=
  match Secp.toAffine p with
  | none => .str "00"
  | some xy => .str ("04" ++ hex32 xy.1.val ++ hex32 xy.2.val)

def optionReference (encode : α → Json) : Option α → Json
  | none => .null
  | some x => encode x

def exportAll (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  let mut programs : Array Json := #[]
  let mut cases : Array Json := #[]
  for f in [bn254Fr,secpBase,secpScalar] do
    let native ← checked (nativeFieldJson f)
    let natural ← checked (fieldProgramNatJson f)
    let word ← checked (u64FieldProgramJson f)
    for (mode, module) in [("native",native),("nat",natural),("u64",word)] do
      let name ← IO.ofExcept (module.getObjValAs? String "name")
      IO.FS.writeFile (directory / (name ++ ".json")) (module.pretty ++ "\n")
      programs := programs.push (Json.mkObj [("name",.str name),("mode",.str mode)])
    for (a,b) in inputPairs (modulus f) do
      let fa := Residue.ofNat (modulus_pos f) a
      let fb := Residue.ofNat (modulus_pos f) b
      let source := (fieldProgram f).eval (fieldModel f) h![fa,fb]
      let natural := (fieldProgramNat f).eval ((NatMethods.library f).model NatMethods.model) h![a,b]
      let word := (u64FieldProgram f).eval (U64.allLibrary.model U64.primitive)
        h![U64.Word4.encode a,U64.Word4.encode b]
      unless source.val == natural && natural == word.decode do
        throw (IO.userError "source/Nat/U64 method-caller mismatch")
      for mode in ["native","nat_methods","u64_methods"] do
        let actualMode := if mode == "nat_methods" then "nat" else if mode == "u64_methods" then "u64" else mode
        cases := cases.push (fixture ("field_" ++ toString f.val ++ "_" ++ mode) actualMode
          #[decimal a,decimal b] (decimal source.val))
  for result in [Public.mixedJson, Secp.generatorRoundtripJson, Secp.fromAffineJson, toAffineJson, roundtripJson,
      Secp.curveEqJson, Secp.curveMSMJson, Secp.constructedMSMJson,
      Secp.constantGeneratorJson, Secp.constantIdentityJson] do
    let module ← checked result
    let name ← IO.ofExcept (module.getObjValAs? String "name")
    IO.FS.writeFile (directory / (name ++ ".json")) (module.pretty ++ "\n")
    programs := programs.push (Json.mkObj [("name",.str name),("mode",.str "native")])
  for (s,t) in ([(0,0),(1,1),(1,0),(2,3),(modulus secpScalar-1,1),
      (2^200+7,2^129+9),(17,19)] : List (Nat × Nat)) do
    let fs := Residue.ofNat (modulus_pos secpScalar) s
    let ft := Residue.ofNat (modulus_pos secpScalar) t
    let out := Secp.mixed.eval Secp.mixedModel h![fs,ft]
    cases := cases.push (fixture "secp_mixed_fields" "native"
      #[decimal fs.val,decimal ft.val] (optionReference (fun x => decimal x.val) out))
  let points : List Secp.Point := [0,Secp.generator,Secp.generator+Secp.generator,-Secp.generator,
    Secp.mul (Residue.ofNat (modulus_pos secpScalar) (modulus secpScalar-1)) Secp.generator]
  for p in points do
    let coords := toAffineProgram.eval Secp.model h![p]
    cases := cases.push (fixture "secp_to_affine" "native" #[pointInput p]
      (optionReference pairReference coords))
    let back := Secp.roundtripProgram.eval Secp.affineModel h![p]
    cases := cases.push (fixture "secp_affine_roundtrip" "native" #[pointInput p]
      (optionReference pointReference back))
  for xy in [Secp.toAffine Secp.generator, Secp.toAffine (Secp.generator+Secp.generator),
      some (Residue.ofNat (modulus_pos secpBase) 0,Residue.ofNat (modulus_pos secpBase) 0),
      some (Residue.ofNat (modulus_pos secpBase) 1,Residue.ofNat (modulus_pos secpBase) 1)] do
    match xy with
    | none => pure ()
    | some pair =>
      let result := Secp.invalidPair.eval Secp.affineModel h![pair]
      cases := cases.push (fixture "secp_from_affine" "native" #[pairReference pair]
        (optionReference pointReference result))
  for p in points do
    for q in points do
      let result := Secp.curveEq.eval Secp.secpModel h![p,q]
      cases := cases.push (fixture "curve_eq" "native" #[pointInput p,pointInput q] (.bool result))
  let scalar := Residue.ofNat (modulus_pos secpScalar)
  let termSets : List (List (FieldValue secpScalar × Secp.Point)) :=
    [[], [(scalar 0,Secp.generator)], [(scalar 1,Secp.generator)], [(scalar 1,0)],
      [(scalar 1,Secp.generator),(scalar 1,-Secp.generator)],
      [(scalar 2,Secp.generator),(scalar 3,Secp.generator+Secp.generator)],
      [(scalar (modulus secpScalar-1),Secp.generator)],
      [(scalar (2^200+7),Secp.generator),(scalar (2^129+9),-Secp.generator),(scalar 17,0)]]
  for terms in termSets do
    let result := Secp.curveMSM.eval Secp.secpModel h![terms]
    let input := Json.arr (terms.toArray.map fun (s,p) => .arr #[decimal s.val,pointInput p])
    cases := cases.push (fixture "curve_msm" "native" #[input] (pointReference result))
  for (s,p) in [(scalar 0,Secp.generator),(scalar 1,Secp.generator),
      (scalar (modulus secpScalar-1),Secp.generator),(scalar (modulus secpScalar-1),0),
      (scalar (2^200+7),Secp.generator+Secp.generator)] do
    let result := Secp.constructedMSM.eval Secp.affineModel h![s,p]
    cases := cases.push (fixture "curve_msm_constructed" "native"
      #[decimal s.val,pointInput p] (pointReference result))
  cases := cases.push (fixture "curve_const_generator" "native" #[]
    (pointReference (Program.eval (F := CurveOp secp256k1) (V := Secp.Val)
      (t := Ty.point secp256k1) Secp.secpModel Secp.constantGenerator .nil)))
  cases := cases.push (fixture "curve_const_identity" "native" #[]
    (pointReference (Program.eval (F := CurveOp secp256k1) (V := Secp.Val)
      (t := Ty.point secp256k1) Secp.secpModel Secp.constantIdentity .nil)))
  let generatorBack := Secp.generatorRoundtrip.eval Secp.affineModel .nil
  cases := cases.push (fixture "secp_generator_affine_roundtrip" "native" #[]
    (optionReference pointReference generatorBack))
  IO.FS.writeFile (directory / "manifest.json") (Json.mkObj [("programs",.arr programs)]).pretty
  IO.FS.writeFile (directory / "reference.json") (Json.arr cases).pretty
  IO.println (Json.mkObj [("programs",toJson programs.size),("fixtures",toJson cases.size)]).compress

end Witgen.MethodFixtures

def main (args : List String) : IO Unit := do
  match args with
  | ["export", directory] => Witgen.MethodFixtures.exportAll directory
  | _ => throw (IO.userError "usage: MainMethods.lean export DIRECTORY")
