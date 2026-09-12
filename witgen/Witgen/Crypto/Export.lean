import Lean
import Witgen.Crypto.Custom

namespace Witgen.Crypto.CryptoExport
open Lean

/-- Serialization metadata is data, not executable foreign code or a certificate. -/
structure OpInfo where
  tag : String
  literal : Option Nat := none
  field : Option Nat := none

def fieldInfo : FieldSig args shapes t → OpInfo
  | .inl (.const n) => ⟨"field.const", some n, none⟩
  | .inl .add => ⟨"field.add", none, none⟩
  | .inl .mul => ⟨"field.mul", none, none⟩
  | .inr (.make _) => ⟨"record.make", none, none⟩
  | .inr (.get _ field) => ⟨"record.get", none, some field.ref.index⟩
  | .inr (.set _ field) => ⟨"record.set", none, some field.ref.index⟩

def natInfo : NatSig args shapes t → OpInfo
  | .inl (.const n) => ⟨"nat.const", some n, none⟩
  | .inl .add => ⟨"nat.add", none, none⟩
  | .inl .mul => ⟨"nat.mul", none, none⟩
  | .inl .mod => ⟨"nat.mod", none, none⟩
  | .inr (.make _) => ⟨"record.make", none, none⟩
  | .inr (.get _ field) => ⟨"record.get", none, some field.ref.index⟩
  | .inr (.set _ field) => ⟨"record.set", none, some field.ref.index⟩

def namedType (name : String) (ty : Json) : Json :=
  Json.mkObj [("name", .str name), ("type", ty)]

/-- Our custom schema has exactly two scalar fields; names and field order come
from the descriptor used by the real StructOp, not an unrelated export table. -/
def quadTypeJson : Json :=
  Json.mkObj [("record", .str (schemaDesc .quad).name),
    ("fields", .arr ((schemaDesc .quad).fields.map fun (name, _) =>
      namedType name (.str "scalar")).toArray)]

def typeJson : Ty → Json
  | .scalar => .str "scalar"
  | .quad => quadTypeJson
  | .envelope => Json.mkObj [("record", .str (schemaDesc .envelope).name),
      ("fields", .arr ((schemaDesc .envelope).fields.map fun (name, _) =>
        namedType name quadTypeJson).toArray)]

theorem quad_schema_scalar_fields :
    (schemaDesc .quad).sorts = [.scalar, .scalar] := rfl

theorem envelope_schema_fields : (schemaDesc .envelope).sorts = [.quad] := rfl

abbrev Info {S : Type} (F : Signature S) :=
  {args : List S} → {shapes : List (RegionShape S)} → {t : S} →
    F args shapes t → OpInfo

def refsJson {S : Type} {Γ : List S} : {ts : List S} → HList (Var Γ) ts → List Nat
  | _, .nil => []
  | _, .cons r rest => r.index :: refsJson rest

/- Generic typed syntax traversal: this works for caller-owned sort universes. -/
mutual
  def programJson {S : Type} {F : Signature S} {Γ : List S} {t : S}
      (sortJson : S → Json) (info : Info F) : Program F Γ t → Json
    | .ret r => Json.mkObj [("tag", .str "ret"), ("ref", toJson r.index)]
    | .let_ (args := args) (s := s) op refs regions next =>
      let details := info op
      let literal := match details.literal with
        | none => []
        | some n => [("value", .str (toString n))]
      let field := match details.field with
        | none => []
        | some n => [("index", toJson n)]
      Json.mkObj [("tag", .str "let"), ("op", .str details.tag),
        ("args", toJson (refsJson refs)), ("arg_types", .arr (args.map sortJson).toArray),
        ("result", sortJson s), ("static", Json.mkObj (literal ++ field)),
        ("regions", .arr (regionsJson sortJson info regions)),
        ("next", programJson sortJson info next)]
  def regionsJson {S : Type} {F : Signature S} {shapes : List (RegionShape S)}
      (sortJson : S → Json) (info : Info F) : Regions F shapes → Array Json
    | .nil => #[]
    | .cons (sh := sh) body rest =>
      #[Json.mkObj [("inputs", .arr (sh.inputs.map sortJson).toArray),
        ("output", sortJson sh.output), ("body", programJson sortJson info body)]] ++
        regionsJson sortJson info rest
end

/-- Slot paths are sourced from the proved full circuit layout. -/
def quadLayout : Json :=
  Json.mkObj [("field", .str "bn254"), ("cells", toJson QuadCircuit.Slots.layout.length),
    ("input_slots", toJson [QuadCircuit.Slots.x, QuadCircuit.Slots.y]),
    ("outputs", .arr (QuadCircuit.outputPaths.map fun (name, slot) =>
      Json.mkObj [("path", toJson [name]), ("slot", toJson slot)]).toArray)]

def envelopeLayout : Json :=
  Json.mkObj [("field", .str "bn254"), ("cells", toJson QuadCircuit.Slots.layout.length),
    ("input_slots", toJson [QuadCircuit.Slots.x, QuadCircuit.Slots.y]),
    ("outputs", .arr (envelopeOutputPaths.map fun (path, slot) =>
      Json.mkObj [("path", toJson path), ("slot", toJson slot)]).toArray)]

def moduleJson {F : Signature Ty} {Γ : List Ty} {t : Ty}
    (info : Info F) (name domain : String) (inputNames : List String)
    (program : Program F Γ t) (layout : Json := quadLayout) : Except String Json := do
  unless inputNames.length == Γ.length do
    throw "input-name count differs from typed context"
  return Json.mkObj [("version", toJson (1 : Nat)), ("name", .str name),
    ("domain", .str domain), ("input_semantics", .str "bn254"),
    ("field_modulus", .str (toString bn254Modulus)),
    ("inputs", .arr ((inputNames.zip Γ).map fun (n, ty) => namedType n (typeJson ty)).toArray),
    ("output", typeJson t), ("body", programJson typeJson info program),
    ("wire_layout", layout)]

def modules : List (String × Except String Json) :=
  [("quad_bn254", moduleJson fieldInfo "generate" "bn254" ["x", "y"]
      (quadFieldWitgen bn254Positive).program),
   ("quad_nat", moduleJson natInfo "generate" "nat" ["x", "y"]
      (quadNatWitgen bn254Positive).program),
   ("envelope_bn254", moduleJson fieldInfo "generate" "bn254" ["x", "y"]
      envelopeField envelopeLayout),
   ("envelope_nat", moduleJson natInfo "generate" "nat" ["x", "y"]
      (envelopeNat bn254Modulus) envelopeLayout)]

def checkedModules : IO (List (String × Json)) :=
  modules.mapM fun (name, source) => do return (name, ← IO.ofExcept source)

def exportAll (directory : System.FilePath) : IO Unit := do
  let sources ← checkedModules
  IO.FS.createDirAll directory
  for (name, source) in sources do
    IO.FS.writeFile (directory / (name ++ ".json")) source.pretty
  IO.FS.writeFile (directory / "manifest.json")
    (Json.mkObj [("programs", toJson (sources.map Prod.fst))]).pretty
  IO.println (Json.mkObj [("exported", toJson sources.length)]).compress

/-- Deliberately cryptographic-width values, including boundary additions and
products far beyond u64/u128 that require reduction by the actual scalar prime. -/
def fixtureInputs : List (Nat × Nat) :=
  [(0, 0), (1, bn254Modulus - 1),
   (bn254Modulus - 1, bn254Modulus - 2), (bn254Modulus - 2, bn254Modulus - 3),
   (2 ^ 64, 2 ^ 64 + 1), (2 ^ 128 + 123, bn254Modulus - 1),
   (2 ^ 200 + 7, 2 ^ 192 + 9), (bn254Modulus / 2, bn254Modulus / 3),
   (bn254Modulus - 123456789, bn254Modulus - 987654321),
   (2 ^ 253, 2 ^ 250), (bn254Modulus - 5, 2 ^ 128), (2 ^ 65 + 99, 2 ^ 129 + 101)]

def decimal (n : Nat) : Json := .str (toString n)

def fixture (name : String) (x y : Nat) (cells : QuadCircuit.Buffer) : Json :=
  Json.mkObj [("program", .str name), ("inputs", .arr #[decimal x, decimal y]),
    ("expected", Json.mkObj [("cells", .arr (cells.toArray.map decimal))])]

/-- Actual source and lowered AST evaluations, including every emitted cell.
The target reference runs its raw Nat record: no decoding or modular repair. -/
def fixtureCases : IO (Array Json) := do
  let mut cases := #[]
  for (x, y) in fixtureInputs do
    unless x < bn254Modulus && y < bn254Modulus do
      throw (IO.userError "fixture input is noncanonical")
    let i : QuadInput bn254Modulus :=
      ⟨Residue.ofNat bn254Positive x, Residue.ofNat bn254Positive y⟩
    let fieldCells := QuadCircuit.populate (QuadCircuit.initial i)
      ((quadFieldWitgen bn254Positive).generate i)
    let raw := (quadNatWitgen bn254Positive).program.eval natModel (encodeNat i)
    let natCells := encodeRawNat i raw
    unless fieldCells == natCells do
      throw (IO.userError "full field/Nat witness mismatch")
    unless decide (QuadCircuit.Constraints i fieldCells) &&
        decide (QuadCircuit.Constraints i natCells) do
      throw (IO.userError "generated full witness violates circuit gates")
    cases := cases.push (fixture "quad_bn254" x y fieldCells)
    cases := cases.push (fixture "quad_nat" x y natCells)
    let sourceEnvelope := envelopeField.eval (fieldModel bn254Positive) (encodeField i)
    let targetEnvelope := (envelopeNat bn254Modulus).eval natModel (encodeNat i)
    let sourceEnvelopeCells := QuadCircuit.populate (QuadCircuit.initial i) sourceEnvelope.trace
    let targetEnvelopeCells := encodeRawNat i targetEnvelope.trace
    unless sourceEnvelopeCells == fieldCells && targetEnvelopeCells == fieldCells do
      throw (IO.userError "nested custom structure changed a full witness cell")
    cases := cases.push (fixture "envelope_bn254" x y sourceEnvelopeCells)
    cases := cases.push (fixture "envelope_nat" x y targetEnvelopeCells)
  return cases

def fixtures (path : Option System.FilePath := none) : IO Unit := do
  let cases ← fixtureCases
  match path with
  | none => IO.println (Json.arr cases).compress
  | some file =>
    IO.FS.writeFile file (Json.arr cases).compress
    IO.println (Json.mkObj [("fixtures", toJson cases.size)]).compress

def demo : IO Unit := do
  let i : QuadInput bn254Modulus :=
    ⟨Residue.ofNat bn254Positive (bn254Modulus - 1),
     Residue.ofNat bn254Positive (bn254Modulus - 2)⟩
  let fieldCells := QuadCircuit.populate (QuadCircuit.initial i)
    ((quadFieldWitgen bn254Positive).generate i)
  IO.println (fixture "quad_bn254" i.x.val i.y.val fieldCells).compress

end Witgen.Crypto.CryptoExport
