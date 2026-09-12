import Lean
import Witgen.Demo

set_option autoImplicit false

namespace Witgen.Export
open Lean Demo

def fieldJson (name : String) (ty : Json) : Json :=
  Json.mkObj [("name", .str name), ("type", ty)]

/-- Generic metadata serialization; no record-specific names or field dispatch. -/
def structTypeJson {S : Type} (encodeType : S → Json) (desc : StructDesc S) : Json :=
  Json.mkObj [("record", .str desc.name), ("fields", .arr (desc.fields.map
    (fun (name, ty) => fieldJson name (encodeType ty))).toArray)]

def typeJson : Ty → Json
  | .scalar => .str "scalar"
  | .bool => .str "bool"
  | .quad => structTypeJson (fun _ => .str "scalar") (schemaDesc .quad)
  | .modmul => structTypeJson (fun _ => .str "scalar") (schemaDesc .modmul)
  | .list element => Json.mkObj [("list", typeJson element)]

def refsJson {S : Type} {Γ : List S} : {ts : List S} → HList (Var Γ) ts → List Nat
  | _, .nil => []
  | _, .cons r rest => r.index :: refsJson rest

/-- Value serialization is separate from syntax export and used for real reference runs. -/
def valueJson {α : Type} (scalar : α → Json) : (t : Ty) → Val α t → Json
  | .scalar, x => scalar x
  | .bool, x => toJson x
  | .quad, x => Json.mkObj [("square", scalar x.square), ("output", scalar x.output)]
  | .modmul, x => Json.mkObj [("product", scalar x.product),
      ("quotient", scalar x.quotient), ("remainder", scalar x.remainder)]
  | .list t, xs => .arr (List.map (valueJson scalar t) xs).toArray

abbrev Info {S : Type} (F : Signature S) :=
  {args : List S} → {shapes : List (RegionShape S)} → {t : S} →
    F args shapes t → OpInfo

def nodeJsonWith {S : Type} (encodeType : S → Json) {F : Signature S} {Γ args : List S}
    {shapes : List (RegionShape S)} {t : S}
    (info : Info F) (op : F args shapes t) (refs : HList (Var Γ) args)
    (regions : Array Json) (next : Json) : Json :=
  let details := info op
  let literal := match details.literal with
    | none => []
    | some n => [("value", Json.str (toString n))]
  let field := match details.field with
    | none => []
    | some n => [("index", toJson n)]
  Json.mkObj [("tag", .str "let"), ("op", .str details.tag),
    ("args", toJson (refsJson refs)), ("arg_types", .arr (args.map encodeType).toArray),
    ("result", encodeType t), ("static", Json.mkObj (literal ++ field)),
    ("regions", .arr regions), ("next", next)]

def regionJsonWith {S : Type} (encodeType : S → Json) {F : Signature S} {Γ : List S} {t : S}
    (_body : Program F Γ t) (bodyJson : Json) : Json :=
  Json.mkObj [("inputs", .arr (Γ.map encodeType).toArray),
    ("output", encodeType t), ("body", bodyJson)]

mutual
  def programJsonWith {S : Type} (encodeType : S → Json) {F : Signature S} {Γ : List S} {t : S}
      (info : Info F) : Program F Γ t → Json
    | .ret r => Json.mkObj [("tag", .str "ret"), ("ref", toJson r.index)]
    | .let_ op args regions next =>
      nodeJsonWith encodeType (F := F) info op args (regionsJsonWith encodeType info regions) (programJsonWith encodeType info next)
  def regionsJsonWith {S : Type} (encodeType : S → Json) {F : Signature S} {shapes : List (RegionShape S)}
      (info : Info F) : Regions F shapes → Array Json
    | .nil => #[]
    | .cons body rest =>
      #[regionJsonWith encodeType body (programJsonWith encodeType info body)] ++ regionsJsonWith encodeType info rest
end

def moduleJsonWith {S : Type} (encodeType : S → Json) {F : Signature S} {Γ : List S} {t : S}
    (info : Info F) (name domain : String) (inputNames : List String)
    (program : Program F Γ t) (layout : Option Json := none)
    (semanticInputs : String := "nat") : Except String Json := do
  if inputNames.length != Γ.length then
    throw "input-name count differs from the typed context"
  let inputs := (inputNames.zip Γ).map fun (name, ty) => fieldJson name (encodeType ty)
  let fields := [("version", toJson (1 : Nat)), ("name", .str name),
    ("domain", .str domain), ("inputs", .arr inputs.toArray),
    ("input_semantics", .str semanticInputs),
    ("output", encodeType t), ("body", programJsonWith encodeType info program)]
  let wire := match layout with | none => [] | some value => [("wire_layout", value)]
  return Json.mkObj (fields ++ wire)

/-- Compatibility entry points for the optional toy regression sort family. -/
def programJson {F : Signature Ty} {Γ : List Ty} {t : Ty}
    (info : Info F) (p : Program F Γ t) : Json := programJsonWith typeJson info p

def moduleJson {F : Signature Ty} {Γ : List Ty} {t : Ty}
    (info : Info F) (name domain : String) (inputNames : List String)
    (program : Program F Γ t) (layout : Option Json := none)
    (semanticInputs : String := "nat") : Except String Json :=
  moduleJsonWith typeJson info name domain inputNames program layout semanticInputs

end Witgen.Export
