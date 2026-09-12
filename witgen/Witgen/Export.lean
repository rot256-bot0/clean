import Lean
import Witgen.Demo

set_option autoImplicit false

namespace Witgen.Export
open Lean Demo

def fieldJson (name : String) (ty : Json) : Json :=
  Json.mkObj [("name", .str name), ("type", ty)]

def typeJson : Ty → Json
  | .scalar => .str "scalar"
  | .bool => .str "bool"
  | .quad => Json.mkObj [("record", .str "Quad"),
      ("fields", .arr #[fieldJson "square" (.str "scalar"), fieldJson "output" (.str "scalar")])]
  | .modmul => Json.mkObj [("record", .str "ModMul"),
      ("fields", .arr #[fieldJson "product" (.str "scalar"),
        fieldJson "quotient" (.str "scalar"), fieldJson "remainder" (.str "scalar")])]
  | .list element => Json.mkObj [("list", typeJson element)]

def refsJson {Γ : List Ty} : {ts : List Ty} → HList (Var Γ) ts → List Nat
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

abbrev Info (F : Signature Ty) :=
  {args : List Ty} → {shapes : List (RegionShape Ty)} → {t : Ty} →
    F args shapes t → OpInfo

def nodeJson {F : Signature Ty} {Γ args : List Ty}
    {shapes : List (RegionShape Ty)} {t : Ty}
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
    ("args", toJson (refsJson refs)), ("arg_types", .arr (args.map typeJson).toArray),
    ("result", typeJson t), ("static", Json.mkObj (literal ++ field)),
    ("regions", .arr regions), ("next", next)]

def regionJson {F : Signature Ty} {Γ : List Ty} {t : Ty}
    (_body : Program F Γ t) (bodyJson : Json) : Json :=
  Json.mkObj [("inputs", .arr (Γ.map typeJson).toArray),
    ("output", typeJson t), ("body", bodyJson)]

mutual
  def programJson {F : Signature Ty} {Γ : List Ty} {t : Ty}
      (info : Info F) : Program F Γ t → Json
    | .ret r => Json.mkObj [("tag", .str "ret"), ("ref", toJson r.index)]
    | .let_ op args regions next =>
      nodeJson (F := F) info op args (regionsJson info regions) (programJson info next)
  def regionsJson {F : Signature Ty} {shapes : List (RegionShape Ty)}
      (info : Info F) : Regions F shapes → Array Json
    | .nil => #[]
    | .cons body rest =>
      #[regionJson body (programJson info body)] ++ regionsJson info rest
end

def moduleJson {F : Signature Ty} {Γ : List Ty} {t : Ty}
    (info : Info F) (name domain : String) (inputNames : List String)
    (program : Program F Γ t) (layout : Option Json := none)
    (semanticInputs : String := "nat") : Except String Json := do
  if inputNames.length != Γ.length then
    throw "input-name count differs from the typed context"
  let inputs := (inputNames.zip Γ).map fun (name, ty) => fieldJson name (typeJson ty)
  let fields := [("version", toJson (1 : Nat)), ("name", .str name),
    ("domain", .str domain), ("inputs", .arr inputs.toArray),
    ("input_semantics", .str semanticInputs),
    ("output", typeJson t), ("body", programJson info program)]
  let wire := match layout with | none => [] | some value => [("wire_layout", value)]
  return Json.mkObj (fields ++ wire)

end Witgen.Export
