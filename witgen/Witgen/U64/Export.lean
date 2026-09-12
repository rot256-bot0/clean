import Witgen.U64.Lowering
import Witgen.Typed.Export

namespace Witgen.U64
open Witgen.Typed Witgen.Methods Lean

def wordJson (w : Word4) : Json :=
  .arr #[.str (toString w.l0.toNat), .str (toString w.l1.toNat),
    .str (toString w.l2.toNat), .str (toString w.l3.toNat)]

/-- All static field literals are already concrete four-word data. -/
def codec : OpCodec U64Op := fun op =>
  let (tag, data) : String × List (String × Json) := match op with
    | .word v => ("u64.word", [("value", .str (toString v.toNat))])
    | .flag v => ("u64.flag", [("value", toJson v)])
    | .literal v => ("u64.literal", [("limbs", wordJson v)])
    | .get i => ("u64.get", [("limb", toJson i.val)])
    | .pack => ("u64.pack", [])
    | .adcWord => ("u64.adcWord", [])
    | .adcFlag => ("u64.adcFlag", [])
    | .sbbWord => ("u64.sbbWord", [])
    | .sbbFlag => ("u64.sbbFlag", [])
    | .or => ("u64.or", [])
    | .not => ("u64.not", [])
    | .select => ("u64.select", [])
    | .bitAt => ("u64.bitAt", [])
    | .repeat n => ("u64.repeat", [("count", toJson n)])
    | .toWord f => ("u64.toWord", [("field", toJson f.val)])
    | .fromWord f => ("u64.fromWord", [("field", toJson f.val)])
    | .fieldLiteral f v => ("u64.fieldLiteral", [("field", toJson f.val), ("limbs", wordJson v)])
  Json.mkObj [("op", .str tag), ("static", Json.mkObj data)]

def sourceAdd (f : FieldId) : Program AnyFieldOp [.field f,.field f] (.field f) :=
  .let_ (.field f .add) h![.zero,.succ .zero] .nil (.ret .zero)

def sourceMul (f : FieldId) : Program AnyFieldOp [.field f,.field f] (.field f) :=
  .let_ (.field f .mul) h![.zero,.succ .zero] .nil (.ret .zero)

def sourceSquare (f : FieldId) : Program AnyFieldOp [.field f] (.field f) :=
  .let_ (.field f .square) h![.zero] .nil (.ret .zero)

def callerJson {Γ t} (name : String) (inputNames : List String)
    (p : Program AnyFieldOp Γ t) (accepted : (p.mapHandler? lower).isSome) : Json :=
  Json.mkObj [("name", .str name),
    ("inputs", toJson ((inputNames.zip Γ).map fun (n,t) =>
      Json.mkObj [("name", .str n), ("type", typeJson t)])),
    ("output", typeJson t),
    ("body", programJson typeJson (withCallsCodec codec) (compile p accepted))]

/-- One shared registry, nine source callers. No duplicated method definitions. -/
def bundleJson : Json :=
  Json.mkObj [("version", toJson (2 : Nat)), ("kind", .str "u64-shared-library"),
    ("methods", .arr (libraryJson typeJson codec allLibrary)),
    ("programs", .arr (([bn254Fr,secpBase,secpScalar].flatMap fun f =>
      [callerJson ("field." ++ toString f.val ++ ".add") ["a","b"] (sourceAdd f) (by rfl),
       callerJson ("field." ++ toString f.val ++ ".mul") ["a","b"] (sourceMul f) (by rfl),
       callerJson ("field." ++ toString f.val ++ ".square") ["a"] (sourceSquare f) (by rfl)]).toArray))]

end Witgen.U64
