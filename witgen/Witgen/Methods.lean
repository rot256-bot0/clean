import Witgen.Core
import Lean

/-! Optional, acyclic, typed shared methods over the unchanged generic core.
Every implementation is finite Program data. Calls have no body/host closure payload. -/
namespace Witgen.Methods

structure MethodSig (S : Type) where
  name : String
  args : List S
  result : S
  deriving DecidableEq, Repr

inductive Ref {S : Type} : List (MethodSig S) → MethodSig S → Type where
  | zero : Ref (m :: ms) m
  | succ : Ref ms m → Ref (n :: ms) m

namespace Ref

def index : Ref ms m → Nat
  | .zero => 0
  | .succ r => r.index + 1

def signature {S : Type} {ms : List (MethodSig S)} {m : MethodSig S} (_ : Ref ms m) :
    MethodSig S := m

def get {S : Type} {V : MethodSig S → Type} {ms : List (MethodSig S)} {m : MethodSig S} :
    Ref ms m → HList V ms → V m
  | .zero, .cons x _ => x
  | .succ r, .cons _ xs => r.get xs

theorem member {S : Type} {ms : List (MethodSig S)} {m : MethodSig S}
    (r : Ref ms m) : m ∈ ms := by
  induction r with
  | zero => exact List.mem_cons_self
  | succ r ih => exact List.mem_cons_of_mem _ ih

theorem index_lt {S : Type} {ms : List (MethodSig S)} {m : MethodSig S}
    (r : Ref ms m) : r.index < ms.length := by
  induction r with
  | zero => simp [index]
  | succ r ih => simpa [index] using Nat.succ_lt_succ ih

end Ref

inductive CallOp {S : Type} (ms : List (MethodSig S)) : Signature S where
  | call (ref : Ref ms m) : CallOp ms m.args [] m.result

abbrev WithCalls (F : Signature S) (ms : List (MethodSig S)) : Signature S :=
  SigSum F (CallOp ms)

inductive Library {S : Type} (F : Signature S) : List (MethodSig S) → Type where
  | nil : Library F []
  | cons (prior : Library F ms) (sig : MethodSig S)
      (fresh : sig.name ∉ ms.map MethodSig.name)
      (body : Program (WithCalls F ms) sig.args sig.result) : Library F (sig :: ms)

abbrev MethodValue (V : S → Type) (m : MethodSig S) := HList V m.args → V m.result

def callModel (values : HList (MethodValue V) ms) : Model (CallOp ms) V where
  eval := fun (.call r) args _ => r.get values args

def Library.eval {F : Signature S} (lib : Library F ms) (primitive : Model F V) :
    HList (MethodValue V) ms :=
  match lib with
  | .nil => .nil
  | .cons prior _ _ body =>
    let values := prior.eval primitive
    .cons (body.eval (primitive.sum (callModel values))) values

def Library.model {F : Signature S} (lib : Library F ms) (primitive : Model F V) :
    Model (WithCalls F ms) V := primitive.sum (callModel (lib.eval primitive))

@[simp] theorem Library.eval_cons {F : Signature S} (lib : Library F ms)
    (primitive : Model F V) (m : MethodSig S) (fresh)
    (body : Program (WithCalls F ms) m.args m.result) :
    (Library.cons lib m fresh body).eval primitive =
      .cons (body.eval (lib.model primitive)) (lib.eval primitive) := rfl

/-- Evaluating a head call is evaluating its registered finite body under prior methods. -/
@[simp] theorem Library.call_head {F : Signature S} (lib : Library F ms)
    (primitive : Model F V) (m : MethodSig S) (fresh)
    (body : Program (WithCalls F ms) m.args m.result) (xs : HList V m.args) :
    ((Library.cons lib m fresh body).model primitive).eval
      (.inr (.call .zero)) xs .nil = body.eval (lib.model primitive) xs := rfl

/-- No duplicate names can enter a library, including unreachable definitions. -/
theorem Library.names_unique {F : Signature S} (lib : Library F ms) :
    (ms.map MethodSig.name).Nodup := by
  induction lib with
  | nil => exact List.nodup_nil
  | cons prior m fresh body ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩

/-- Name uniqueness implies a unique typed link, not merely a unique signature string. -/
theorem Ref.unique_of_names {S : Type} {ms : List (MethodSig S)} {m n : MethodSig S}
    (r : Ref ms m) (q : Ref ms n) (unique : (ms.map MethodSig.name).Nodup)
    (same : m.name = n.name) : m = n ∧ HEq r q := by
  induction r generalizing n with
  | zero =>
    cases q with
    | zero => exact ⟨rfl, HEq.rfl⟩
    | succ q =>
      have fresh := (List.nodup_cons.mp unique).1
      exact (fresh (same ▸ List.mem_map.mpr ⟨_, q.member, rfl⟩)).elim
  | succ r ih =>
    cases q with
    | zero =>
      have fresh := (List.nodup_cons.mp unique).1
      exact (fresh (same ▸ List.mem_map.mpr ⟨_, r.member, rfl⟩)).elim
    | succ q =>
      obtain ⟨eq, h⟩ := ih q (List.nodup_cons.mp unique).2 same
      cases eq
      cases eq_of_heq h
      exact ⟨rfl, HEq.rfl⟩

theorem Library.ref_unique {F : Signature S} (lib : Library F ms)
    (r : Ref ms m) (q : Ref ms n) (same : m.name = n.name) : HEq r q :=
  (r.unique_of_names q lib.names_unique same).2

/-- A method body can only refer to the prior library, which excludes its own name. -/
theorem Library.earlier_only {F : Signature S} (_lib : Library F ms)
    (m : MethodSig S) (fresh : m.name ∉ ms.map MethodSig.name)
    (r : Ref ms n) : n.name ≠ m.name := by
  intro h
  apply fresh
  rw [← h]
  exact List.mem_map.mpr ⟨n, r.member, rfl⟩

/-- Generic call/body substitution law, including aliasing of actual arguments. -/
theorem call_substitution {F : Signature S} (lib : Library F ms) (primitive : Model F V)
    (body : Program (WithCalls F ms) args result) (actual : HList (Var Γ) args)
    (env : HList V Γ) :
    (body.subst (fun r => r.get actual)).eval (lib.model primitive) env =
      body.eval (lib.model primitive) (actual.map (fun r => r.get env)) := by
  apply Program.eval_subst
  intro s r
  exact (r.get_map (fun v => v.get env) actual).symm

/-- Semantic contracts for calls relate complete typed argument vectors. -/
def MethodRel {S : Type} {V W : S → Type} (R : ∀ s, V s → W s → Prop) (m : MethodSig S)
    (a : MethodValue V m) (b : MethodValue W m) : Prop :=
  ∀ xs ys, HList.Rel R xs ys → R m.result (a xs) (b ys)

theorem Ref.get_related {V W : MethodSig S → Type}
    (R : ∀ m, V m → W m → Prop) (r : Ref ms m)
    (xs : HList V ms) (ys : HList W ms) (hr : HList.Rel R xs ys) :
    R m (r.get xs) (r.get ys) := by
  induction r with
  | zero => cases xs; cases ys; exact hr.1
  | succ r ih => cases xs; cases ys; exact ih _ _ hr.2

mutual
  theorem eval_related {F : Signature S} (M : Model F V) (N : Model F W)
      (R : ∀ s, V s → W s → Prop) (law : M.Respects N (Handler.id F) R)
      (p : Program F Γ t) (xs : HList V Γ) (ys : HList W Γ) (hr : HList.Rel R xs ys) :
      R t (p.eval M xs) (p.eval N ys) := by
    cases p with
    | ret r => exact r.get_related R xs ys hr
    | let_ op args regions next =>
      apply eval_related M N R law next
      exact ⟨law op _ _ _ _ (HList.map_get_related R xs ys hr args)
        (regions_related M N R law regions), hr⟩
  theorem regions_related {F : Signature S} (M : Model F V) (N : Model F W)
      (R : ∀ s, V s → W s → Prop) (law : M.Respects N (Handler.id F) R)
      (regions : Regions F shapes) :
      HList.Rel (BodyRel R) (regions.eval M) (regions.eval N) := by
    cases regions with
    | nil => trivial
    | cons body rest => exact ⟨fun xs ys hr => eval_related M N R law body xs ys hr,
        regions_related M N R law rest⟩
end

theorem withCalls_respects {F : Signature S} (M : Model F V) (N : Model F W)
    (R : ∀ s, V s → W s → Prop) (law : M.Respects N (Handler.id F) R)
    (xs : HList (MethodValue V) ms) (ys : HList (MethodValue W) ms)
    (hr : HList.Rel (MethodRel R) xs ys) :
    (M.sum (callModel xs)).Respects (N.sum (callModel ys))
      (Handler.id (WithCalls F ms)) R := by
  intro args shapes s op as bs fs gs hab hfg
  cases op with
  | inl op => exact law op as bs fs gs hab hfg
  | inr op =>
    cases op with | call r => exact r.get_related (MethodRel R) xs ys hr as bs hab

/-- Primitive refinement lifts through all stored bodies, inductively in dependency order. -/
theorem Library.eval_related {F : Signature S} (lib : Library F ms)
    (M : Model F V) (N : Model F W) (R : ∀ s, V s → W s → Prop)
    (law : M.Respects N (Handler.id F) R) :
    HList.Rel (MethodRel R) (lib.eval M) (lib.eval N) := by
  induction lib with
  | nil => trivial
  | cons prior m fresh body ih =>
    exact ⟨fun xs ys hr => Methods.eval_related _ _ R
      (withCalls_respects M N R law _ _ ih) body xs ys hr, ih⟩

/-- Whole callers refine without expanding any call node. -/
theorem Library.caller_refinement {F : Signature S} (lib : Library F ms)
    (M : Model F V) (N : Model F W) (R : ∀ s, V s → W s → Prop)
    (law : M.Respects N (Handler.id F) R) (p : Program (WithCalls F ms) Γ t)
    (xs : HList V Γ) (ys : HList W Γ) (hr : HList.Rel R xs ys) :
    R t (p.eval (lib.model M) xs) (p.eval (lib.model N) ys) :=
  Methods.eval_related _ _ R
    (withCalls_respects M N R law _ _ (lib.eval_related M N R law)) p xs ys hr

open Lean

/-- Only operation-local data; the serializer owns references, types, and nested regions. -/
abbrev OpCodec {S : Type} (F : Signature S) :=
  {args : List S} → {shapes : List (RegionShape S)} → {result : S} →
    F args shapes result → Json

def callCodec {S : Type} {ms : List (MethodSig S)} : OpCodec (CallOp ms) :=
  fun (.call r) => Json.mkObj [("op", .str "method.call"),
    ("static", Json.mkObj [("name", .str r.signature.name), ("index", toJson r.index)])]

def withCallsCodec {F : Signature S} {ms : List (MethodSig S)} (primitive : OpCodec F) :
    OpCodec (WithCalls F ms) := fun op => match op with
  | .inl op => primitive op
  | .inr op => callCodec op

def refsJson {S : Type} {Γ : List S} : {args : List S} → HList (Var Γ) args → List Nat
  | _, .nil => []
  | _, .cons r rs => r.index :: refsJson rs

mutual
  def programJson {S : Type} {F : Signature S} {Γ : List S} {t : S}
      (encodeType : S → Json) (codec : OpCodec F) : Program F Γ t → Json
    | .ret r => Json.mkObj [("tag", .str "ret"), ("ref", toJson r.index)]
    | @Program.let_ _ _ args _ result _ _ op refs regions next =>
      (codec op).mergeObj (Json.mkObj [("tag", .str "let"),
        ("args", toJson (refsJson refs)), ("arg_types", toJson (args.map encodeType)),
        ("result", encodeType result), ("regions", .arr (regionsJson encodeType codec regions)),
        ("next", programJson encodeType codec next)])
  def regionsJson {S : Type} {F : Signature S} {shapes : List (RegionShape S)}
      (encodeType : S → Json) (codec : OpCodec F) : Regions F shapes → Array Json
    | .nil => #[]
    | @Regions.cons _ _ _ sh body rest =>
      #[Json.mkObj [("inputs", toJson (sh.inputs.map encodeType)),
        ("output", encodeType sh.output), ("body", programJson encodeType codec body)]] ++
        regionsJson encodeType codec rest
end

/-- Dependency order; each definition is emitted exactly once, never in callers. -/
def libraryJson {S : Type} {F : Signature S} {ms : List (MethodSig S)}
    (encodeType : S → Json) (codec : OpCodec F) : Library F ms → Array Json
  | .nil => #[]
  | .cons prior m _ body => libraryJson encodeType codec prior ++ #[Json.mkObj
      [("name", .str m.name), ("args", toJson (m.args.map encodeType)),
       ("result", encodeType m.result), ("body", programJson encodeType (withCallsCodec codec) body)]]

theorem libraryJson_size {S : Type} {F : Signature S} {ms : List (MethodSig S)}
    (encodeType : S → Json) (codec : OpCodec F) (lib : Library F ms) :
    (libraryJson encodeType codec lib).size = ms.length := by
  induction lib with
  | nil => rfl
  | cons prior m fresh body ih => simp [libraryJson, ih]

def moduleJson {S : Type} {F : Signature S} {ms : List (MethodSig S)}
    {Γ : List S} {t : S} (encodeType : S → Json) (codec : OpCodec F)
    (lib : Library F ms) (name : String) (inputNames : List String)
    (p : Program (WithCalls F ms) Γ t) : Except String Json := do
  if inputNames.length != Γ.length then throw "input-name count differs from the typed context"
  return Json.mkObj [("version", toJson (2 : Nat)), ("name", .str name),
    ("inputs", toJson ((inputNames.zip Γ).map fun (n, s) =>
      Json.mkObj [("name", .str n), ("type", encodeType s)])),
    ("output", encodeType t), ("methods", .arr (libraryJson encodeType codec lib)),
    ("body", programJson encodeType (withCallsCodec codec) p)]

end Witgen.Methods
