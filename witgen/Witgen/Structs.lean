import Witgen.Core

/-! Optional structure feature. Schemas and their sort universe belong to callers;
construction and projection are the only operations, independent of schema count. -/
namespace Witgen

structure StructDesc (S : Type) where
  name : String
  result : S
  fields : List (String × S)
  names_nodup : (fields.map Prod.fst).Nodup := by decide

def StructDesc.sorts (d : StructDesc S) : List S := d.fields.map Prod.snd

inductive FieldRef {S : Type} : List (String × S) → String → S → Type where
  | here : FieldRef ((name, t) :: rest) name t
  | there : FieldRef rest name t → FieldRef (field :: rest) name t

def FieldRef.ref : FieldRef fields name t → Var (fields.map Prod.snd) t
  | .here => .zero
  | .there f => .succ f.ref

class NamedField {S : Type} (fields : List (String × S)) (name : String) (t : outParam S) where
  ref : FieldRef fields name t

instance : NamedField ((name, t) :: rest) name t := ⟨.here⟩
instance (priority := low) [NamedField rest name t] : NamedField (field :: rest) name t :=
  ⟨.there NamedField.ref⟩

/-- Ordered named arguments check both field names and their sorts. -/
inductive NamedArgs {S : Type} (V : S → Type) : List (String × S) → Type where
  | nil : NamedArgs V []
  | cons (name : String) {t : S} {rest : List (String × S)} :
      V t → NamedArgs V rest → NamedArgs V ((name, t) :: rest)

def NamedArgs.values : NamedArgs V fields → HList V (fields.map Prod.snd)
  | .nil => .nil
  | .cons _ x xs => .cons x xs.values

inductive StructOp {S : Type} {Schema : Type}
    (desc : Schema → StructDesc S) : Signature S where
  | make (schema : Schema) : StructOp desc (desc schema).sorts [] (desc schema).result
  | get (schema : Schema) {name : String} {t : S}
      (field : FieldRef (desc schema).fields name t) : StructOp desc [(desc schema).result] [] t

/-- Explicit isomorphism: no projection defaults, casts, or hidden record dispatch. -/
structure StructRepr {S : Type} (V : S → Type) (d : StructDesc S) where
  pack : HList V d.sorts → V d.result
  unpack : V d.result → HList V d.sorts
  unpack_pack : ∀ xs, unpack (pack xs) = xs
  pack_unpack : ∀ x, pack (unpack x) = x

def structModel {desc : Schema → StructDesc S}
    (repr : ∀ k, StructRepr V (desc k)) : Model (StructOp desc) V where
  eval := fun op args _ => match op, args with
    | .make k, xs => (repr k).pack xs
    | .get k field, .cons x .nil => field.ref.get ((repr k).unpack x)

@[simp] theorem StructRepr.get_pack (r : StructRepr V d)
    (field : FieldRef d.fields name t) (xs : HList V d.sorts) :
    field.ref.get (r.unpack (r.pack xs)) = field.ref.get xs := by rw [r.unpack_pack]

/-- Generic local representation contract for *all* schemas and fields. -/
theorem structModel_respects {desc : Schema → StructDesc S}
    (a : ∀ k, StructRepr V (desc k)) (b : ∀ k, StructRepr W (desc k))
    (R : ∀ s, V s → W s → Prop)
    (pack : ∀ k xs ys, HList.Rel R xs ys → R _ ((a k).pack xs) ((b k).pack ys))
    (unpack : ∀ k x y, R _ x y → HList.Rel R ((a k).unpack x) ((b k).unpack y)) :
    (structModel a).Respects (structModel b) (Handler.id _) R := by
  intro args shapes t op xs ys fs gs hr _
  cases op with
  | make k => exact pack k xs ys hr
  | get k field =>
    cases xs with
    | cons x xs =>
      cases xs
      cases ys with
      | cons y ys =>
        cases ys
        exact field.ref.get_related R _ _ (unpack k x y hr.1)

/-- The unchanged core theorem lifts the local representation laws through every
finite program, including closed nested regions and explicit captures. -/
def structLowering {desc : Schema → StructDesc S}
    (a : ∀ k, StructRepr V (desc k)) (b : ∀ k, StructRepr W (desc k))
    (R : ∀ s, V s → W s → Prop)
    (pack : ∀ k xs ys, HList.Rel R xs ys → R _ ((a k).pack xs) ((b k).pack ys))
    (unpack : ∀ k x y, R _ x y → HList.Rel R ((a k).unpack x) ((b k).unpack y)) :
    CertifiedLowering (structModel a) (structModel b) R :=
  .ofHandler _ _ (Handler.id _) R (structModel_respects a b R pack unpack)

end Witgen
