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

/-- Persistent update of one typed field; the original environment is unchanged. -/
def Var.set {S : Type} {V : S → Type} {Γ : List S} {t : S} :
    Var Γ t → HList V Γ → V t → HList V Γ
  | .zero, .cons _ xs, value => .cons value xs
  | .succ r, .cons x xs, value => .cons x (r.set xs value)

@[simp] theorem Var.get_set {S : Type} {V : S → Type} {Γ : List S} {t : S} (r : Var Γ t)
    (xs : HList V Γ) (value : V t) : r.get (r.set xs value) = value := by
  induction r with
  | zero => cases xs; rfl
  | succ r ih => cases xs with | cons x xs => exact ih xs value

@[simp] theorem Var.set_get {S : Type} {V : S → Type} {Γ : List S} {t : S} (r : Var Γ t)
    (xs : HList V Γ) : r.set xs (r.get xs) = xs := by
  induction r with
  | zero => cases xs; rfl
  | succ r ih => cases xs with | cons x xs => simp only [Var.set, Var.get, ih]

theorem Var.set_related {S : Type} {V W : S → Type}
    {Γ : List S} {t : S} (R : ∀ s, V s → W s → Prop) (r : Var Γ t)
    (xs : HList V Γ) (ys : HList W Γ) (x : V t) (y : W t)
    (hxy : R t x y) (h : HList.Rel R xs ys) :
    HList.Rel R (r.set xs x) (r.set ys y) := by
  induction r with
  | zero =>
    cases xs with | cons a xs => cases ys with | cons b ys => exact ⟨hxy, h.2⟩
  | succ r ih =>
    cases xs with | cons a xs => cases ys with | cons b ys => exact ⟨h.1, ih xs ys x y hxy h.2⟩

theorem Var.get_set_other {S : Type} {V : S → Type} {Γ : List S} {s t : S}
    (read : Var Γ s) (write : Var Γ t) (xs : HList V Γ) (value : V t)
    (hne : read.index ≠ write.index) : read.get (write.set xs value) = read.get xs := by
  induction write generalizing s with
  | zero =>
    cases read with
    | zero => exact False.elim (hne rfl)
    | succ read => cases xs; rfl
  | succ write ih =>
    cases read with
    | zero => cases xs; rfl
    | succ read =>
      cases xs with
      | cons x xs =>
        apply ih read xs value
        intro h
        apply hne
        simp [Var.index, h]

@[simp] theorem Var.set_set {S : Type} {V : S → Type} {Γ : List S} {t : S}
    (r : Var Γ t) (xs : HList V Γ) (x y : V t) : r.set (r.set xs x) y = r.set xs y := by
  induction r with
  | zero => cases xs; rfl
  | succ r ih => cases xs with | cons a xs => simp only [Var.set, ih]

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
  | set (schema : Schema) {name : String} {t : S}
      (field : FieldRef (desc schema).fields name t) :
      StructOp desc [(desc schema).result, t] [] (desc schema).result

/-- Explicit isomorphism: no projection defaults, casts, or hidden record dispatch. -/
structure StructRepr {S : Type} (V : S → Type) (d : StructDesc S) where
  pack : HList V d.sorts → V d.result
  unpack : V d.result → HList V d.sorts
  unpack_pack : ∀ xs, unpack (pack xs) = xs
  pack_unpack : ∀ x, pack (unpack x) = x

def StructRepr.set (r : StructRepr V d) (field : FieldRef d.fields name t)
    (record : V d.result) (value : V t) : V d.result :=
  r.pack (field.ref.set (r.unpack record) value)

@[simp] theorem StructRepr.get_set (r : StructRepr V d)
    (field : FieldRef d.fields name t) (record : V d.result) (value : V t) :
    field.ref.get (r.unpack (r.set field record value)) = value := by
  simp [StructRepr.set, r.unpack_pack]

@[simp] theorem StructRepr.set_get (r : StructRepr V d)
    (field : FieldRef d.fields name t) (record : V d.result) :
    r.set field record (field.ref.get (r.unpack record)) = record := by
  simp [StructRepr.set, r.pack_unpack]

def structModel {desc : Schema → StructDesc S}
    (repr : ∀ k, StructRepr V (desc k)) : Model (StructOp desc) V where
  eval := fun op args _ => match op, args with
    | .make k, xs => (repr k).pack xs
    | .get k field, .cons x .nil => field.ref.get ((repr k).unpack x)
    | .set k field, .cons x (.cons value .nil) => (repr k).set field x value

theorem StructRepr.get_set_other (r : StructRepr V d)
    (field : FieldRef d.fields name t) (other : FieldRef d.fields otherName u)
    (record : V d.result) (value : V t)
    (hne : other.ref.index ≠ field.ref.index) :
    other.ref.get (r.unpack (r.set field record value)) = other.ref.get (r.unpack record) := by
  simp only [StructRepr.set, r.unpack_pack]
  exact other.ref.get_set_other field.ref _ value hne

@[simp] theorem StructRepr.set_set (r : StructRepr V d)
    (field : FieldRef d.fields name t) (record : V d.result) (x y : V t) :
    r.set field (r.set field record x) y = r.set field record y := by
  simp [StructRepr.set, r.unpack_pack]

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
  | set k field =>
    cases xs with
    | cons x xs => cases xs with
      | cons value xs =>
        cases xs
        cases ys with
        | cons y ys => cases ys with
          | cons value' ys =>
            cases ys
            exact pack k _ _ (field.ref.set_related R _ _ _ _ hr.2.1 (unpack k x y hr.1))

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
