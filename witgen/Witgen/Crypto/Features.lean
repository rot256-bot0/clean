import Witgen.Crypto.Field
import Witgen.Structs

namespace Witgen.Crypto

inductive Ty where
  | scalar | quad | envelope
  deriving Repr, DecidableEq

/-- Native circuit witness type; its intermediate square is a required cell. -/
structure QuadWitness (α : Type) where
  square : α
  output : α
  deriving Repr, DecidableEq

structure QuadEnvelope (α : Type) where
  trace : QuadWitness α
  deriving Repr, DecidableEq

@[reducible] def Val (α : Type) : Ty → Type
  | .scalar => α
  | .quad => QuadWitness α
  | .envelope => QuadEnvelope α

def Val.map (f : α → β) : {t : Ty} → Val α t → Val β t
  | .scalar, x => f x
  | .quad, x => ⟨f x.square, f x.output⟩
  | .envelope, x => ⟨⟨f x.trace.square, f x.trace.output⟩⟩

/-- A schema key, not a record-specific operation family. -/
inductive Schema where
  | quad | envelope
  deriving Repr, DecidableEq

@[reducible] def schemaDesc : Schema → StructDesc Ty
  | .quad => {
      name := "QuadWitness"
      result := .quad
      fields := [("square", .scalar), ("output", .scalar)] }
  | .envelope => {
      name := "QuadEnvelope"
      result := .envelope
      fields := [("trace", .quad)] }

def schemaRepr (α : Type) : (k : Schema) → StructRepr (Val α) (schemaDesc k)
  | .quad => {
      pack := fun | .cons a (.cons b .nil) => ⟨a, b⟩
      unpack := fun w => .cons w.square (.cons w.output .nil)
      unpack_pack := by intro xs; cases xs with | cons a xs => cases xs with
        | cons b xs => cases xs; rfl
      pack_unpack := by intro w; cases w; rfl }
  | .envelope => {
      pack := fun | .cons w .nil => ⟨w⟩
      unpack := fun e => .cons e.trace .nil
      unpack_pack := by intro xs; cases xs with | cons w xs => cases xs; rfl
      pack_unpack := by intro e; cases e; rfl }

inductive FieldOp : Signature Ty where
  | const (n : Nat) : FieldOp [] [] .scalar
  | add : FieldOp [.scalar, .scalar] [] .scalar
  | mul : FieldOp [.scalar, .scalar] [] .scalar

inductive NatOp : Signature Ty where
  | const (n : Nat) : NatOp [] [] .scalar
  | add : NatOp [.scalar, .scalar] [] .scalar
  | mul : NatOp [.scalar, .scalar] [] .scalar
  | mod : NatOp [.scalar, .scalar] [] .scalar

abbrev FieldSig := SigSum FieldOp (StructOp schemaDesc)
abbrev NatSig := SigSum NatOp (StructOp schemaDesc)

def fieldScalarModel {p : Nat} (hp : 0 < p) : Model FieldOp (Val (Fin p)) where
  eval := fun op args _ => match op, args with
    | .const n, .nil => Residue.ofNat hp n
    | .add, .cons a (.cons b .nil) => Residue.add a b
    | .mul, .cons a (.cons b .nil) => Residue.mul a b

def natScalarModel : Model NatOp (Val Nat) where
  eval := fun op args _ => match op, args with
    | .const n, .nil => n
    | .add, .cons a (.cons b .nil) => a + b
    | .mul, .cons a (.cons b .nil) => a * b
    | .mod, .cons a (.cons b .nil) => a % b

def fieldModel {p : Nat} (hp : 0 < p) : Model FieldSig (Val (Fin p)) :=
  (fieldScalarModel hp).sum (structModel (schemaRepr (Fin p)))

def natModel : Model NatSig (Val Nat) :=
  natScalarModel.sum (structModel (schemaRepr Nat))

/-- Representation relation includes the entire native record. -/
def Graph (f : α → β) (t : Ty) (x : Val α t) (y : Val β t) : Prop :=
  Val.map f x = y

theorem graph_env (f : α → β) (xs : HList (Val α) Γ) :
    HList.Rel (Graph f) xs (xs.map (Val.map f)) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨rfl, ih⟩

theorem graph_env_eq (f : α → β) (xs : HList (Val α) Γ) (ys : HList (Val β) Γ)
    (h : HList.Rel (Graph f) xs ys) : xs.map (Val.map f) = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys =>
      have hx : Val.map f x = y := h.1
      simp only [HList.map, hx, ih ys h.2]

/-- Instantiate the reusable structural feature's generic naturality theorem. -/
theorem struct_respects (f : α → β) :
    (structModel (schemaRepr α)).Respects (structModel (schemaRepr β))
      (Handler.id _) (Graph f) := by
  apply structModel_respects
  · intro k xs ys hr
    rw [← graph_env_eq f xs ys hr]
    cases k with
    | quad => cases xs with
      | cons a xs => cases xs with
        | cons b xs => cases xs; rfl
    | envelope => cases xs with
      | cons w xs => cases xs; rfl
  · intro k x y hr
    cases k with
    | quad =>
      change Val.map f x = y at hr
      rw [← hr]
      exact ⟨rfl, rfl, trivial⟩
    | envelope =>
      change Val.map f x = y at hr
      rw [← hr]
      exact ⟨rfl, trivial⟩

/-- All references, without assuming any particular sort universe. -/
def allRefs {S : Type} : (Γ : List S) → HList (Var Γ) Γ
  | [] => .nil
  | _ :: Γ => .cons .zero ((allRefs Γ).map (fun r => .succ r))

theorem hmap_hmap {S : Type} {V W U : S → Type} {Γ : List S}
    (f : {s : S} → V s → W s) (g : {s : S} → W s → U s) (xs : HList V Γ) :
    (xs.map f).map g = xs.map (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [HList.map, ih]

theorem allRefs_eval {S : Type} {Γ : List S} {V : S → Type} (xs : HList V Γ) :
    (allRefs Γ).map (fun r => r.get xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [allRefs, HList.map, hmap_hmap, Var.get, ih]

def emit {S : Type} {F : Signature S} {args : List S} {shapes : List (RegionShape S)}
    {t : S} (op : F args shapes t) (regions : Regions F shapes) : Program F args t :=
  .let_ op (allRefs args) regions (.ret .zero)

theorem emit_eval {S : Type} {F : Signature S} {V : S → Type}
    {args : List S} {shapes : List (RegionShape S)} {t : S}
    (M : Model F V) (op : F args shapes t) (regions : Regions F shapes) (xs : HList V args) :
    (emit op regions).eval M xs = M.eval op xs (regions.eval M) := by
  simp only [emit, Program.eval, allRefs_eval, Var.get]

/-- One field instruction becomes unbounded Nat arithmetic plus explicit reduction. -/
def fieldScalarToNat (p : Nat) : Template FieldOp NatSig
  | _, _, _, .const n, _ => emit (.inl (.const (n % p))) .nil
  | _, _, _, .add, _ =>
      .let_ (.inl .add) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
      .let_ (.inl (.const p)) .nil .nil <|
      .let_ (.inl .mod) (.cons (.succ .zero) (.cons .zero .nil)) .nil (.ret .zero)
  | _, _, _, .mul, _ =>
      .let_ (.inl .mul) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
      .let_ (.inl (.const p)) .nil .nil <|
      .let_ (.inl .mod) (.cons (.succ .zero) (.cons .zero .nil)) .nil (.ret .zero)

def fieldToNat (p : Nat) : Template FieldSig NatSig
  | _, _, _, .inl op, regions => fieldScalarToNat p op regions
  | _, _, _, .inr op, regions => emit (.inr op) regions

theorem fieldToNat_law {p : Nat} (hp : 0 < p) :
    Template.Respects (fieldModel hp) natModel (fieldToNat p) (Graph Fin.val) := by
  intro args shapes t op xs ys fs regions hr hb
  cases op with
  | inr op =>
    simp only [fieldToNat, emit_eval]
    exact struct_respects Fin.val op xs ys fs (regions.eval natModel) hr hb
  | inl op =>
    rw [← graph_env_eq Fin.val xs ys hr]
    cases op with
    | const n => cases xs; rfl
    | add => cases xs with
      | cons a xs => cases xs with
        | cons b xs => cases xs; rfl
    | mul => cases xs with
      | cons a xs => cases xs with
        | cons b xs => cases xs; rfl

/-- Generic in both positive modulus and finite feature/subprogram AST. -/
theorem fieldToNat_correct {p : Nat} (hp : 0 < p)
    (program : Program FieldSig Γ t) (env : HList (Val (Fin p)) Γ) :
    Val.map Fin.val (program.eval (fieldModel hp) env) =
      (program.lower (fieldToNat p)).eval natModel (env.map (Val.map Fin.val)) :=
  Program.eval_lower_related (fieldToNat p) (fieldModel hp) natModel
    (Graph Fin.val) (fieldToNat_law hp) program env _ (graph_env Fin.val env)

def fieldNatLowering {p : Nat} (hp : 0 < p) :
    CertifiedLowering (fieldModel hp) natModel (Graph Fin.val) :=
  .ofTemplate _ _ (fieldToNat p) _ (fieldToNat_law hp)

end Witgen.Crypto
