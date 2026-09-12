import Witgen.Authoring
import Witgen.Arithmetic

/-! Optional typed demonstration vocabulary; none of these sorts or features
belong to the generic kernel. Payloads are finite data, never semantic closures. -/
namespace Witgen.Demo
open Arithmetic

inductive Ty where
  | scalar | bool | quad | modmul | list (element : Ty)
  deriving Repr, DecidableEq

structure Quad (α : Type) where
  square : α
  output : α
  deriving Repr, DecidableEq

structure ModMul (α : Type) where
  product : α
  quotient : α
  remainder : α
  deriving Repr, DecidableEq

@[reducible] def Val (α : Type) : Ty → Type
  | .scalar => α
  | .bool => Bool
  | .quad => Quad α
  | .modmul => ModMul α
  | .list t => List (Val α t)

def Val.map (f : α → β) : {t : Ty} → Val α t → Val β t
  | .scalar, x => f x
  | .bool, x => x
  | .quad, x => ⟨f x.square, f x.output⟩
  | .modmul, x => ⟨f x.product, f x.quotient, f x.remainder⟩
  | .list _, xs => List.map (Val.map f) xs

inductive FieldOp : Signature Ty where
  | const (n : Nat) : FieldOp [] [] .scalar
  | add : FieldOp [.scalar, .scalar] [] .scalar
  | mul : FieldOp [.scalar, .scalar] [] .scalar
  | eq : FieldOp [.scalar, .scalar] [] .bool

inductive NatOp : Signature Ty where
  | const (n : Nat) : NatOp [] [] .scalar
  | add : NatOp [.scalar, .scalar] [] .scalar
  | mul : NatOp [.scalar, .scalar] [] .scalar
  | div : NatOp [.scalar, .scalar] [] .scalar
  | mod : NatOp [.scalar, .scalar] [] .scalar
  | eq : NatOp [.scalar, .scalar] [] .bool

inductive WordOp : Signature Ty where
  | const (n : Nat) : WordOp [] [] .scalar
  | add : WordOp [.scalar, .scalar] [] .scalar
  | mul : WordOp [.scalar, .scalar] [] .scalar
  | div : WordOp [.scalar, .scalar] [] .scalar
  | mod : WordOp [.scalar, .scalar] [] .scalar
  | eq : WordOp [.scalar, .scalar] [] .bool

inductive Schema where
  | quad | modmul
  deriving Repr, DecidableEq

@[reducible] def schemaDesc : Schema → StructDesc Ty
  | .quad => ⟨"Quad", .quad, [("square", .scalar), ("output", .scalar)], by decide⟩
  | .modmul => ⟨"ModMul", .modmul,
      [("product", .scalar), ("quotient", .scalar), ("remainder", .scalar)], by decide⟩

/-- Optional sort-to-schema lookup belongs to this caller, not StructOp/Core. -/
def Ty.schema? : Ty → Option Schema
  | .quad => some .quad
  | .modmul => some .modmul
  | _ => none

def Ty.recordName (t : Ty) : Option String := t.schema?.map (fun k => (schemaDesc k).name)
def Ty.recordFields (t : Ty) : List (String × Ty) :=
  (t.schema?.map (fun k => (schemaDesc k).fields)).getD []

inductive ListOp : Signature Ty where
  | empty (element : Ty) : ListOp [] [] (.list element)
  | push (element : Ty) : ListOp [.list element, element] [] (.list element)

abbrev AggregateSig := SigSum (StructOp schemaDesc) ListOp

inductive Control : Signature Ty where
  | branch (captures : List Ty) (result : Ty) :
      Control (.bool :: captures) [⟨captures, result⟩, ⟨captures, result⟩] result
  | map (captures : List Ty) (input output : Ty) :
      Control (.list input :: captures) [⟨input :: captures, output⟩] (.list output)
  | fold (captures : List Ty) (element accumulator : Ty) :
      Control (.list element :: accumulator :: captures)
        [⟨element :: accumulator :: captures, accumulator⟩] accumulator

abbrev FieldSig := SigSum FieldOp (SigSum AggregateSig Control)
abbrev NatSig := SigSum NatOp (SigSum AggregateSig Control)
abbrev WordSig := SigSum WordOp (SigSum AggregateSig Control)

instance {F : Signature Ty} : Has (StructOp schemaDesc) (SigSum F (SigSum AggregateSig Control)) where
  inject := fun op => .inr (.inl (.inl op))
  injective := fun h => Sum.inl.inj (Sum.inl.inj (Sum.inr.inj h))

instance {F : Signature Ty} : Has ListOp (SigSum F (SigSum AggregateSig Control)) where
  inject := fun op => .inr (.inl (.inr op))
  injective := fun h => Sum.inr.inj (Sum.inl.inj (Sum.inr.inj h))

instance {F : Signature Ty} : Has Control (SigSum F (SigSum AggregateSig Control)) where
  inject := fun op => .inr (.inr op)
  injective := fun h => Sum.inr.inj (Sum.inr.inj h)

def fieldScalarModel : Model FieldOp (Val Field17) where
  eval := fun op args _ => match op, args with
    | .const n, .nil => Field17.ofNat n
    | .add, .cons a (.cons b .nil) => Field17.add a b
    | .mul, .cons a (.cons b .nil) => Field17.mul a b
    | .eq, .cons a (.cons b .nil) => decide (a = b)

def natScalarModel : Model NatOp (Val Nat) where
  eval := fun op args _ => match op, args with
    | .const n, .nil => n
    | .add, .cons a (.cons b .nil) => a + b
    | .mul, .cons a (.cons b .nil) => a * b
    | .div, .cons a (.cons b .nil) => a / b
    | .mod, .cons a (.cons b .nil) => a % b
    | .eq, .cons a (.cons b .nil) => decide (a = b)

def wordScalarModel : Model WordOp (Val UInt64) where
  eval := fun op args _ => match op, args with
    | .const n, .nil => UInt64.ofNat n
    | .add, .cons a (.cons b .nil) => a + b
    | .mul, .cons a (.cons b .nil) => a * b
    | .div, .cons a (.cons b .nil) => a / b
    | .mod, .cons a (.cons b .nil) => a % b
    | .eq, .cons a (.cons b .nil) => decide (a = b)

def schemaRepr (α : Type) : (k : Schema) → StructRepr (Val α) (schemaDesc k)
  | .quad => {
      pack := fun | .cons a (.cons b .nil) => ⟨a, b⟩
      unpack := fun w => .cons w.square (.cons w.output .nil)
      unpack_pack := by intro xs; cases xs with | cons a xs => cases xs with | cons b xs => cases xs; rfl
      pack_unpack := by intro x; cases x; rfl }
  | .modmul => {
      pack := fun | .cons a (.cons b (.cons c .nil)) => ⟨a, b, c⟩
      unpack := fun w => .cons w.product (.cons w.quotient (.cons w.remainder .nil))
      unpack_pack := by intro xs; cases xs with | cons a xs => cases xs with | cons b xs => cases xs with | cons c xs => cases xs; rfl
      pack_unpack := by intro x; cases x; rfl }

def listModel (α : Type) : Model ListOp (Val α) where
  eval := fun op args _ => match op, args with
    | .empty _, .nil => []
    | .push _, .cons xs (.cons x .nil) => xs ++ [x]

def aggregateModel (α : Type) : Model AggregateSig (Val α) :=
  (structModel (schemaRepr α)).sum (listModel α)

def controlModel (α : Type) : Model Control (Val α) where
  eval := fun op args bodies => match op, args, bodies with
    | .branch _ _, .cons b captures, .cons yes (.cons no .nil) =>
        if b then yes captures else no captures
    | .map _ _ _, .cons xs captures, .cons body .nil =>
        List.map (fun x => body (.cons x captures)) xs
    | .fold _ _ _, .cons xs (.cons initial captures), .cons body .nil =>
        xs.foldl (fun acc x => body (.cons x (.cons acc captures))) initial

def fieldModel : Model FieldSig (Val Field17) :=
  fieldScalarModel.sum ((aggregateModel Field17).sum (controlModel Field17))
def natModel : Model NatSig (Val Nat) :=
  natScalarModel.sum ((aggregateModel Nat).sum (controlModel Nat))
def wordModel : Model WordSig (Val UInt64) :=
  wordScalarModel.sum ((aggregateModel UInt64).sum (controlModel UInt64))

/-- Smart author-facing arithmetic calls hide injection and empty region lists. -/
def fieldConst {F : Signature Ty} [Has FieldOp F] (n : Nat) : Step F Γ .scalar :=
  call (FieldOp.const n) h![] .nil
def fieldMul {F : Signature Ty} [Has FieldOp F] (x y : Var Γ .scalar) : Step F Γ .scalar :=
  call FieldOp.mul h![x, y] .nil
def fieldAdd {F : Signature Ty} [Has FieldOp F] (x y : Var Γ .scalar) : Step F Γ .scalar :=
  call FieldOp.add h![x, y] .nil
def natMul {F : Signature Ty} [Has NatOp F] (x y : Var Γ .scalar) : Step F Γ .scalar :=
  call NatOp.mul h![x, y] .nil
def natDiv {F : Signature Ty} [Has NatOp F] (x y : Var Γ .scalar) : Step F Γ .scalar :=
  call NatOp.div h![x, y] .nil
def natMod {F : Signature Ty} [Has NatOp F] (x y : Var Γ .scalar) : Step F Γ .scalar :=
  call NatOp.mod h![x, y] .nil

/-- Named authoring, feature-polymorphic and returning the entire structure. -/
def quadratic {F : Signature Ty} [Has FieldOp F] [Has (StructOp schemaDesc) F] :
    Program F [.scalar, .scalar] .quad :=
  witgen [x, c] do
    let square ← fieldMul x x
    let output ← fieldAdd square c
    let result ← makeNamedStruct schemaDesc .quad fields![square := square, output := output]
    return result

def quadraticField : Program FieldSig [.scalar, .scalar] .quad := quadratic

theorem quadraticField_eval (x c : Field17) :
    quadraticField.eval fieldModel (.cons x (.cons c .nil)) =
      (⟨Field17.mul x x, Field17.add (Field17.mul x x) c⟩ : Quad Field17) := rfl

/-- Static traversal metadata. Sorts/argument indices/region shapes come from
Program.let_ itself. This is not a JSON codec or a native-backend certificate. -/
structure OpInfo where
  tag : String
  literal : Option Nat := none
  field : Option Nat := none
  deriving Repr, DecidableEq

def FieldOp.info : FieldOp args shapes t → OpInfo
  | .const n => ⟨"field.const", some n, none⟩
  | .add => ⟨"field.add", none, none⟩
  | .mul => ⟨"field.mul", none, none⟩
  | .eq => ⟨"field.eq", none, none⟩

def NatOp.info : NatOp args shapes t → OpInfo
  | .const n => ⟨"nat.const", some n, none⟩
  | .add => ⟨"nat.add", none, none⟩
  | .mul => ⟨"nat.mul", none, none⟩
  | .div => ⟨"nat.div", none, none⟩
  | .mod => ⟨"nat.mod", none, none⟩
  | .eq => ⟨"nat.eq", none, none⟩

def WordOp.info : WordOp args shapes t → OpInfo
  | .const n => ⟨"word.const", some n, none⟩
  | .add => ⟨"word.add", none, none⟩
  | .mul => ⟨"word.mul", none, none⟩
  | .div => ⟨"word.div", none, none⟩
  | .mod => ⟨"word.mod", none, none⟩
  | .eq => ⟨"word.eq", none, none⟩

def structInfo {S Schema : Type} {desc : Schema → StructDesc S}
    {args : List S} {shapes : List (RegionShape S)} {t : S} :
    StructOp desc args shapes t → OpInfo
  | .make _ => ⟨"record.make", none, none⟩
  | .get _ field => ⟨"record.get", none, some field.ref.index⟩

def ListOp.info : ListOp args shapes t → OpInfo
  | .empty _ => ⟨"list.empty", none, none⟩
  | .push _ => ⟨"list.push", none, none⟩

def aggregateInfo : AggregateSig args shapes t → OpInfo
  | .inl op => structInfo op
  | .inr op => op.info

def Control.info : Control args shapes t → OpInfo
  | .branch _ _ => ⟨"control.branch", none, none⟩
  | .map _ _ _ => ⟨"control.map", none, none⟩
  | .fold _ _ _ => ⟨"control.fold", none, none⟩

def fieldInfo : FieldSig args shapes t → OpInfo
  | .inl op => op.info
  | .inr (.inl op) => aggregateInfo op
  | .inr (.inr op) => op.info

def natInfo : NatSig args shapes t → OpInfo
  | .inl op => op.info
  | .inr (.inl op) => aggregateInfo op
  | .inr (.inr op) => op.info

def wordInfo : WordSig args shapes t → OpInfo
  | .inl op => op.info
  | .inr (.inl op) => aggregateInfo op
  | .inr (.inr op) => op.info

/-- RSA-inspired bounded regression slice, not signature verification. -/
def modMul {F : Signature Ty} [Has NatOp F] [Has (StructOp schemaDesc) F] :
    Program F [.scalar, .scalar, .scalar] .modmul :=
  witgen [a, b, n] do
    let product ← natMul a b
    let quotient ← natDiv product n
    let remainder ← natMod product n
    let result ← makeNamedStruct schemaDesc .modmul
      fields![product := product, quotient := quotient, remainder := remainder]
    return result

def modMulNat : Program NatSig [.scalar, .scalar, .scalar] .modmul := modMul

def ModMul.toArithmetic (w : ModMul Nat) : MulModWitness :=
  ⟨w.product, w.quotient, w.remainder⟩

theorem modMulNat_eval (a b n : Nat) :
    modMulNat.eval natModel (.cons a (.cons b (.cons n .nil))) =
      (⟨a * b, a * b / n, a * b % n⟩ : ModMul Nat) := rfl

theorem modMulNat_satisfies (a b n : Nat) (hn : 0 < n) :
    MulModRel a b n
      (modMulNat.eval natModel (.cons a (.cons b (.cons n .nil)))).toArithmetic :=
  genMulMod_correct a b n hn

/-- Captured c is an explicit map argument and an explicit closed body input. -/
def batchQuadratic {F : Signature Ty} [Has FieldOp F] [Has (StructOp schemaDesc) F] [Has Control F] :
    Program F [.list .scalar, .scalar] (.list .quad) :=
  witgen [xs, c] do
    let result ← call (Control.map [.scalar] .scalar .quad) h![xs, c] regions![quadratic]
    return result

def batchQuadraticField : Program FieldSig [.list .scalar, .scalar] (.list .quad) :=
  batchQuadratic

/-- Both arms are finite closed syntax; false returns an actual empty list. -/
def conditionalBatch {F : Signature Ty} [Has FieldOp F] [Has (StructOp schemaDesc) F]
    [Has ListOp F] [Has Control F] :
    Program F [.bool, .list .scalar, .scalar] (.list .quad) :=
  witgen [b, xs, c] do
    let result ← call (Control.branch [.list .scalar, .scalar] (.list .quad)) h![b, xs, c]
      regions![batchQuadratic, (witgen [_xs, _c] do
        let empty ← call (ListOp.empty .quad) h![] .nil
        return empty)]
    return result

def conditionalBatchField : Program FieldSig [.bool, .list .scalar, .scalar] (.list .quad) :=
  conditionalBatch

theorem batchQuadraticField_eval (xs : List Field17) (c : Field17) :
    batchQuadraticField.eval fieldModel (.cons xs (.cons c .nil)) =
      xs.map (fun x => (⟨Field17.mul x x, Field17.add (Field17.mul x x) c⟩ : Quad Field17)) := rfl

theorem conditionalBatch_eval (b : Bool) (xs : List Field17) (c : Field17) :
    conditionalBatchField.eval fieldModel (.cons b (.cons xs (.cons c .nil))) =
      if b then xs.map (fun x => (⟨Field17.mul x x, Field17.add (Field17.mul x x) c⟩ : Quad Field17))
      else [] := by cases b <;> rfl

/- Preorder native metadata traversal. Includes every closed region, even the
unselected branch. The typed parent serializer additionally retains refs/sorts. -/
mutual
  def nativeOps {F : Signature Ty}
      (info : ∀ {args shapes t}, F args shapes t → OpInfo) : Program F Γ t → List OpInfo
    | .ret _ => []
    | .let_ op _ regions next => info op :: (nativeRegionOps info regions ++ nativeOps info next)
  def nativeRegionOps {F : Signature Ty}
      (info : ∀ {args shapes t}, F args shapes t → OpInfo) : Regions F shapes → List OpInfo
    | .nil => []
    | .cons body rest => nativeOps info body ++ nativeRegionOps info rest
end

end Witgen.Demo
