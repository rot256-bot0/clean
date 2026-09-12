import Witgen.Core
import Witgen.Arithmetic

/-! Optional typed demonstration vocabulary; none of these sorts or features
belong to the generic kernel. Payloads are finite data, never semantic closures. -/
namespace Witgen.Demo
open Arithmetic

inductive Ty where
  | scalar | bool | quad | modmul | list (element : Ty)
  deriving Repr, DecidableEq

/-- Native record identity and ordered named fields are library-owned metadata. -/
def Ty.recordName : Ty → Option String
  | .quad => some "Quad"
  | .modmul => some "ModMul"
  | _ => none

def Ty.recordFields : Ty → List (String × Ty)
  | .quad => [("square", .scalar), ("output", .scalar)]
  | .modmul => [("product", .scalar), ("quotient", .scalar), ("remainder", .scalar)]
  | _ => []

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

inductive DataOp : Signature Ty where
  | quad : DataOp [.scalar, .scalar] [] .quad
  | square : DataOp [.quad] [] .scalar
  | output : DataOp [.quad] [] .scalar
  | modmul : DataOp [.scalar, .scalar, .scalar] [] .modmul
  | product : DataOp [.modmul] [] .scalar
  | quotient : DataOp [.modmul] [] .scalar
  | remainder : DataOp [.modmul] [] .scalar
  | empty (element : Ty) : DataOp [] [] (.list element)
  | push (element : Ty) : DataOp [.list element, element] [] (.list element)

inductive Control : Signature Ty where
  | branch (captures : List Ty) (result : Ty) :
      Control (.bool :: captures) [⟨captures, result⟩, ⟨captures, result⟩] result
  | map (captures : List Ty) (input output : Ty) :
      Control (.list input :: captures) [⟨input :: captures, output⟩] (.list output)
  | fold (captures : List Ty) (element accumulator : Ty) :
      Control (.list element :: accumulator :: captures)
        [⟨element :: accumulator :: captures, accumulator⟩] accumulator

abbrev FieldSig := SigSum FieldOp (SigSum DataOp Control)
abbrev NatSig := SigSum NatOp (SigSum DataOp Control)
abbrev WordSig := SigSum WordOp (SigSum DataOp Control)

instance {F : Signature Ty} : Has DataOp (SigSum F (SigSum DataOp Control)) where
  inject := fun op => .inr (.inl op)
  injective := fun h => Sum.inl.inj (Sum.inr.inj h)

instance {F : Signature Ty} : Has Control (SigSum F (SigSum DataOp Control)) where
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

def dataModel (α : Type) : Model DataOp (Val α) where
  eval := fun op args _ => match op, args with
    | .quad, .cons a (.cons b .nil) => ⟨a, b⟩
    | .square, .cons w .nil => w.square
    | .output, .cons w .nil => w.output
    | .modmul, .cons p (.cons q (.cons r .nil)) => ⟨p, q, r⟩
    | .product, .cons w .nil => w.product
    | .quotient, .cons w .nil => w.quotient
    | .remainder, .cons w .nil => w.remainder
    | .empty _, .nil => []
    | .push _, .cons xs (.cons x .nil) => xs ++ [x]

def controlModel (α : Type) : Model Control (Val α) where
  eval := fun op args bodies => match op, args, bodies with
    | .branch _ _, .cons b captures, .cons yes (.cons no .nil) =>
        if b then yes captures else no captures
    | .map _ _ _, .cons xs captures, .cons body .nil =>
        List.map (fun x => body (.cons x captures)) xs
    | .fold _ _ _, .cons xs (.cons initial captures), .cons body .nil =>
        xs.foldl (fun acc x => body (.cons x (.cons acc captures))) initial

def fieldModel : Model FieldSig (Val Field17) :=
  fieldScalarModel.sum ((dataModel Field17).sum (controlModel Field17))
def natModel : Model NatSig (Val Nat) :=
  natScalarModel.sum ((dataModel Nat).sum (controlModel Nat))
def wordModel : Model WordSig (Val UInt64) :=
  wordScalarModel.sum ((dataModel UInt64).sum (controlModel UInt64))

/-- Feature-polymorphic program. Return the entire record, not a selected scalar. -/
def quadratic {F : Signature Ty} [Has FieldOp F] [Has DataOp F] :
    Program F [.scalar, .scalar] .quad :=
  .let_ (Has.inject FieldOp.mul) (.cons .zero (.cons .zero .nil)) .nil <|
  .let_ (Has.inject FieldOp.add) (.cons .zero (.cons (.succ (.succ .zero)) .nil)) .nil <|
  .let_ (Has.inject DataOp.quad) (.cons (.succ .zero) (.cons .zero .nil)) .nil <|
  .ret .zero

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

def DataOp.info : DataOp args shapes t → OpInfo
  | .quad | .modmul => ⟨"record.make", none, none⟩
  | .square | .product => ⟨"record.get", none, some 0⟩
  | .output | .quotient => ⟨"record.get", none, some 1⟩
  | .remainder => ⟨"record.get", none, some 2⟩
  | .empty _ => ⟨"list.empty", none, none⟩
  | .push _ => ⟨"list.push", none, none⟩

def Control.info : Control args shapes t → OpInfo
  | .branch _ _ => ⟨"control.branch", none, none⟩
  | .map _ _ _ => ⟨"control.map", none, none⟩
  | .fold _ _ _ => ⟨"control.fold", none, none⟩

def fieldInfo : FieldSig args shapes t → OpInfo
  | .inl op => op.info
  | .inr (.inl op) => op.info
  | .inr (.inr op) => op.info

def natInfo : NatSig args shapes t → OpInfo
  | .inl op => op.info
  | .inr (.inl op) => op.info
  | .inr (.inr op) => op.info

def wordInfo : WordSig args shapes t → OpInfo
  | .inl op => op.info
  | .inr (.inl op) => op.info
  | .inr (.inr op) => op.info

/-- RSA-inspired modular multiplication slice, not signature verification. -/
def modMul {F : Signature Ty} [Has NatOp F] [Has DataOp F] :
    Program F [.scalar, .scalar, .scalar] .modmul :=
  .let_ (Has.inject NatOp.mul) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
  .let_ (Has.inject NatOp.div)
    (.cons .zero (.cons (.succ (.succ (.succ .zero))) .nil)) .nil <|
  .let_ (Has.inject NatOp.mod)
    (.cons (.succ .zero) (.cons (.succ (.succ (.succ (.succ .zero)))) .nil)) .nil <|
  .let_ (Has.inject DataOp.modmul)
    (.cons (.succ (.succ .zero)) (.cons (.succ .zero) (.cons .zero .nil))) .nil <|
  .ret .zero

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

/-- Captured c is an explicit map argument and an explicit body input. -/
def batchQuadratic {F : Signature Ty} [Has FieldOp F] [Has DataOp F] [Has Control F] :
    Program F [.list .scalar, .scalar] (.list .quad) :=
  .let_ (Has.inject (Control.map [.scalar] .scalar .quad))
    (.cons .zero (.cons (.succ .zero) .nil)) (.cons quadratic .nil) (.ret .zero)

def batchQuadraticField : Program FieldSig [.list .scalar, .scalar] (.list .quad) :=
  batchQuadratic

/-- The false region returns an actual empty record list. Both regions are syntax. -/
def conditionalBatch {F : Signature Ty} [Has FieldOp F] [Has DataOp F] [Has Control F] :
    Program F [.bool, .list .scalar, .scalar] (.list .quad) :=
  .let_ (Has.inject (Control.branch [.list .scalar, .scalar] (.list .quad)))
    (.cons .zero (.cons (.succ .zero) (.cons (.succ (.succ .zero)) .nil)))
    (.cons batchQuadratic
      (.cons (.let_ (Has.inject (DataOp.empty .quad)) .nil .nil (.ret .zero)) .nil))
    (.ret .zero)

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
