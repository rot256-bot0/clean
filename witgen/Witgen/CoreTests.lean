import Witgen.Core

namespace Witgen.CoreTests

inductive S where
  | number
  deriving DecidableEq, Repr

abbrev V : S → Type := fun _ => Nat

inductive Scalar : Signature S where
  | lit (n : Nat) : Scalar [] [] .number
  | add : Scalar [.number, .number] [] .number

def scalarModel : Model Scalar V where
  eval := fun op args _ => match op, args with
    | .lit n, .nil => n
    | .add, .cons a (.cons b .nil) => a + b

def addition : Program Scalar [] .number :=
  .let_ (.lit 20) .nil .nil <|
  .let_ (.lit 22) .nil .nil <|
  .let_ .add (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
  .ret .zero

example : addition.eval scalarModel .nil = 42 := rfl
#eval addition.eval scalarModel .nil

-- Slice 2: an independent feature joins without changing Program or Model.
inductive Marker : Signature S where
  | identity : Marker [.number] [] .number

abbrev Extended := SigSum Scalar Marker

def markerModel : Model Marker V where
  eval := fun op args _ => match op, args with
    | .identity, .cons x .nil => x

def extendedModel : Model Extended V := Model.sum scalarModel markerModel

def embedded : Program Extended [] .number := addition.mapHandler Has.inject
example : embedded.eval extendedModel .nil = 42 := rfl
example : (addition.mapHandler (Handler.id Scalar)).eval scalarModel .nil = 42 := rfl

-- Reference substitution can reorder/duplicate inputs, while fixing let binders.
def swap : RefSubst [S.number, S.number] [S.number, S.number] := fun r =>
  match r with
  | .zero => .succ .zero
  | .succ .zero => .zero

def second : Program Scalar [S.number, S.number] .number := .ret (.succ .zero)
example : (second.subst swap).eval scalarModel (.cons 7 (.cons 9 .nil)) = 7 := rfl
#check Program.eval_subst
#check Program.eval_mapHandler_related
#check CertifiedLowering.comp
#print axioms Program.eval_subst
#print axioms Program.eval_mapHandler_related
#print axioms CertifiedLowering.comp_correct

-- Slice 3: operation-to-subprogram substitution, not merely relabeling.
inductive ModMul : Signature S where
  | mul (modulus : Nat) : ModMul [.number, .number] [] .number

inductive NatOps : Signature S where
  | lit (n : Nat) : NatOps [] [] .number
  | mul : NatOps [.number, .number] [] .number
  | mod : NatOps [.number, .number] [] .number

def modularModel : Model ModMul V where
  eval := fun op args _ => match op, args with
    | .mul m, .cons a (.cons b .nil) => a * b % m

def natModel : Model NatOps V where
  eval := fun op args _ => match op, args with
    | .lit n, .nil => n
    | .mul, .cons a (.cons b .nil) => a * b
    | .mod, .cons a (.cons b .nil) => a % b

def mulTemplate : Template ModMul NatOps := fun op _ => match op with
  | .mul m =>
    .let_ .mul (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
    .let_ (.lit m) .nil .nil <|
    .let_ .mod (.cons (.succ .zero) (.cons .zero .nil)) .nil <|
    .ret .zero

def twiceModular : Program ModMul [S.number, S.number] .number :=
  .let_ (.mul 13) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
  .let_ (.mul 11) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
  .ret .zero

example : (twiceModular.lower mulTemplate).eval natModel (.cons 7 (.cons 5 .nil)) =
    (7 * 5 % 13) * 7 % 11 := rfl
#eval (twiceModular.lower mulTemplate).eval natModel (.cons 7 (.cons 5 .nil))
#check Program.eval_bind
#check Program.eval_lower_related
#check CertifiedLowering.ofTemplate
#print axioms Program.eval_bind
#print axioms Program.eval_lower_related

-- Use the generic proof, rather than only testing evaluation on constants.
def EqR (_ : S) (a b : Nat) : Prop := a = b

theorem env_eq {D : T → Type} {xs ys : HList D ts}
    (h : HList.Rel (fun _ a b => a = b) xs ys) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys =>
      have hxy := h.1
      have hxys := ih h.2
      subst y; subst ys; rfl

theorem mulTemplate_law : Template.Respects modularModel natModel mulTemplate EqR := by
  intro args shapes s op xs ys fs regions h _
  have heq := env_eq h
  subst ys
  cases op with
  | mul m =>
    cases xs with
    | cons a xs =>
      cases xs with
      | cons b xs => cases xs; rfl

def modToNat : CertifiedLowering modularModel natModel EqR :=
  .ofTemplate modularModel natModel mulTemplate EqR mulTemplate_law

theorem lowered_correct (a b : Nat) :
    (twiceModular.lower mulTemplate).eval natModel (.cons a (.cons b .nil)) =
      (a * b % 13) * a % 11 := by
  exact (modToNat.correct twiceModular (.cons a (.cons b .nil))
    (.cons a (.cons b .nil)) ⟨rfl, rfl, trivial⟩).symm

theorem natIdentity_law : natModel.Respects natModel (Handler.id NatOps) EqR := by
  intro args shapes s op xs ys fs gs h _
  have heq := env_eq h
  subst ys
  cases op <;> cases fs <;> cases gs <;> rfl

def natIdentity : CertifiedLowering natModel natModel EqR :=
  .ofHandler natModel natModel (Handler.id NatOps) EqR natIdentity_law

theorem composed_lowering_correct (a b : Nat) :
    RelComp EqR EqR S.number ((a * b % 13) * a % 11)
      (((modToNat.comp natIdentity).run twiceModular).eval natModel (.cons a (.cons b .nil))) := by
  exact CertifiedLowering.comp_correct modToNat natIdentity twiceModular
    (.cons a (.cons b .nil)) (.cons a (.cons b .nil))
    ⟨⟨a, rfl, rfl⟩, ⟨b, rfl, rfl⟩, trivial⟩

#print axioms lowered_correct
#print axioms composed_lowering_correct

-- Slice 4: optional control + first-class aggregates, absent from Core.
namespace Optional

inductive Ty where
  | number | flag | numbers | record
  deriving DecidableEq, Repr

structure MapRecord where
  values : List Nat
  visits : List Nat
  deriving DecidableEq, Repr

abbrev Val : Ty → Type
  | .number => Nat
  | .flag => Bool
  | .numbers => List Nat
  | .record => MapRecord

inductive DataOp : Signature Ty where
  | numbers (xs : List Nat) : DataOp [] [] .numbers
  | empty : DataOp [] [] .record
  | double : DataOp [.number] [] .number
  | push : DataOp [.record, .number, .number] [] .record

inductive Control : Signature Ty where
  | branch (t : Ty) : Control [.flag] [⟨[], t⟩, ⟨[], t⟩] t
  | fold : Control [.numbers, .record] [⟨[.number, .record], .record⟩] .record

abbrev Library := SigSum DataOp Control

def push (r : MapRecord) (x y : Nat) : MapRecord :=
  ⟨r.values ++ [y], r.visits ++ [x]⟩

def dataModel : Model DataOp Val where
  eval := fun op args _ => match op, args with
    | .numbers xs, .nil => xs
    | .empty, .nil => ⟨[], []⟩
    | .double, .cons x .nil => x * 2
    | .push, .cons r (.cons x (.cons y .nil)) => push r x y

def controlModel : Model Control Val where
  eval := fun op args bodies => match op, args, bodies with
    | .branch _, .cons b .nil, .cons yes (.cons no .nil) =>
      if b then yes .nil else no .nil
    | .fold, .cons xs (.cons init .nil), .cons step .nil =>
      xs.foldl (fun acc x => step (.cons x (.cons acc .nil))) init

def model : Model Library Val := Model.sum dataModel controlModel

/-- Map is derived via a left fold carrying a first-class result record.
Both transformed values and an ordered input visitation trace are returned. -/
def mapBody : Program Library [.number, .record] .record :=
  .let_ (.inl .double) (.cons .zero .nil) .nil <|
  .let_ (.inl .push)
    (.cons (.succ (.succ .zero)) (.cons (.succ .zero) (.cons .zero .nil))) .nil <|
  .ret .zero

def mapped : Program Library [.numbers] .record :=
  .let_ (.inl .empty) .nil .nil <|
  .let_ (.inr .fold) (.cons (.succ .zero) (.cons .zero .nil))
    (.cons mapBody .nil) <|
  .ret .zero

def constantMap (xs : List Nat) : Program Library [] .record :=
  .let_ (.inl (.numbers xs)) .nil .nil mapped

def branch (yes no : Program Library [] .record) : Program Library [.flag] .record :=
  .let_ (.inr (.branch .record)) (.cons .zero .nil)
    (.cons yes (.cons no .nil)) (.ret .zero)

def runMap (xs : List Nat) : MapRecord := mapped.eval model (.cons xs .nil)

def runBranch (b : Bool) : MapRecord :=
  (branch (constantMap [3, 1, 4]) (constantMap [9, 8])).eval model (.cons b .nil)

/-- Neither equation mentions the unselected body's interpretation. -/
theorem branch_true (yes no : Program Library [] .record) :
    (branch yes no).eval model (.cons true .nil) = yes.eval model .nil := rfl

theorem branch_false (yes no : Program Library [] .record) :
    (branch yes no).eval model (.cons false .nil) = no.eval model .nil := rfl

theorem fold_acc (xs : List Nat) (acc : MapRecord) :
    xs.foldl (fun r x => push r x (x * 2)) acc =
      ⟨acc.values ++ xs.map (fun x => x * 2), acc.visits ++ xs⟩ := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [push, List.map_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem map_correct (xs : List Nat) :
    runMap xs = ⟨xs.map (fun x => x * 2), xs⟩ := by
  change xs.foldl (fun r x => push r x (x * 2)) ⟨[], []⟩ = _
  simpa using fold_acc xs ⟨[], []⟩

end Optional

example : (Optional.runBranch true).values = [6, 2, 8] := rfl
example : (Optional.runBranch true).visits = [3, 1, 4] := rfl
example : (Optional.runBranch false).values = [18, 16] := rfl
example : (Optional.runBranch false).visits = [9, 8] := rfl
example : (Optional.runMap []).values = [] := rfl
#eval Optional.runBranch true
#eval Optional.runBranch false
#print axioms Optional.branch_true
#print axioms Optional.branch_false
#print axioms Optional.map_correct

-- Regression controls for structure, scoping, and a genuinely wrong template.
example : ¬ Nonempty (Var [] S.number) := by
  intro ⟨r⟩
  cases r

def unreducedTemplate : Template ModMul NatOps := fun op _ => match op with
  | .mul _ => .let_ .mul (.cons .zero (.cons (.succ .zero) .nil)) .nil (.ret .zero)

theorem unreducedTemplate_rejected :
    ¬ Template.Respects modularModel natModel unreducedTemplate EqR := by
  intro h
  have wrong : (9 : Nat) = 35 := h (.mul 13)
    (.cons 7 (.cons 5 .nil)) (.cons 7 (.cons 5 .nil)) .nil .nil
    ⟨rfl, rfl, trivial⟩ trivial
  exact (by decide : (9 : Nat) ≠ 35) wrong

namespace Optional

/-- Test-local identity arguments for arbitrary operation shapes. -/
def refs (ts : List T) : HList (Var ts) ts := match ts with
  | [] => .nil
  | _ :: ts => .cons .zero ((refs ts).map (fun r => .succ r))

def keep : Template Library Library := fun op regions =>
  .let_ op (refs _) regions (.ret .zero)

-- This evaluates lower through branch -> fold -> scalar body nesting.
example : ((branch (constantMap [3, 1, 4]) (constantMap [9, 8])).lower keep).eval
    model (.cons true .nil) = ⟨[6, 2, 8], [3, 1, 4]⟩ := rfl
example : ((branch (constantMap [3, 1, 4]) (constantMap [9, 8])).lower keep).eval
    model (.cons false .nil) = ⟨[18, 16], [9, 8]⟩ := rfl

-- Relabeling traverses the same higher-order syntax, without core changes.
example : ((branch (constantMap [3, 1, 4]) (constantMap [9, 8])).mapHandler
    (Handler.id Library)).eval model (.cons true .nil) = ⟨[6, 2, 8], [3, 1, 4]⟩ := rfl

end Optional

#print axioms unreducedTemplate_rejected

end Witgen.CoreTests
