import Witgen.Authoring
import Witgen.Export

/-! A user-owned circuit type and feature, unrelated to Demo.Ty. The source
carries a native SplitWitness; the target carries a generic ordered field vector.
The certified lowering expands a custom operation into arithmetic and StructOp. -/
namespace Witgen.Custom

inductive Ty where
  | nat | split
  deriving DecidableEq, Repr

structure SplitWitness where
  low : Nat
  high : Nat
  deriving DecidableEq, Repr

inductive Schema where | split

@[reducible] def desc : Schema → StructDesc Ty
  | .split => ⟨"SplitWitness", .split, [("low", .nat), ("high", .nat)], by decide⟩

@[reducible] def Native : Ty → Type
  | .nat => Nat
  | .split => SplitWitness

/-- No native SplitWitness survives in the target semantic representation. -/
@[reducible] def Structural : Ty → Type
  | .nat => Nat
  | .split => HList (fun _ : Ty => Nat) (desc .split).sorts

def repr : (k : Schema) → StructRepr Structural (desc k)
  | .split => {
      pack := fun | h![lo, hi] => h![lo, hi]
      unpack := fun | h![lo, hi] => h![lo, hi]
      unpack_pack := by intro xs; cases xs with | cons lo xs => cases xs with | cons hi xs => cases xs; rfl
      pack_unpack := by intro xs; cases xs with | cons lo xs => cases xs with | cons hi xs => cases xs; rfl }

inductive SplitOp : Signature Ty where
  | split (base : Nat) : SplitOp [.nat] [] .split
  | low : SplitOp [.split] [] .nat
  | high : SplitOp [.split] [] .nat

inductive NatOp : Signature Ty where
  | const (n : Nat) : NatOp [] [] .nat
  | div : NatOp [.nat, .nat] [] .nat
  | mod : NatOp [.nat, .nat] [] .nat

abbrev Target := SigSum NatOp (StructOp desc)

def nativeModel : Model SplitOp Native where
  eval := fun op xs _ => match op, xs with
    | .split base, h![x] => ⟨x % base, x / base⟩
    | .low, h![w] => w.low
    | .high, h![w] => w.high

def arithmeticModel : Model NatOp Structural where
  eval := fun op xs _ => match op, xs with
    | .const n, h![] => n
    | .div, h![a, b] => a / b
    | .mod, h![a, b] => a % b

def targetModel : Model Target Structural := arithmeticModel.sum (structModel repr)

def split {F : Signature Ty} [Has SplitOp F] (base : Nat) (x : Var Γ .nat) : Step F Γ .split :=
  call (.split base : SplitOp _ _ _) h![x] .nil

def low {F : Signature Ty} [Has SplitOp F] (w : Var Γ .split) : Step F Γ .nat :=
  call SplitOp.low h![w] .nil

def constant (n : Nat) : Step Target Γ .nat := call (NatOp.const n) h![] .nil
def quotient (a b : Var Γ .nat) : Step Target Γ .nat := call NatOp.div h![a, b] .nil
def remainder (a b : Var Γ .nat) : Step Target Γ .nat := call NatOp.mod h![a, b] .nil

/-- Author code mentions its own custom circuit feature, not structure fields. -/
def splitProgram (base : Nat) : Program SplitOp [.nat] .split :=
  witgen [x] do
    let witness ← split base x
    return witness

def lowProgram (base : Nat) : Program SplitOp [.nat] .nat :=
  witgen [x] do
    let witness ← split base x
    let result ← low witness
    return result

/-- The lowering author uses generic named structures; no new target record tags. -/
def lowerSplit : Template SplitOp Target
  | _, _, _, .split base, _ =>
    witgen [x] do
      let base ← constant base
      let lo ← remainder x base
      let hi ← quotient x base
      let witness ← makeNamedStruct desc .split fields![low := lo, high := hi]
      return witness
  | _, _, _, .low, _ =>
    witgen [w] do
      let result ← getField desc .split "low" w
      return result
  | _, _, _, .high, _ =>
    witgen [w] do
      let result ← getField desc .split "high" w
      return result

def Related : (t : Ty) → Native t → Structural t → Prop
  | .nat, x, y => x = y
  | .split, w, fields => h![w.low, w.high] = fields

/-- Per-feature proof discharges the unchanged generic core's template contract. -/
theorem lowerSplit_law : Template.Respects nativeModel targetModel lowerSplit Related := by
  intro args shapes t op xs ys fs regions hr _
  cases op with
  | split base =>
    cases xs with
    | cons x xs =>
      cases xs
      cases ys with
      | cons y ys =>
        cases ys
        have h : x = y := hr.1
        subst y
        rfl
  | low =>
    cases xs with
    | cons w xs =>
      cases xs
      cases ys with
      | cons fields ys =>
        cases ys
        have h : h![w.low, w.high] = fields := hr.1
        subst fields
        rfl
  | high =>
    cases xs with
    | cons w xs =>
      cases xs
      cases ys with
      | cons fields ys =>
        cases ys
        have h : h![w.low, w.high] = fields := hr.1
        subst fields
        rfl

def certifiedLowering : CertifiedLowering nativeModel targetModel Related :=
  .ofTemplate _ _ lowerSplit Related lowerSplit_law

theorem lowerSplit_correct (p : Program SplitOp Γ t) (xs : HList Native Γ)
    (ys : HList Structural Γ) (hr : HList.Rel Related xs ys) :
    Related t (p.eval nativeModel xs) ((p.lower lowerSplit).eval targetModel ys) :=
  Program.eval_lower_related _ _ _ _ lowerSplit_law p xs ys hr

/-- A circuit-facing complete-witness relation: reconstruction and limb range. -/
def SplitRel (base n : Nat) (w : SplitWitness) : Prop :=
  n = w.low + base * w.high ∧ (0 < base → w.low < base)

theorem splitProgram_satisfies (base n : Nat) :
    SplitRel base n ((splitProgram base).eval nativeModel h![n]) := by
  exact ⟨(Nat.mod_add_div n base).symm, fun h => Nat.mod_lt n h⟩

/-- Target fields satisfy the source circuit contract via the representation relation. -/
theorem lowered_satisfies (base n : Nat) :
    ∃ w, SplitRel base n w ∧
      Related .split w (((splitProgram base).lower lowerSplit).eval targetModel h![n]) :=
  ⟨_, splitProgram_satisfies base n,
    lowerSplit_correct (splitProgram base) h![n] h![n] ⟨rfl, trivial⟩⟩

def typeJson : Ty → Lean.Json
  | .nat => .str "scalar"
  | .split => Export.structTypeJson (fun _ => .str "scalar") (desc .split)

def info : Export.Info Target
  | _, _, _, .inl (.const n) => ⟨"nat.const", some n, none⟩
  | _, _, _, .inl .div => ⟨"nat.div", none, none⟩
  | _, _, _, .inl .mod => ⟨"nat.mod", none, none⟩
  | _, _, _, .inr op => Demo.structInfo op

def exportSplit (base : Nat) : Except String Lean.Json :=
  Export.moduleJsonWith typeJson info "generate" "nat" ["x"] ((splitProgram base).lower lowerSplit)

def exportLow (base : Nat) : Except String Lean.Json :=
  Export.moduleJsonWith typeJson info "generate" "nat" ["x"] ((lowProgram base).lower lowerSplit)

end Witgen.Custom
