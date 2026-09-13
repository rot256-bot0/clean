import Witgen.Typed.Export

/-! A small concrete named-method lowering. This Nat backend is a reference
implementation; the independent U64 backend uses the same registry API. -/
namespace Witgen.Typed.NatMethods
open Witgen Methods

inductive Op : Signature Ty where
  | const (f : FieldId) (n : Nat) : Op [] [] (.field f)
  | unpack (f : FieldId) : Op [.field f] [] .nat
  | pack (f : FieldId) : Op [.nat] [] (.field f)
  | add : Op [.nat, .nat] [] .nat
  | mul : Op [.nat, .nat] [] .nat
  | mod (p : Nat) : Op [.nat] [] .nat
  | neg (f : FieldId) : Op [.field f] [] (.field f)
  | inv (f : FieldId) : Op [.field f] [] (.field f)
  | sqrt (f : FieldId) : Op [.field f] [] (.option (.field f))
  | sub (f : FieldId) : Op [.field f,.field f] [] (.field f)

abbrev Val : Ty → Type
  | .field _ | .nat => Nat
  | .bool => Bool
  | .u64 => UInt64
  | .word4 => UInt64 × UInt64 × UInt64 × UInt64
  | .point _ => PUnit
  | .pair a b => Val a × Val b
  | .option a => Option (Val a)
  | .list a => List (Val a)

def model : Model Op Val where
  eval := fun op args _ => match op, args with
    | .const f n, .nil => n % modulus f
    | .unpack _, .cons a .nil => a
    | .pack _, .cons a .nil => a
    | .add, .cons a (.cons b .nil) => a + b
    | .mul, .cons a (.cons b .nil) => a * b
    | .mod p, .cons a .nil => a % p
    | .neg f, .cons a .nil => (modulus f - a % modulus f) % modulus f
    | .inv f, .cons a .nil => inverseNat (modulus f) a
    | .sqrt f, .cons a .nil => sqrtNat f a
    | .sub f, .cons a (.cons b .nil) =>
        (a % modulus f + modulus f - b % modulus f) % modulus f

def addSig (f : FieldId) : MethodSig Ty :=
  ⟨"field." ++ toString f.val ++ ".add.nat", [.field f, .field f], .field f⟩
def mulSig (f : FieldId) : MethodSig Ty :=
  ⟨"field." ++ toString f.val ++ ".mul.nat", [.field f, .field f], .field f⟩
def squareSig (f : FieldId) : MethodSig Ty :=
  ⟨"field." ++ toString f.val ++ ".square.nat", [.field f], .field f⟩

private def unpack {F : Signature Ty} {Γ : List Ty} {f : FieldId} [Has Op F]
    (a : Var Γ (.field f)) : Step F Γ .nat := call (Op.unpack f) h![a] .nil
private def pack {F : Signature Ty} {Γ : List Ty} [Has Op F]
    (f : FieldId) (a : Var Γ .nat) : Step F Γ (.field f) := call (Op.pack f) h![a] .nil
private def add {F : Signature Ty} {Γ : List Ty} [Has Op F]
    (a b : Var Γ .nat) : Step F Γ .nat := call Op.add h![a,b] .nil
private def mul {F : Signature Ty} {Γ : List Ty} [Has Op F]
    (a b : Var Γ .nat) : Step F Γ .nat := call Op.mul h![a,b] .nil
private def mod {F : Signature Ty} {Γ : List Ty} [Has Op F]
    (p : Nat) (a : Var Γ .nat) : Step F Γ .nat := call (Op.mod p) h![a] .nil

def addBody (f : FieldId) : Program (WithCalls Op []) (addSig f).args (addSig f).result :=
  witgen [a,b] do
    let x ← unpack a
    let y ← unpack b
    let z ← add x y
    let r ← mod (modulus f) z
    let out ← pack f r
    return out

def mulBody (f : FieldId) : Program (WithCalls Op [addSig f]) (mulSig f).args (mulSig f).result :=
  witgen [a,b] do
    let x ← unpack a
    let y ← unpack b
    let z ← mul x y
    let r ← mod (modulus f) z
    let out ← pack f r
    return out

def squareBody (f : FieldId) : Program (WithCalls Op [mulSig f, addSig f])
    (squareSig f).args (squareSig f).result :=
  .let_ (.inr (.call .zero)) h![.zero, .zero] .nil (.ret .zero)

def library (f : FieldId) : Library Op [squareSig f, mulSig f, addSig f] :=
  .cons (.cons (.cons .nil (addSig f) (by simp) (addBody f)) (mulSig f)
    (by simp [mulSig, addSig]) (mulBody f)) (squareSig f)
    (by simp [squareSig, mulSig, addSig]) (squareBody f)

def handler (f : FieldId) : Handler (FieldOp f) (WithCalls Op [squareSig f, mulSig f, addSig f])
  | _, _, _, .const n => .inl (.const f n)
  | _, _, _, .add => .inr (.call (.succ (.succ .zero)))
  | _, _, _, .mul => .inr (.call (.succ .zero))
  | _, _, _, .square => .inr (.call .zero)
  | _, _, _, .neg => .inl (.neg f)
  | _, _, _, .inv => .inl (.inv f)
  | _, _, _, .sqrt => .inl (.sqrt f)
  | _, _, _, .sub => .inl (.sub f)

def Rel : ∀ t, FieldVal t → Val t → Prop
  | .field _, a, b => a.val = b
  | .nat, a, b => a = b
  | .bool, a, b => a = b
  | .u64, a, b => a = b
  | .word4, a, b => a = b
  | .point _, a, b => a = b
  | .pair a b, x, y => Rel a x.1 y.1 ∧ Rel b x.2 y.2
  | .option a, x, y => Option.Rel (Rel a) x y
  | .list a, x, y => ListRel (Rel a) x y

theorem handler_respects (f : FieldId) :
    (fieldModel f).Respects ((library f).model model) (handler f) Rel := by
  intro args shapes s op xs ys fs gs hr _
  cases op with
  | const n => cases xs; cases ys; rfl
  | add =>
    cases xs; rename_i a xs; cases xs; rename_i b xs; cases xs
    cases ys; rename_i x ys; cases ys; rename_i y ys; cases ys
    obtain ⟨ha, hb, _⟩ := hr
    change (a.val + b.val) % modulus f = (x + y) % modulus f
    change a.val = x at ha
    change b.val = y at hb
    rw [ha, hb]
  | mul =>
    cases xs; rename_i a xs; cases xs; rename_i b xs; cases xs
    cases ys; rename_i x ys; cases ys; rename_i y ys; cases ys
    obtain ⟨ha, hb, _⟩ := hr
    change (a.val * b.val) % modulus f = (x * y) % modulus f
    change a.val = x at ha
    change b.val = y at hb
    rw [ha, hb]
  | square =>
    cases xs; rename_i a xs; cases xs
    cases ys; rename_i x ys; cases ys
    obtain ⟨ha, _⟩ := hr
    change a.val ^ 2 % modulus f = (x * x) % modulus f
    change a.val = x at ha
    simp [ha, Nat.pow_succ]
  | neg =>
    cases xs; rename_i a xs; cases xs
    cases ys; rename_i x ys; cases ys
    obtain ⟨ha, _⟩ := hr
    change (modulus f - a.val) % modulus f = (modulus f - x % modulus f) % modulus f
    change a.val = x at ha
    rw [← ha, Nat.mod_eq_of_lt a.isLt]
  | inv =>
    cases xs; rename_i a xs; cases xs
    cases ys; rename_i x ys; cases ys
    obtain ⟨ha, _⟩ := hr
    change inverseNat (modulus f) a.val = inverseNat (modulus f) x
    exact congrArg (inverseNat (modulus f)) ha
  | sqrt =>
    cases xs; rename_i a xs; cases xs
    cases ys; rename_i x ys; cases ys
    obtain ⟨ha, _⟩ := hr
    change a.val = x at ha
    change Option.Rel (fun a b => a.val = b) (Residue.sqrt a) (sqrtNat f x)
    rw [← ha]
    exact Residue.sqrt_nat_rel a
  | sub =>
    cases xs; rename_i a xs; cases xs
    rename_i b xs; cases xs
    cases ys; rename_i x ys; cases ys
    rename_i y ys; cases ys
    obtain ⟨ha, hb, _⟩ := hr
    change a.val = x at ha
    change b.val = y at hb
    change (Residue.sub a b).val = (x % modulus f + modulus f - y % modulus f) % modulus f
    rw [Residue.sub_val, ← ha, ← hb, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt]

def lowering (f : FieldId) : CertifiedLowering (fieldModel f) ((library f).model model) Rel :=
  .ofHandler _ _ (handler f) Rel (handler_respects f)

open Lean in
def codec : OpCodec Op := fun op =>
  let (tag, data) : String × List (String × Json) := match op with
    | .const f n => ("nat.field.const", [("field", toJson f.val), ("value", .str (toString n)),
        ("modulus", .str (toString (modulus f)))])
    | .unpack f => ("nat.field.unpack", [("field", toJson f.val)])
    | .pack f => ("nat.field.pack", [("field", toJson f.val)])
    | .add => ("nat.add", [])
    | .mul => ("nat.mul", [])
    | .mod p => ("nat.mod", [("modulus", .str (toString p))])
    | .neg f => ("nat.field.neg", [("field", toJson f.val), ("modulus", .str (toString (modulus f)))])
    | .inv f => ("nat.field.inv", [("field", toJson f.val), ("modulus", .str (toString (modulus f)))])
    | .sqrt f => ("nat.field.sqrt", [("field", toJson f.val), ("modulus", .str (toString (modulus f)))])
    | .sub f => ("nat.field.sub", [("field", toJson f.val), ("modulus", .str (toString (modulus f)))])
  Json.mkObj [("op", .str tag), ("static", Json.mkObj data)]

end Witgen.Typed.NatMethods
