import Witgen.Typed.Export

namespace Witgen.Typed

/-- Optional structural values, not mandatory computational core operations. -/
inductive ValueOp : Signature Ty where
  | pair (a b : Ty) : ValueOp [a,b] [] (.pair a b)
  | fst (a b : Ty) : ValueOp [.pair a b] [] a
  | snd (a b : Ty) : ValueOp [.pair a b] [] b
  | some (a : Ty) : ValueOp [a] [] (.option a)
  | none (a : Ty) : ValueOp [] [] (.option a)
  | bind (a b : Ty) : ValueOp [.option a] [⟨[a], .option b⟩] (.option b)
  | nil (a : Ty) : ValueOp [] [] (.list a)
  | cons (a : Ty) : ValueOp [a, .list a] [] (.list a)
  | case (a result : Ty) (captures : List Ty) : ValueOp ((.option a) :: captures)
      [⟨captures, result⟩, ⟨a :: captures, result⟩] result

def ValueOp.model (fields : FieldId → Type) (words : Type) (points : CurveId → Type) :
    Model ValueOp (Value fields words points) where
  eval := fun op args regions => match op, args, regions with
    | .pair _ _, .cons a (.cons b .nil), .nil => (a,b)
    | .fst _ _, .cons a .nil, .nil => a.1
    | .snd _ _, .cons a .nil, .nil => a.2
    | .some _, .cons a .nil, .nil => Option.some a
    | .none _, .nil, .nil => Option.none
    | .bind _ _, .cons a .nil, .cons body .nil => a.bind (fun x => body (.cons x .nil))
    | .nil _, .nil, .nil => []
    | .cons _, .cons x (.cons xs .nil), .nil => x :: xs
    | .case _ _ _, .cons x captures, .cons onNone (.cons onSome .nil) =>
      match x with
      | Option.none => onNone captures
      | Option.some a => onSome (.cons a captures)

theorem ValueOp.case_none (fields : FieldId → Type) (words : Type) (points : CurveId → Type)
    (a result : Ty) (captures : List Ty)
    (xs : HList (Value fields words points) captures)
    (onNone : Body (Value fields words points) ⟨captures, result⟩)
    (onSome : Body (Value fields words points) ⟨a :: captures, result⟩) :
    (ValueOp.model fields words points).eval (.case a result captures)
      (.cons Option.none xs) (.cons onNone (.cons onSome .nil)) = onNone xs := rfl

theorem ValueOp.case_some (fields : FieldId → Type) (words : Type) (points : CurveId → Type)
    (a result : Ty) (captures : List Ty)
    (x : Value fields words points a) (xs : HList (Value fields words points) captures)
    (onNone : Body (Value fields words points) ⟨captures, result⟩)
    (onSome : Body (Value fields words points) ⟨a :: captures, result⟩) :
    (ValueOp.model fields words points).eval (.case a result captures)
      (.cons (Option.some x) xs) (.cons onNone (.cons onSome .nil)) = onSome (.cons x xs) := rfl

open Lean Methods in
def ValueOp.codec : OpCodec ValueOp := fun op =>
  let tag := match op with
    | .pair .. => "value.pair"
    | .fst .. => "value.fst"
    | .snd .. => "value.snd"
    | .some .. => "option.some"
    | .none .. => "option.none"
    | .bind .. => "option.bind"
    | .nil .. => "value.nil"
    | .cons .. => "value.cons"
    | .case .. => "option.match"
  Json.mkObj [("op", .str tag), ("static", Json.mkObj [])]

end Witgen.Typed

namespace Witgen.value
open Typed
variable {F : Signature Ty} {Γ : List Ty} [Has ValueOp F] {a b : Ty}
def Pair (x : Var Γ a) (y : Var Γ b) : Step F Γ (.pair a b) := call (.pair a b : ValueOp _ _ _) h![x,y] .nil
def Fst (x : Var Γ (.pair a b)) : Step F Γ a := call (.fst a b : ValueOp _ _ _) h![x] .nil
def Snd (x : Var Γ (.pair a b)) : Step F Γ b := call (.snd a b : ValueOp _ _ _) h![x] .nil
def Some (x : Var Γ a) : Step F Γ (.option a) := call (.some a : ValueOp _ _ _) h![x] .nil
def None (a : Ty) : Step F Γ (.option a) := call (.none a : ValueOp _ _ _) .nil .nil
def Bind (x : Var Γ (.option a)) (body : Program F [a] (.option b)) : Step F Γ (.option b) :=
  call (.bind a b : ValueOp _ _ _) h![x] (.cons body .nil)
def Nil (a : Ty) : Step F Γ (.list a) := call (.nil a : ValueOp _ _ _) .nil .nil
def Cons (x : Var Γ a) (xs : Var Γ (.list a)) : Step F Γ (.list a) :=
  call (.cons a : ValueOp _ _ _) h![x,xs] .nil
def Match {captures : List Ty} (x : Var Γ (.option a)) (refs : HList (Var Γ) captures)
    (onNone : Program F captures b) (onSome : Program F (a :: captures) b) : Step F Γ b :=
  call (.case a b captures : ValueOp _ _ _) (.cons x refs) (.cons onNone (.cons onSome .nil))
end Witgen.value
