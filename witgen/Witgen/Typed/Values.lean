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

def ValueOp.model (fields : FieldId → Type) (words points : Type) :
    Model ValueOp (Value fields words points) where
  eval := fun op args regions => match op, args, regions with
    | .pair _ _, .cons a (.cons b .nil), .nil => (a,b)
    | .fst _ _, .cons a .nil, .nil => a.1
    | .snd _ _, .cons a .nil, .nil => a.2
    | .some _, .cons a .nil, .nil => Option.some a
    | .none _, .nil, .nil => Option.none
    | .bind _ _, .cons a .nil, .cons body .nil => a.bind (fun x => body (.cons x .nil))

open Lean Methods in
def ValueOp.codec : OpCodec ValueOp := fun op =>
  let tag := match op with
    | .pair .. => "value.pair"
    | .fst .. => "value.fst"
    | .snd .. => "value.snd"
    | .some .. => "option.some"
    | .none .. => "option.none"
    | .bind .. => "option.bind"
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
end Witgen.value
