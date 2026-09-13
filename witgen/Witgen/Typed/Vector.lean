import Witgen.Typed.Export

namespace Witgen.Typed
open Witgen

/-- Optional list storage and bounded iteration. All executable bodies are finite regions. -/
inductive VectorOp : Signature Ty where
  | empty (t : Ty) : VectorOp [] [] (.list t)
  | singleton (t : Ty) : VectorOp [t] [] (.list t)
  | nats (xs : List Nat) : VectorOp [] [] (.list .nat)
  | apply (t : Ty) (captures : List Ty) : VectorOp captures [⟨captures, t⟩] t
  | getD (t : Ty) : VectorOp [.list t, .nat, t] [] t
  | append (t : Ty) : VectorOp [.list t, .list t] [] (.list t)
  | take (t : Ty) (n : Nat) : VectorOp [.list t] [] (.list t)
  | drop (t : Ty) (n : Nat) : VectorOp [.list t] [] (.list t)
  | flatten (t : Ty) : VectorOp [.list (.list t)] [] (.list t)
  | tabulate (t : Ty) (n : Nat) (captures : List Ty) :
      VectorOp captures [⟨.nat :: captures, t⟩] (.list t)
  | fold (t : Ty) (n : Nat) (captures : List Ty) :
      VectorOp (t :: captures) [⟨.nat :: t :: captures, t⟩] t

def VectorOp.model : Model VectorOp FieldVal where
  eval := fun op args regions => match op, args, regions with
    | .empty _, .nil, .nil => []
    | .singleton _, h![x], .nil => [x]
    | .nats xs, .nil, .nil => xs
    | .apply _ _, captures, .cons body .nil => body captures
    | .getD _, h![xs, i, fallback], .nil => xs[i]?.getD fallback
    | .append _, h![xs, ys], .nil => xs ++ ys
    | .take _ n, h![xs], .nil => xs.take n
    | .drop _ n, h![xs], .nil => xs.drop n
    | .flatten _, h![xs], .nil => xs.flatten
    | .tabulate _ n _, captures, .cons body .nil =>
        (List.range n).map (fun i => body (.cons i captures))
    | .fold _ n _, .cons initial captures, .cons body .nil =>
        (List.range n).foldl (fun acc i => body (.cons i (.cons acc captures))) initial

@[simp] theorem VectorOp.tabulate_length (t : Ty) (n : Nat) (captures : List Ty)
    (xs : HList FieldVal captures) (body : Body FieldVal ⟨.nat :: captures, t⟩) :
    (model.eval (.tabulate t n captures) xs (.cons body .nil)).length = n := by
  simp [model]

@[simp] theorem VectorOp.fold_zero (t : Ty) (captures : List Ty)
    (initial : FieldVal t) (xs : HList FieldVal captures)
    (body : Body FieldVal ⟨.nat :: t :: captures, t⟩) :
    model.eval (.fold t 0 captures) (.cons initial xs) (.cons body .nil) = initial := rfl

open Lean Methods in
def VectorOp.codec : OpCodec VectorOp := fun op =>
  let (tag, extra) : String × List (String × Json) := match op with
    | .empty _ => ("vector.empty", [])
    | .singleton _ => ("vector.singleton", [])
    | .nats xs => ("vector.nats", [("values", .arr ((xs.map (fun n => Json.str (toString n))).toArray))])
    | .apply _ _ => ("vector.apply", [])
    | .getD _ => ("vector.getD", [])
    | .append _ => ("vector.append", [])
    | .take _ n => ("vector.take", [("count", toJson n)])
    | .drop _ n => ("vector.drop", [("count", toJson n)])
    | .flatten _ => ("vector.flatten", [])
    | .tabulate _ n _ => ("vector.tabulate", [("count", toJson n)])
    | .fold _ n _ => ("vector.fold", [("count", toJson n)])
  Json.mkObj [("op", .str tag), ("static", Json.mkObj extra)]

end Witgen.Typed

namespace Witgen.vector
open Typed
variable {F : Signature Ty} {Γ : List Ty} [Has VectorOp F] {t : Ty}

def Empty (t : Ty) : Step F Γ (.list t) := call (VectorOp.empty t) .nil .nil

def Singleton (x : Var Γ t) : Step F Γ (.list t) := call (VectorOp.singleton t) h![x] .nil

def Nats (xs : List Nat) : Step F Γ (.list .nat) := call (VectorOp.nats xs) .nil .nil

/-- Execute an explicitly captured finite subprogram, never an opaque host callback. -/
def Apply {captures : List Ty} (refs : HList (Var Γ) captures)
    (body : Program F captures t) : Step F Γ t :=
  call (VectorOp.apply t captures) refs (.cons body .nil)

def GetD (xs : Var Γ (.list t)) (i : Var Γ .nat) (fallback : Var Γ t) : Step F Γ t :=
  call (VectorOp.getD t) h![xs, i, fallback] .nil

def Append (xs ys : Var Γ (.list t)) : Step F Γ (.list t) :=
  call (VectorOp.append t) h![xs, ys] .nil

def Take (n : Nat) (xs : Var Γ (.list t)) : Step F Γ (.list t) :=
  call (VectorOp.take t n) h![xs] .nil

def Drop (n : Nat) (xs : Var Γ (.list t)) : Step F Γ (.list t) :=
  call (VectorOp.drop t n) h![xs] .nil

def Flatten (xs : Var Γ (.list (.list t))) : Step F Γ (.list t) :=
  call (VectorOp.flatten t) h![xs] .nil

def Tabulate {captures : List Ty} (n : Nat) (refs : HList (Var Γ) captures)
    (body : Program F (.nat :: captures) t) : Step F Γ (.list t) :=
  call (VectorOp.tabulate t n captures) refs (.cons body .nil)

def Fold {captures : List Ty} (n : Nat) (initial : Var Γ t)
    (refs : HList (Var Γ) captures) (body : Program F (.nat :: t :: captures) t) : Step F Γ t :=
  call (VectorOp.fold t n captures) (.cons initial refs) (.cons body .nil)

end Witgen.vector
