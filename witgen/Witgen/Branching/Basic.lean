import Witgen.Authoring

namespace Witgen

/-- Optional branching over a library's Bool sort. Both regions have the same
result and receive exactly the captures declared in the operation arguments. -/
inductive BranchOp {S : Type} (bool : S) : Signature S where
  | branch (captures : List S) (result : S) :
      BranchOp bool (bool :: captures)
        [⟨captures, result⟩, ⟨captures, result⟩] result

/-- Region functions are selected, not eagerly evaluated branch values. -/
def BranchOp.model {S : Type} {bool : S} (V : S → Type)
    (toBool : V bool → Bool) : Model (BranchOp bool) V where
  eval := fun op args regions => match op, args, regions with
    | .branch _ _, .cons condition captures, .cons yes (.cons no .nil) =>
        if toBool condition then yes captures else no captures

@[simp] theorem BranchOp.eval_true {S : Type} {bool : S} {captures : List S} {result : S} (V : S → Type)
    (toBool : V bool → Bool) (condition : V bool) (h : toBool condition = true)
    (env : HList V captures) (yes no : HList V captures → V result) :
    (model V toBool).eval (.branch captures result) (.cons condition env)
      (.cons yes (.cons no .nil)) = yes env := by simp [model, h]

@[simp] theorem BranchOp.eval_false {S : Type} {bool : S} {captures : List S} {result : S} (V : S → Type)
    (toBool : V bool → Bool) (condition : V bool) (h : toBool condition = false)
    (env : HList V captures) (yes no : HList V captures → V result) :
    (model V toBool).eval (.branch captures result) (.cons condition env)
      (.cons yes (.cons no .nil)) = no env := by simp [model, h]

namespace control

/-- The Bool sort is inferred from the condition; Bool algebra is not required. -/
def If {S : Type} {F : Signature S} {Γ captures : List S} {bool result : S}
    [Has (BranchOp bool) F] (condition : Var Γ bool)
    (refs : HList (Var Γ) captures)
    (yes no : Program F captures result) : Step F Γ result :=
  call (BranchOp.branch (bool := bool) captures result) (.cons condition refs)
    (.cons yes (.cons no .nil))

end control
end Witgen
