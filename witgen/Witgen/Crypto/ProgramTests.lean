import Witgen.Crypto.Program

open Witgen Witgen.Crypto

example {p : Nat} (hp : 0 < p) (program : Program QuadFeature Γ t)
    (env : HList (Val (Fin p)) Γ) :
    (program.lower quadToField).eval (fieldModel hp) env =
      program.eval (quadFeatureModel hp) env :=
  quadToField_correct hp program env

example {p : Nat} (hp : 0 < p) (x y : Fin p) :
    quadraticField.eval (fieldModel hp) (.cons x (.cons y .nil)) =
      (⟨Residue.mul x x, Residue.add (Residue.mul x x) y⟩ : QuadWitness (Fin p)) := by
  exact quadraticField_eval hp x y

example {p : Nat} (hp : 0 < p) (x y : Fin p) :
    (quadraticNat p).eval natModel (.cons x.val (.cons y.val .nil)) =
      (⟨(x.val * x.val) % p, ((x.val * x.val) % p + y.val) % p⟩ : QuadWitness Nat) := by
  exact quadraticNat_eval hp x y

example {p : Nat} (hp : 0 < p) (program : Program FieldSig Γ t)
    (env : HList (Val (Fin p)) Γ) :
    Val.map Fin.val (program.eval (fieldModel hp) env) =
      (program.lower (fieldToNat p)).eval natModel (env.map (Val.map Fin.val)) :=
  fieldToNat_correct hp program env

-- Large literal reduction is exercised through the real feature AST too.
def wideLiteral : Program FieldSig [] .scalar :=
  witgen [] do
    let value ← fieldConst (bn254Modulus + 2 ^ 200)
    return value

example : (wideLiteral.eval (fieldModel bn254Positive) .nil).val = 2 ^ 200 := by decide
example : (wideLiteral.lower (fieldToNat bn254Modulus)).eval natModel .nil = 2 ^ 200 := by decide

-- The arithmetic theorem intentionally requires positivity, not primality.
example : ((quadraticNat 100).eval natModel (.cons 99 (.cons 98 .nil))).output = 99 := by decide

example :
    ((quadraticNat bn254Modulus).eval natModel
      (.cons (bn254Modulus - 1) (.cons (bn254Modulus - 2) .nil))).output =
      bn254Modulus - 1 := by decide
