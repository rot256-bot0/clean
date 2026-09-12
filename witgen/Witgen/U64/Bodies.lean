import Witgen.U64.Op

namespace Witgen.U64
open Witgen.Typed Witgen.Methods

/-- Reifiable Add body: only limb/flag operations and structural packing. -/
def addBody : Program (WithCalls U64Op []) addSig.args addSig.result :=
  .let_ (.inl (.flag false)) (.nil) .nil <|
  .let_ (.inl (.get 0)) (.cons (.succ (.zero)) (.nil)) .nil <|
  .let_ (.inl (.get 1)) (.cons (.succ (.succ (.zero))) (.nil)) .nil <|
  .let_ (.inl (.get 2)) (.cons (.succ (.succ (.succ (.zero)))) (.nil)) .nil <|
  .let_ (.inl (.get 3)) (.cons (.succ (.succ (.succ (.succ (.zero))))) (.nil)) .nil <|
  .let_ (.inl (.get 0)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))) (.nil)) .nil <|
  .let_ (.inl (.get 1)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))) (.nil)) .nil <|
  .let_ (.inl (.get 2)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))) (.nil)) .nil <|
  .let_ (.inl (.get 3)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))) (.nil)) .nil <|
  .let_ (.inl (.get 0)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))) (.nil)) .nil <|
  .let_ (.inl (.get 1)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))))) (.nil)) .nil <|
  .let_ (.inl (.get 2)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))))) (.nil)) .nil <|
  .let_ (.inl (.get 3)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))))))) (.nil)) .nil <|
  .let_ (.inl (.adcWord)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))) (.cons (.succ (.succ (.succ (.zero)))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))))) (.nil)))) .nil <|
  .let_ (.inl (.adcFlag)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))) (.cons (.succ (.succ (.succ (.succ (.zero))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))))) (.nil)))) .nil <|
  .let_ (.inl (.adcWord)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))) (.cons (.succ (.succ (.succ (.succ (.zero))))) (.cons (.zero) (.nil)))) .nil <|
  .let_ (.inl (.adcFlag)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.zero)))))) (.cons (.succ (.zero)) (.nil)))) .nil <|
  .let_ (.inl (.adcWord)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.zero)))))) (.cons (.zero) (.nil)))) .nil <|
  .let_ (.inl (.adcFlag)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))) (.cons (.succ (.zero)) (.nil)))) .nil <|
  .let_ (.inl (.adcWord)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))) (.cons (.zero) (.nil)))) .nil <|
  .let_ (.inl (.adcFlag)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))) (.cons (.succ (.zero)) (.nil)))) .nil <|
  .let_ (.inl (.sbbWord)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))))))))))))) (.nil)))) .nil <|
  .let_ (.inl (.sbbFlag)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))))))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))))))))))))) (.nil)))) .nil <|
  .let_ (.inl (.sbbWord)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))))))))))))) (.cons (.zero) (.nil)))) .nil <|
  .let_ (.inl (.sbbFlag)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))))))))))))) (.cons (.succ (.zero)) (.nil)))) .nil <|
  .let_ (.inl (.sbbWord)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))))))))))))) (.cons (.zero) (.nil)))) .nil <|
  .let_ (.inl (.sbbFlag)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))))))))))))))) (.cons (.succ (.zero)) (.nil)))) .nil <|
  .let_ (.inl (.sbbWord)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))))))))))))))) (.cons (.zero) (.nil)))) .nil <|
  .let_ (.inl (.sbbFlag)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))))))))))))))) (.cons (.succ (.zero)) (.nil)))) .nil <|
  .let_ (.inl (.pack)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))) (.nil))))) .nil <|
  .let_ (.inl (.pack)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))) (.cons (.succ (.succ (.succ (.succ (.zero))))) (.cons (.succ (.succ (.zero))) (.nil))))) .nil <|
  .let_ (.inl (.not)) (.cons (.succ (.succ (.zero))) (.nil)) .nil <|
  .let_ (.inl (.or)) (.cons (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))))))) (.cons (.zero) (.nil))) .nil <|
  .let_ (.inl (.select)) (.cons (.zero) (.cons (.succ (.succ (.zero))) (.cons (.succ (.succ (.succ (.zero)))) (.nil)))) .nil <|
  .ret .zero


def addLibrary : Library U64Op [addSig] :=
  .cons .nil addSig (by decide) addBody

theorem addBody_eval (p a b : Word4) :
    addBody.eval ((Library.nil : Library U64Op []).model primitive) h![p,a,b] =
      Word4.Add p a b := by
  simp only [addBody, Program.eval, Regions.eval, HList.map, Var.get,
    Library.model, Model.sum, primitive, Word4.limb]
  rfl

/-- Two earlier Add call refs, not an inlined implementation. The sum for the
zero-bit alternative is evaluated eagerly; no constant-time claim is made. -/
def mulStep : Program (WithCalls U64Op [addSig])
    [.nat,.word4,.word4,.word4,.word4] .word4 :=
  witgen [i,r,p,a,b] do
    let d ← invoke (.zero : Ref [addSig] addSig) h![p,r,r]
    let s ← invoke (.zero : Ref [addSig] addSig) h![p,d,b]
    let c ← prim .bitAt h![a,i]
    let out ← prim .select h![c,s,d]
    return out

def mulBodyN (n : Nat) : Program (WithCalls U64Op [addSig]) mulSig.args mulSig.result :=
  .let_ (.inl (.literal Word4.zero)) .nil .nil <|
  .let_ (.inl (.repeat n)) h![.succ .zero, .succ (.succ .zero),
    .succ (.succ (.succ .zero)), .zero] (.cons mulStep .nil) <|
  .ret .zero

def mulBody := mulBodyN 256

def mulLibrary : Library U64Op [mulSig,addSig] :=
  .cons addLibrary mulSig (by decide) mulBody

theorem eval_primitive (lib : Library U64Op ms) (op : U64Op args shapes t)
    (xs : HList Val args) (bs : HList (Body Val) shapes) :
    (lib.model primitive).eval (.inl op) xs bs = primitive.eval op xs bs := rfl

theorem eval_addCall (p a b : Word4) :
    (addLibrary.model primitive).eval (.inr (.call .zero)) h![p,a,b] .nil =
      Word4.Add p a b := addBody_eval p a b

theorem addLibrary_values : addLibrary.eval primitive =
    h![(fun xs => match xs with | h![p,a,b] => Word4.Add p a b)] := by
  rw [addLibrary, Library.eval_cons]
  apply congrArg (fun f : MethodValue Val addSig => HList.cons f .nil)
  funext xs
  cases xs with
  | cons p xs =>
    cases xs with
    | cons a xs =>
      cases xs with
      | cons b xs =>
        cases xs
        exact addBody_eval p a b

theorem mulStep_eval (i : Nat) (r p a b : Word4) :
    mulStep.eval (addLibrary.model primitive) h![i,r,p,a,b] =
      (if a.bitAt i then Word4.Add p (Word4.Add p r r) b else Word4.Add p r r) := by
  rw [Library.model, addLibrary_values]
  rfl

theorem repeat_mulStep (p a b : Word4) (n : Nat) (r : Word4) :
    repeatDown (fun i r => mulStep.eval (addLibrary.model primitive) h![i,r,p,a,b]) n r =
      Word4.mulLoop p a b n r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    simp only [repeatDown, Word4.mulLoop]
    rw [ih, mulStep_eval]

theorem mulBodyN_eval (n : Nat) (p a b : Word4) :
    (mulBodyN n).eval (addLibrary.model primitive) h![p,a,b] =
      repeatDown (fun i r => mulStep.eval (addLibrary.model primitive) h![i,r,p,a,b])
        n Word4.zero := rfl

theorem mulBody_eval (p a b : Word4) :
    mulBody.eval (addLibrary.model primitive) h![p,a,b] = Word4.Mul p a b := by
  rw [mulBody, mulBodyN_eval]
  exact repeat_mulStep p a b 256 Word4.zero

def squareBody : Program (WithCalls U64Op [mulSig,addSig]) squareSig.args squareSig.result :=
  .let_ (.inr (.call .zero)) h![.zero, .succ .zero, .succ .zero] .nil (.ret .zero)

def library : Library U64Op [squareSig,mulSig,addSig] :=
  .cons mulLibrary squareSig (by decide) squareBody

theorem eval_mulCall (p a b : Word4) :
    (mulLibrary.model primitive).eval (.inr (.call .zero)) h![p,a,b] .nil =
      Word4.Mul p a b := by
  rw [mulLibrary, Library.call_head, mulBody_eval]

theorem squareBody_run (M : Model (WithCalls U64Op [mulSig,addSig]) Val) (p a : Word4) :
    squareBody.eval M h![p,a] = M.eval (.inr (.call .zero)) h![p,a,a] .nil := rfl

theorem squareBody_eval (p a : Word4) :
    squareBody.eval (mulLibrary.model primitive) h![p,a] = Word4.Square p a := by
  rw [squareBody_run, eval_mulCall]
  rfl

/-- These endpoints discharge implementation correctness for the actual stored AST. -/
theorem addBody_correct (p a b : Word4) (hp : 0 < p.decode)
    (ha : Word4.Canonical p.decode a) (hb : Word4.Canonical p.decode b) :
    (addBody.eval ((Library.nil : Library U64Op []).model primitive) h![p,a,b]).decode =
      (a.decode+b.decode) % p.decode ∧
    Word4.Canonical p.decode (addBody.eval ((Library.nil : Library U64Op []).model primitive) h![p,a,b]) := by
  rw [addBody_eval]; exact Word4.Add_correct p a b hp ha hb

theorem mulBody_correct (p a b : Word4) (hp : 0 < p.decode)
    (ha : Word4.Canonical p.decode a) (hb : Word4.Canonical p.decode b) :
    (mulBody.eval (addLibrary.model primitive) h![p,a,b]).decode =
      (a.decode*b.decode) % p.decode ∧
    Word4.Canonical p.decode (mulBody.eval (addLibrary.model primitive) h![p,a,b]) := by
  rw [mulBody_eval]; exact Word4.Mul_correct p a b hp ha hb

theorem squareBody_correct (p a : Word4) (hp : 0 < p.decode)
    (ha : Word4.Canonical p.decode a) :
    (squareBody.eval (mulLibrary.model primitive) h![p,a]).decode =
      (a.decode*a.decode) % p.decode ∧
    Word4.Canonical p.decode (squareBody.eval (mulLibrary.model primitive) h![p,a]) := by
  rw [squareBody_eval]; exact Word4.Square_correct p a hp ha

end Witgen.U64
