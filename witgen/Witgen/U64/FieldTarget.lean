import Witgen.U64.Bodies
import Witgen.Typed.Field

namespace Witgen.U64
open Witgen.Typed Witgen.Methods

theorem modulus_lt (f : FieldId) : modulus f < capacity := by
  unfold modulus
  split <;> first | decide | (split <;> decide)

/-- Static method parameter encoded at AST construction / ABI setup only. -/
def wordModulus (f : FieldId) : Word4 := Word4.encode (modulus f)

@[simp] theorem wordModulus_decode (f : FieldId) : (wordModulus f).decode = modulus f :=
  Word4.decode_encode_of_lt (modulus_lt f)

abbrev fieldAddSig (f : FieldId) : MethodSig Ty :=
  ⟨"field." ++ toString f.val ++ ".add.u64", [.field f,.field f], .field f⟩
abbrev fieldMulSig (f : FieldId) : MethodSig Ty :=
  ⟨"field." ++ toString f.val ++ ".mul.u64", [.field f,.field f], .field f⟩
abbrev fieldSquareSig (f : FieldId) : MethodSig Ty :=
  ⟨"field." ++ toString f.val ++ ".square.u64", [.field f], .field f⟩

/-- Layout-only wrapper. Its call reference supplies the arithmetic. -/
def binaryWrapper (f : FieldId)
    (ref : Ref ms (⟨name,[.word4,.word4,.word4],.word4⟩ : MethodSig Ty)) :
    Program (WithCalls U64Op ms) [.field f,.field f] (.field f) :=
  .let_ (.inl (.toWord f)) h![.zero] .nil <|
  .let_ (.inl (.toWord f)) h![.succ (.succ .zero)] .nil <|
  .let_ (.inl (.literal (wordModulus f))) .nil .nil <|
  .let_ (.inr (.call ref)) h![.zero,.succ (.succ .zero),.succ .zero] .nil <|
  .let_ (.inl (.fromWord f)) h![.zero] .nil (.ret .zero)

def unaryWrapper (f : FieldId)
    (ref : Ref ms (⟨name,[.word4,.word4],.word4⟩ : MethodSig Ty)) :
    Program (WithCalls U64Op ms) [.field f] (.field f) :=
  .let_ (.inl (.toWord f)) h![.zero] .nil <|
  .let_ (.inl (.literal (wordModulus f))) .nil .nil <|
  .let_ (.inr (.call ref)) h![.zero,.succ .zero] .nil <|
  .let_ (.inl (.fromWord f)) h![.zero] .nil (.ret .zero)

abbrev fieldAddBody (f : FieldId) (ref : Ref ms addSig) := binaryWrapper f ref
abbrev fieldMulBody (f : FieldId) (ref : Ref ms mulSig) := binaryWrapper f ref
abbrev fieldSquareBody (f : FieldId) (ref : Ref ms squareSig) := unaryWrapper f ref

theorem binaryWrapper_eval (lib : Library U64Op ms) (f : FieldId)
    (ref : Ref ms (⟨name,[.word4,.word4,.word4],.word4⟩ : MethodSig Ty)) (a b : Word4) :
    (binaryWrapper f ref).eval (lib.model primitive) h![a,b] =
      (lib.model primitive).eval (.inr (.call ref)) h![wordModulus f,a,b] .nil := rfl

theorem unaryWrapper_eval (lib : Library U64Op ms) (f : FieldId)
    (ref : Ref ms (⟨name,[.word4,.word4],.word4⟩ : MethodSig Ty)) (a : Word4) :
    (unaryWrapper f ref).eval (lib.model primitive) h![a] =
      (lib.model primitive).eval (.inr (.call ref)) h![wordModulus f,a] .nil := rfl

/-- Earlier calls retain their implementation when the library grows. -/
theorem call_tail (lib : Library U64Op ms) (m : MethodSig Ty) (fresh)
    (body : Program (WithCalls U64Op ms) m.args m.result)
    (r : Ref ms sig) (xs : HList Val sig.args) :
    ((Library.cons lib m fresh body).model primitive).eval
      (.inr (.call (.succ r))) xs .nil =
    (lib.model primitive).eval (.inr (.call r)) xs .nil := rfl

def bnAddLibrary : Library U64Op [fieldAddSig bn254Fr,squareSig,mulSig,addSig] :=
  .cons library (fieldAddSig bn254Fr) (by decide) (fieldAddBody bn254Fr (.succ (.succ (.zero))))

def bnMulLibrary : Library U64Op [fieldMulSig bn254Fr,fieldAddSig bn254Fr,squareSig,mulSig,addSig] :=
  .cons bnAddLibrary (fieldMulSig bn254Fr) (by decide) (fieldMulBody bn254Fr (.succ (.succ (.zero))))

def bnSquareLibrary : Library U64Op [fieldSquareSig bn254Fr,fieldMulSig bn254Fr,fieldAddSig bn254Fr,squareSig,mulSig,addSig] :=
  .cons bnMulLibrary (fieldSquareSig bn254Fr) (by decide) (fieldSquareBody bn254Fr (.succ (.succ (.zero))))

def baseAddLibrary : Library U64Op [fieldAddSig secpBase,fieldSquareSig bn254Fr,fieldMulSig bn254Fr,fieldAddSig bn254Fr,squareSig,mulSig,addSig] :=
  .cons bnSquareLibrary (fieldAddSig secpBase) (by decide) (fieldAddBody secpBase (.succ (.succ (.succ (.succ (.succ (.zero)))))))

def baseMulLibrary : Library U64Op [fieldMulSig secpBase,fieldAddSig secpBase,fieldSquareSig bn254Fr,fieldMulSig bn254Fr,fieldAddSig bn254Fr,squareSig,mulSig,addSig] :=
  .cons baseAddLibrary (fieldMulSig secpBase) (by decide) (fieldMulBody secpBase (.succ (.succ (.succ (.succ (.succ (.zero)))))))

def baseSquareLibrary : Library U64Op [fieldSquareSig secpBase,fieldMulSig secpBase,fieldAddSig secpBase,fieldSquareSig bn254Fr,fieldMulSig bn254Fr,fieldAddSig bn254Fr,squareSig,mulSig,addSig] :=
  .cons baseMulLibrary (fieldSquareSig secpBase) (by decide) (fieldSquareBody secpBase (.succ (.succ (.succ (.succ (.succ (.zero)))))))

def scalarAddLibrary : Library U64Op [fieldAddSig secpScalar,fieldSquareSig secpBase,fieldMulSig secpBase,fieldAddSig secpBase,fieldSquareSig bn254Fr,fieldMulSig bn254Fr,fieldAddSig bn254Fr,squareSig,mulSig,addSig] :=
  .cons baseSquareLibrary (fieldAddSig secpScalar) (by decide) (fieldAddBody secpScalar (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))

def scalarMulLibrary : Library U64Op [fieldMulSig secpScalar,fieldAddSig secpScalar,fieldSquareSig secpBase,fieldMulSig secpBase,fieldAddSig secpBase,fieldSquareSig bn254Fr,fieldMulSig bn254Fr,fieldAddSig bn254Fr,squareSig,mulSig,addSig] :=
  .cons scalarAddLibrary (fieldMulSig secpScalar) (by decide) (fieldMulBody secpScalar (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))

def scalarSquareLibrary : Library U64Op [fieldSquareSig secpScalar,fieldMulSig secpScalar,fieldAddSig secpScalar,fieldSquareSig secpBase,fieldMulSig secpBase,fieldAddSig secpBase,fieldSquareSig bn254Fr,fieldMulSig bn254Fr,fieldAddSig bn254Fr,squareSig,mulSig,addSig] :=
  .cons scalarMulLibrary (fieldSquareSig secpScalar) (by decide) (fieldSquareBody secpScalar (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))))

abbrev allSigs : List (MethodSig Ty) := [fieldSquareSig secpScalar,fieldMulSig secpScalar,fieldAddSig secpScalar,fieldSquareSig secpBase,fieldMulSig secpBase,fieldAddSig secpBase,fieldSquareSig bn254Fr,fieldMulSig bn254Fr,fieldAddSig bn254Fr,squareSig,mulSig,addSig]

def allLibrary : Library U64Op allSigs := scalarSquareLibrary

def fieldAddRef (f : FieldId) : Ref allSigs (fieldAddSig f) :=
  Fin.cases (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))))) (Fin.cases (.succ (.succ (.succ (.succ (.succ (.zero)))))) (Fin.cases (.succ (.succ (.zero))) (fun i => Fin.elim0 i))) f

def fieldMulRef (f : FieldId) : Ref allSigs (fieldMulSig f) :=
  Fin.cases (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.zero)))))))) (Fin.cases (.succ (.succ (.succ (.succ (.zero))))) (Fin.cases (.succ (.zero)) (fun i => Fin.elim0 i))) f

def fieldSquareRef (f : FieldId) : Ref allSigs (fieldSquareSig f) :=
  Fin.cases (.succ (.succ (.succ (.succ (.succ (.succ (.zero))))))) (Fin.cases (.succ (.succ (.succ (.zero)))) (Fin.cases (.zero) (fun i => Fin.elim0 i))) f

theorem fieldAdd_eval (f : FieldId) (a b : Word4) :
    (allLibrary.model primitive).eval (.inr (.call (fieldAddRef f))) h![a,b] .nil =
      Word4.Add (wordModulus f) a b := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) f
  all_goals simp only [fieldAddRef, Fin.cases_zero, Fin.cases_succ, allLibrary,
    scalarSquareLibrary, scalarMulLibrary, scalarAddLibrary, baseSquareLibrary, baseMulLibrary, baseAddLibrary, bnSquareLibrary, bnMulLibrary, bnAddLibrary,
    library, mulLibrary, addLibrary]
  all_goals repeat rw (config := { transparency := .default }) [call_tail]
  all_goals rw (config := { transparency := .default }) [Library.call_head, fieldAddBody, binaryWrapper_eval]
  all_goals repeat rw (config := { transparency := .default }) [call_tail]
  all_goals rw (config := { transparency := .default }) [Library.call_head]
  all_goals exact addBody_eval _ _ _

theorem fieldMul_eval (f : FieldId) (a b : Word4) :
    (allLibrary.model primitive).eval (.inr (.call (fieldMulRef f))) h![a,b] .nil =
      Word4.Mul (wordModulus f) a b := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) f
  all_goals simp only [fieldMulRef, Fin.cases_zero, Fin.cases_succ, allLibrary,
    scalarSquareLibrary, scalarMulLibrary, scalarAddLibrary, baseSquareLibrary, baseMulLibrary, baseAddLibrary, bnSquareLibrary, bnMulLibrary, bnAddLibrary,
    library, mulLibrary, addLibrary]
  all_goals repeat rw (config := { transparency := .default }) [call_tail]
  all_goals rw (config := { transparency := .default }) [Library.call_head, fieldMulBody, binaryWrapper_eval]
  all_goals repeat rw (config := { transparency := .default }) [call_tail]
  all_goals rw (config := { transparency := .default }) [Library.call_head]
  all_goals exact mulBody_eval _ _ _

theorem fieldSquare_eval (f : FieldId) (a : Word4) :
    (allLibrary.model primitive).eval (.inr (.call (fieldSquareRef f))) h![a] .nil =
      Word4.Square (wordModulus f) a := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) f
  all_goals simp only [fieldSquareRef, Fin.cases_zero, Fin.cases_succ, allLibrary,
    scalarSquareLibrary, scalarMulLibrary, scalarAddLibrary, baseSquareLibrary, baseMulLibrary, baseAddLibrary, bnSquareLibrary, bnMulLibrary, bnAddLibrary,
    library, mulLibrary, addLibrary]
  all_goals repeat rw (config := { transparency := .default }) [call_tail]
  all_goals rw (config := { transparency := .default }) [Library.call_head, fieldSquareBody, unaryWrapper_eval]
  all_goals repeat rw (config := { transparency := .default }) [call_tail]
  all_goals rw (config := { transparency := .default }) [Library.call_head]
  all_goals exact squareBody_eval _ _

end Witgen.U64
