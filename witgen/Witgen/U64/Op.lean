import Witgen.U64.Mul
import Witgen.Typed.Types
import Witgen.Methods
import Witgen.Authoring

namespace Witgen.U64
open Witgen.Typed Witgen.Methods

/-- Word representation model. Logical field identity remains in the Ty index. -/
abbrev Val : Ty → Type
  | .field _ => Word4
  | .word4 => Word4
  | .u64 => UInt64
  | .bool => Bool
  | .nat => Nat
  | .point => PUnit
  | .pair a b => Val a × Val b
  | .option a => Option (Val a)

def Word4.limb (a : Word4) (i : Fin 4) : UInt64 :=
  match i.val with
  | 0 => a.l0
  | 1 => a.l1
  | 2 => a.l2
  | _ => a.l3

/-- Bounded descending loop with one mutable word4 accumulator, three explicit
word4 captures and one Nat index. Only the loop index is a Nat at runtime. -/
def repeatDown (step : Nat → Word4 → Word4) : Nat → Word4 → Word4
  | 0, r => r
  | n+1, r => repeatDown step n (step n r)

/-- The finite low-level signature: no field add/mul/square intrinsics. -/
inductive U64Op : Signature Ty where
  | word (v : UInt64) : U64Op [] [] .u64
  | flag (v : Bool) : U64Op [] [] .bool
  | literal (v : Word4) : U64Op [] [] .word4
  | get (i : Fin 4) : U64Op [.word4] [] .u64
  | pack : U64Op [.u64, .u64, .u64, .u64] [] .word4
  | adcWord : U64Op [.u64, .u64, .bool] [] .u64
  | adcFlag : U64Op [.u64, .u64, .bool] [] .bool
  | sbbWord : U64Op [.u64, .u64, .bool] [] .u64
  | sbbFlag : U64Op [.u64, .u64, .bool] [] .bool
  | or : U64Op [.bool, .bool] [] .bool
  | not : U64Op [.bool] [] .bool
  | select : U64Op [.bool, .word4, .word4] [] .word4
  | bitAt : U64Op [.word4, .nat] [] .bool
  | repeat (n : Nat) : U64Op [.word4, .word4, .word4, .word4]
      [⟨[.nat, .word4, .word4, .word4, .word4], .word4⟩] .word4
  | toWord (f : FieldId) : U64Op [.field f] [] .word4
  | fromWord (f : FieldId) : U64Op [.word4] [] (.field f)
  | fieldLiteral (f : FieldId) (v : Word4) : U64Op [] [] (.field f)

def choose (c : Bool) (a b : Word4) : Word4 := if c then a else b

def primitive : Model U64Op Val where
  eval := fun op args regions => match op, args, regions with
    | .word v, .nil, .nil => v
    | .flag v, .nil, .nil => v
    | .literal v, .nil, .nil => v
    | .get i, .cons a .nil, .nil => a.limb i
    | .pack, .cons a (.cons b (.cons c (.cons d .nil))), .nil => ⟨a,b,c,d⟩
    | .adcWord, .cons a (.cons b (.cons c .nil)), .nil => (adc a b c).1
    | .adcFlag, .cons a (.cons b (.cons c .nil)), .nil => (adc a b c).2
    | .sbbWord, .cons a (.cons b (.cons c .nil)), .nil => (sbb a b c).1
    | .sbbFlag, .cons a (.cons b (.cons c .nil)), .nil => (sbb a b c).2
    | .or, .cons a (.cons b .nil), .nil => a || b
    | .not, .cons a .nil, .nil => !a
    | .select, .cons c (.cons a (.cons b .nil)), .nil => choose c a b
    | .bitAt, .cons a (.cons i .nil), .nil => a.bitAt i
    | .repeat n, .cons p (.cons a (.cons b (.cons r .nil))), .cons body .nil =>
        repeatDown (fun i r => body h![i,r,p,a,b]) n r
    | .toWord _, .cons a .nil, .nil => a
    | .fromWord _, .cons a .nil, .nil => a
    | .fieldLiteral _ v, .nil, .nil => v

def prim {ms : List (MethodSig Ty)} (op : U64Op args [] t)
    (refs : HList (Var Γ) args) :
    Step (WithCalls U64Op ms) Γ t := ⟨_, _, .inl op, refs, .nil⟩

def repeatStep (n : Nat)
    (refs : HList (Var Γ) [.word4,.word4,.word4,.word4])
    (body : Program (WithCalls U64Op ms) [.nat,.word4,.word4,.word4,.word4] .word4) :
    Step (WithCalls U64Op ms) Γ .word4 :=
  ⟨_, _, .inl (.repeat n), refs, .cons body .nil⟩

def invoke (ref : Ref ms m) (refs : HList (Var Γ) m.args) :
    Step (WithCalls U64Op ms) Γ m.result := ⟨_, _, .inr (.call ref), refs, .nil⟩

abbrev addSig : MethodSig Ty := ⟨"u64.field.add", [.word4,.word4,.word4], .word4⟩
abbrev mulSig : MethodSig Ty := ⟨"u64.field.mul", [.word4,.word4,.word4], .word4⟩
abbrev squareSig : MethodSig Ty := ⟨"u64.field.square", [.word4,.word4], .word4⟩

/-- An execution derivation counting loop-region invocations, not CPU cycles. -/
inductive RepeatExec (step : Nat → Word4 → Word4) : Nat → Word4 → Word4 → Nat → Prop
  | done (r) : RepeatExec step 0 r r 0
  | next (n r out k) : RepeatExec step n (step n r) out k →
      RepeatExec step (n+1) r out (k+1)

theorem repeatDown_exec (step : Nat → Word4 → Word4) (n : Nat) (r : Word4) :
    RepeatExec step n r (repeatDown step n r) n := by
  induction n generalizing r with
  | zero => exact .done r
  | succ n ih => exact .next n r _ n (ih (step n r))

theorem RepeatExec.steps {step n r out k} (h : RepeatExec step n r out k) : k = n := by
  induction h with
  | done => rfl
  | next _ _ _ _ _ ih => omega

end Witgen.U64
