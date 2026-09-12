import Witgen.Methods
import Witgen.Typed.Types

namespace Witgen.Typed.MethodTests
open Witgen Methods

inductive Prim : Signature Ty where
  | add : Prim [.nat, .nat] [] .nat

def primitive : Model Prim (fun _ => Nat) where
  eval := fun .add (.cons a (.cons b .nil)) _ => a + b

def twiceSig : MethodSig Ty := ⟨"twice", [.nat], .nat⟩
def twiceBody : Program (WithCalls Prim []) [.nat] .nat :=
  .let_ (.inl .add) (.cons .zero (.cons .zero .nil)) .nil (.ret .zero)
def lib : Library Prim [twiceSig] := .cons .nil twiceSig (by decide) twiceBody
def caller : Program (WithCalls Prim [twiceSig]) [.nat] .nat :=
  .let_ (.inr (.call .zero)) (.cons .zero .nil) .nil (.ret .zero)
example : caller.eval (lib.model primitive) (.cons 7 .nil) = 14 := rfl

end Witgen.Typed.MethodTests

namespace Witgen.Typed.MethodTests
open Witgen Methods

def quadSig : MethodSig Ty := ⟨"quad", [.nat], .nat⟩
def quadBody : Program (WithCalls Prim [twiceSig]) [.nat] .nat :=
  .let_ (.inr (.call .zero)) (.cons .zero .nil) .nil
    (.let_ (.inr (.call .zero)) (.cons .zero .nil) .nil (.ret .zero))
def lib2 : Library Prim [quadSig, twiceSig] := .cons lib quadSig (by decide) quadBody

def nestedCaller : Program (WithCalls Prim [quadSig, twiceSig]) [.nat] .nat :=
  .let_ (.inr (.call .zero)) (.cons .zero .nil) .nil (.ret .zero)

example : nestedCaller.eval (lib2.model primitive) (.cons 7 .nil) = 28 := rfl
example : [quadSig.name, twiceSig.name].Nodup := lib2.names_unique
example : (Ref.zero : Ref [quadSig, twiceSig] quadSig).index < 2 := Ref.index_lt _

example : HEq (Ref.zero : Ref [quadSig, twiceSig] quadSig)
    (Ref.zero : Ref [quadSig, twiceSig] quadSig) :=
  lib2.ref_unique .zero .zero rfl

end Witgen.Typed.MethodTests
