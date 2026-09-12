import Witgen.Authoring
import Witgen.StructTests
namespace Witgen.AuthoringTests
open StructTests

def pairProgram : Program (StructOp desc) [.number, .number] .pair :=
  witgen [x, y] do
    let pair ← makeStruct desc .pair h![x, y]
    return pair

example : pairProgram.eval (structModel repr) h![3, 8] = (3, 8) := rfl
example : pairProgram = Program.let_ (.make .pair)
    (.cons .zero (.cons (.succ .zero) .nil)) .nil (.ret .zero) := rfl
def shadowed : Program (StructOp desc) [.number, .number] .number :=
  witgen [x, y] do
    let old := x
    let x ← makeStruct desc .pair h![x, y]
    let x ← getField desc .pair "right" x
    let pair ← makeStruct desc .pair h![old, x]
    let output ← getField desc .pair "left" pair
    return output

example : shadowed.eval (structModel repr) h![3, 8] = 3 := rfl

-- Even unused input references must have their sorts pinned by the declared context.
def unused : Program (StructOp desc) [.number, .pair] .pair :=
  witgen [_unused, pair] do
    return pair
example : unused.eval (structModel repr) h![7, (3, 8)] = (3, 8) := rfl
def namedFields : Program (StructOp desc) [.number, .number] .pair :=
  witgen [x, y] do
    let result ← makeNamedStruct desc .pair fields![left := x, right := y]
    return result
example : namedFields = pairProgram := rfl

-- The supported ambient interface stays usable without weakening/reference code.
abbrev StaticBase := Nat
def staticAlias (base : StaticBase) : Program (StructOp desc) [.number] .number :=
  let next := base + 1
  witgen [x] do return (fun (_ : Nat) => x) next
example : (staticAlias 8).eval (structModel repr) h![3] = 3 := rfl

example (n : Nat) (i : Int) (b : Bool) (s : String) (c : Char) (u : Unit)
    (u8 : UInt8) (u16 : UInt16) (u32 : UInt32) (u64 : UInt64) (us : USize) (f : Fin n) :
    Program (StructOp desc) [.number] .number :=
  witgen [x] do
    return (fun (_ : Nat) (_ : Int) (_ : Bool) (_ : String) (_ : Char) (_ : Unit)
      (_ : UInt8) (_ : UInt16) (_ : UInt32) (_ : UInt64) (_ : USize) (_ : Fin n) => x)
      n i b s c u u8 u16 u32 u64 us f

example (S : Type) (V : S → Type) : Program (StructOp desc) [.number] .number :=
  witgen [x] do return (fun (_ : S → Type) => x) V

def genericCapability {F : Signature Ty} [Has (StructOp desc) F] :
    Program F [.number, .number] .pair :=
  witgen [x, y] do
    let pair ← makeNamedStruct desc .pair fields![left := x, right := y]
    return pair
example : genericCapability (F := StructOp desc) = pairProgram := rfl

-- An unused ambient local is not a capture.
example {Carrier : Type} (_r : Carrier) : Program (StructOp desc) [.number] .number :=
  witgen [x] do return x

-- Captures must be explicit inputs, even when the outer context has identical sorts.
/-- error: implicit witgen capture 'outer'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (outer : Var (S := Ty) [.number, .number] .number) :
    Program (StructOp desc) [.number, .number] .pair :=
  witgen [_x, y] do
    let pair ← makeStruct desc .pair h![outer, y]
    return pair
-- Pure statements are reference aliases, not arbitrary host-language computation.
example : True := by
  fail_if_success
    have bad : Program (StructOp desc) [.number] .number :=
      witgen [x] do
        let _constant := (3 : Nat)
        return x
  trivial

/-- error: implicit witgen capture 'captured'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (outer : Var (S := Ty) [.number, .number] .number) :
    Program (StructOp desc) [.number, .number] .pair :=
  let captured := fun (_ : Unit) => outer
  witgen [_x, y] do
    let pair ← makeStruct desc .pair h![captured (), y]
    return pair
-- Missing fields, wrong sorts/order, and malformed scopes are rejected.
example : True := by
  fail_if_success
    have bad : Program (StructOp desc) [.pair] .number :=
      witgen [pair] do
        let value ← getField desc .pair "missing" pair
        return value
  fail_if_success
    have bad : Program (StructOp desc) [.number, .number] .pair :=
      witgen [x, y] do
        let result ← makeNamedStruct desc .pair fields![right := x, left := y]
        return result
  fail_if_success
    have bad : Program (StructOp desc) [.pair, .number] .pair :=
      witgen [pair, x] do
        let result ← makeNamedStruct desc .pair fields![left := pair, right := x]
        return result
  fail_if_success
    have bad : Program (StructOp desc) [.number, .number] .number :=
      witgen [x] do return x
  fail_if_success
    have bad : Program (StructOp desc) [.number, .number] .number :=
      witgen [x, x] do return x
  fail_if_success
    have bad : Program (StructOp desc) [.number] .number :=
      witgen [_x] do return notDeclared
  fail_if_success
    have bad : StructDesc Ty :=
      ⟨"Duplicate", .pair, [("x", .number), ("x", .number)], by decide⟩
  trivial
-- Ambient functions that can manufacture references are not closed inputs either.
/-- error: implicit witgen capture 'ambient'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (ambient : Unit → Var (S := Ty) [.number, .number] .number) :
    Program (StructOp desc) [.number, .number] .pair :=
  witgen [_x, y] do
    let pair ← makeStruct desc .pair h![ambient (), y]
    return pair

-- LEAN-SCOPE-1: exact diagnostics, not failure from an unrelated type mismatch.
abbrev NumberRef := Var (S := Ty) [.number, .number] .number
structure RefBox where
  ref : NumberRef

/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (r : Unit → NumberRef) : Program (StructOp desc) [.number, .number] .pair :=
  witgen [_x, y] do
    let pair ← makeStruct desc .pair h![r (), y]
    return pair

/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (r : RefBox) : Program (StructOp desc) [.number, .number] .pair :=
  witgen [_x, y] do
    let pair ← makeStruct desc .pair h![r.ref, y]
    return pair

-- Unknown carriers must not be accepted just because their fields are invisible.
/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example {Carrier : Type} (r : Carrier) : Program (StructOp desc) [.number] .number :=
  witgen [x] do
    return (fun (_ : Carrier) => x) r

-- Even a static-result function parameter is outside the closed-data interface.
/-- error: implicit witgen capture 'f'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (f : Unit → Nat) : Program (StructOp desc) [.number] .number :=
  witgen [x] do
    return (fun (_ : Nat) => x) (f ())

-- A genuine capability is not a universal certificate for its payload family.
abbrev UnitSig : Signature Ty := fun _ _ _ => Unit
abbrev RefSig : Signature Ty := fun _ _ _ => NumberRef
/-- error: implicit witgen capture 'cap'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (cap : Has UnitSig RefSig) : Program (StructOp desc) [.number] .number :=
  witgen [x] do
    return (fun (_ : Has UnitSig RefSig) => x) cap
-- Has capabilities may be supplied to global Step/Program constructors, not
-- inspected as ambient data. Otherwise an opaque operation result could be
-- decoded through arbitrary host-language casts before becoming a reference.
/-- error: implicit witgen capture 'cap'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example {F : Signature Ty} [cap : Has UnitSig F] :
    Program (StructOp desc) [.number] .number :=
  witgen [x] do
    return (fun (_ : F [] [] .number) => x) (cap.inject ())

-- No blanket exemption for typeclasses or proof parameters.
class RefClass where
  ref : NumberRef
/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example [r : RefClass] : Program (StructOp desc) [.number, .number] .pair :=
  witgen [_x, y] do
    let pair ← makeStruct desc .pair h![r.ref, y]
    return pair

/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
noncomputable example (r : Nonempty NumberRef) :
    Program (StructOp desc) [.number, .number] .pair :=
  witgen [_x, y] do
    let pair ← makeStruct desc .pair h![Classical.choice r, y]
    return pair

/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
noncomputable example (r : ∃ _ : NumberRef, True) :
    Program (StructOp desc) [.number, .number] .pair :=
  witgen [_x, y] do
    let pair ← makeStruct desc .pair h![Classical.choose r, y]
    return pair

-- Static types do not excuse provenance in their let values or type indices.
/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (r : NumberRef) : Program (StructOp desc) [.number] .number :=
  let n := r.index
  witgen [x] do return (fun (_ : Nat) => x) n

/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (r : NumberRef) (n : Fin (r.index + 1)) :
    Program (StructOp desc) [.number] .number :=
  witgen [x] do return (fun (_ : Nat) => x) n.val
-- Instantiated tactic holes in local definitions must also be traversed.
/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (r : NumberRef) : Program (StructOp desc) [.number] .number := by
  let n : Nat := ?value
  case value => exact r.index
  exact witgen [x] do return (fun (_ : Nat) => x) n

-- Future assignments cannot introduce dependencies after closure checking.
/-- error: unresolved witgen term; solve holes before entering the closed block -/
#guard_msgs in
example (r : NumberRef) : Program (StructOp desc) [.number, .number] .number := by
  refine witgen [_x, _y] do return ?_
  all_goals exact r

/-- error: unresolved witgen dependency 'n'; solve holes before entering the closed block -/
#guard_msgs in
example (r : NumberRef) : Program (StructOp desc) [.number] .number := by
  let n : Nat := ?value
  exact witgen [x] do return (fun (_ : Nat) => x) n
  all_goals exact r.index
end Witgen.AuthoringTests
