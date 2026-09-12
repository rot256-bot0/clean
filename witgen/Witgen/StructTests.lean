import Witgen.Structs

namespace Witgen.StructTests
inductive Ty where | number | pair deriving DecidableEq
inductive Schema where | pair

@[reducible] def desc : Schema → StructDesc Ty
  | .pair => ⟨"Pair", .pair, [("left", .number), ("right", .number)], by decide⟩
@[reducible] def V : Ty → Type
  | .number => Nat
  | .pair => Nat × Nat

@[reducible] def repr : (k : Schema) → StructRepr V (desc k)
  | .pair => {
    pack := fun | .cons x (.cons y .nil) => (x, y)
    unpack := fun (x, y) => .cons x (.cons y .nil)
    unpack_pack := by intro xs; cases xs with | cons x xs => cases xs with | cons y xs => cases xs; rfl
    pack_unpack := by intro x; cases x; rfl }

example : (structModel repr).eval (.make .pair) (.cons 3 (.cons 8 .nil)) .nil = (3, 8) := rfl
example : (structModel repr).eval
    (.get .pair (NamedField.ref (fields := (desc .pair).fields) (name := "right") (t := .number)))
    (.cons (3, 8) .nil) .nil = 8 := rfl
example (xs : HList V (desc .pair).sorts) :
    (repr .pair).unpack ((repr .pair).pack xs) = xs := (repr .pair).unpack_pack xs
-- Duplicate schema names must be rejected at descriptor construction.
example : (desc .pair).fields.map Prod.fst |>.Nodup := (desc .pair).names_nodup
end Witgen.StructTests
