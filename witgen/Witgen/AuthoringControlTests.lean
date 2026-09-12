import Witgen.Demo

namespace Witgen.AuthoringControlTests
open Demo Arithmetic

/-- Same-sorted references, repeated binds, an alias, shadowed names in closed
regions, and a branch result reused alongside older captures. -/
def branchReuse : Program FieldSig [.bool, .scalar, .scalar] .scalar :=
  witgen [flag, x, c] do
    let old := x
    let twice ← fieldAdd x x
    let picked ← call (Control.branch [.scalar, .scalar] .scalar) h![flag, twice, c]
      regions![(witgen [x, c] do
        let result ← fieldAdd x c
        return result),
        (witgen [x, c] do
          let result ← fieldMul x c
          return result)]
    let shifted ← fieldAdd picked old
    let final ← fieldAdd shifted c
    return final

theorem branchReuse_eval (flag : Bool) (x c : Field17) :
    branchReuse.eval fieldModel h![flag, x, c] =
      Field17.add (Field17.add
        (if flag then Field17.add (Field17.add x x) c
         else Field17.mul (Field17.add x x) c) x) c := by
  cases flag <;> rfl

example : branchReuse.eval fieldModel h![true, 3, 4] = 0 := rfl
example : branchReuse.eval fieldModel h![false, 3, 4] = 14 := rfl

-- The outer/inner contexts are definitionally identical, but captures are reordered.
-- Outer x is index 1; inner index 1 denotes c. Rejection must be from the guard.
/-- error: implicit witgen capture 'x'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example : Program FieldSig [.bool, .scalar, .scalar] .scalar :=
  witgen [flag, x, c] do
    let result ← call (Control.branch [.bool, .scalar, .scalar] .scalar) h![flag, flag, c, x]
      regions![(witgen [_flag, _c, _x] do return x),
        (witgen [_flag, _c, x] do return x)]
    return result

abbrev ScalarRef := Var (S := Ty) [.bool, .scalar, .scalar] .scalar
structure RefBox where
  ref : ScalarRef

/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (r : Unit → ScalarRef) : Program FieldSig [.bool, .scalar, .scalar] .scalar :=
  witgen [flag, x, c] do
    let result ← call (Control.branch [.bool, .scalar, .scalar] .scalar) h![flag, flag, c, x]
      regions![(witgen [_flag, _c, _x] do return r ()),
        (witgen [_flag, _c, x] do return x)]
    return result

/-- error: implicit witgen capture 'r'; declare it as a region input and pass it explicitly -/
#guard_msgs in
example (r : RefBox) : Program FieldSig [.bool, .scalar, .scalar] .scalar :=
  witgen [flag, x, c] do
    let result ← call (Control.branch [.bool, .scalar, .scalar] .scalar) h![flag, flag, c, x]
      regions![(witgen [_flag, _c, _x] do return r.ref),
        (witgen [_flag, _c, x] do return x)]
    return result

-- Explicit named inputs retain x across the very same reordering.
def explicitReordering : Program FieldSig [.bool, .scalar, .scalar] .scalar :=
  witgen [flag, x, c] do
    let result ← call (Control.branch [.bool, .scalar, .scalar] .scalar) h![flag, flag, c, x]
      regions![(witgen [_flag, _c, x] do return x),
        (witgen [_flag, _c, x] do return x)]
    return result
example : explicitReordering.eval fieldModel h![true, 3, 8] = 3 := rfl
example : explicitReordering.eval fieldModel h![false, 3, 8] = 3 := rfl

#eval (show IO Unit from do
  for flag in [false, true] do
    for x in List.range 17 do
      for c in List.range 17 do
        let fx := Field17.ofNat x
        let fc := Field17.ofNat c
        let actual := branchReuse.eval fieldModel h![flag, fx, fc]
        let picked := if flag then Field17.add (Field17.add fx fx) fc
          else Field17.mul (Field17.add fx fx) fc
        unless actual == Field17.add (Field17.add picked fx) fc do
          throw (IO.userError "named branch/capture scoping regression")
  IO.println "named authoring: 578 branch/alias/capture evaluations passed")
end Witgen.AuthoringControlTests
