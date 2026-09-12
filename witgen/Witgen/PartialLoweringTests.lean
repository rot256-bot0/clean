import Witgen.PartialLowering

namespace Witgen.PartialLoweringTests
inductive Op : Signature Unit where
  | keep : Op [()] [] ()
  | reject : Op [()] [] ()
  | nested : Op [()] [⟨[()], ()⟩] ()
abbrev Val (_ : Unit) := Nat

def model : Model Op Val where
  eval := fun op args regions => match op, args, regions with
    | .keep, .cons n .nil, .nil => n
    | .reject, .cons n .nil, .nil => n
    | .nested, .cons n .nil, .cons body .nil => body (.cons n .nil)

def handler : PartialHandler Op Op
  | _, _, _, .keep => some .keep
  | _, _, _, .reject => none
  | _, _, _, .nested => some .nested

def accepted : Program Op [()] () := .let_ .keep (.cons .zero .nil) .nil (.ret .zero)
def rejected : Program Op [()] () := .let_ .reject (.cons .zero .nil) .nil (.ret .zero)
def badRegion : Program Op [()] () :=
  .let_ .nested (.cons .zero .nil) (.cons rejected .nil) (.ret .zero)

example : accepted.mapHandler? handler = some accepted := rfl
example : rejected.mapHandler? handler = none := rfl
example : badRegion.mapHandler? handler = none := rfl
#check Program.eval_mapHandler?_related

end Witgen.PartialLoweringTests
