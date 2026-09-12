import Witgen.Branching.Programs

namespace Witgen.Branching.ProgramTests
open Typed
example (f : FieldId) (a b : FieldValue f) :
    (conditional (F := Feature f) f).eval (model f) h![true,a,b] = Residue.mul a b := rfl
example (f : FieldId) (a b : FieldValue f) :
    (conditional (F := Feature f) f).eval (model f) h![false,a,b] = Residue.add a b := rfl
example (f : FieldId) (a : FieldValue f) :
    (matchFallback (F := Feature f) f).eval (model f) h![none,a] = Residue.neg a := rfl
example (f : FieldId) (a b : FieldValue f) :
    (matchFallback (F := Feature f) f).eval (model f) h![some a,b] = Residue.inv a := rfl
end Witgen.Branching.ProgramTests
