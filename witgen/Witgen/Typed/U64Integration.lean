import Witgen.Typed.Examples
import Witgen.U64.Export

/-! Integration with the separately owned, concrete four-limb method bodies.
This file contains no U64 field arithmetic implementation or host oracle. -/
namespace Witgen.Typed
open Witgen

def anyFieldProgram (f : FieldId) : Program AnyFieldOp [.field f, .field f] (.field f) :=
  (fieldProgram f).mapHandler (AnyFieldOp.field f)

def u64FieldProgram (f : FieldId) :
    Program (Methods.WithCalls U64.U64Op U64.allSigs) [.field f, .field f] (.field f) :=
  U64.compile (anyFieldProgram f) (by rfl)

/-- Raw U64 decoding agrees exactly with the Fin result, without output normalization. -/
theorem u64FieldProgram_correct (f : FieldId) (a b : FieldValue f)
    (aw bw : U64.Word4) (ha : aw.decode = a.val) (hb : bw.decode = b.val) :
    ((u64FieldProgram f).eval (U64.allLibrary.model U64.primitive) h![aw,bw]).decode =
      ((fieldProgram f).eval (fieldModel f) h![a,b]).val := by
  exact U64.caller_correct (anyFieldProgram f) (u64FieldProgram f)
    (U64.compile_accepted _ _) h![a,b] h![aw,bw] ⟨ha,hb,trivial⟩

open Lean Methods in
def u64FieldProgramJson (f : FieldId) : Except String Json :=
  moduleJson typeJson U64.codec U64.allLibrary
    ("field_" ++ toString f.val ++ "_u64_methods") ["a", "b"] (u64FieldProgram f)

end Witgen.Typed
