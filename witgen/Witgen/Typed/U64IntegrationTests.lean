import Witgen.Typed.U64Integration
namespace Witgen.Typed.U64IntegrationTests
open Witgen

#guard [bn254Fr, secpBase, secpScalar].all (fun f =>
  ((u64FieldProgram f).eval (U64.allLibrary.model U64.primitive)
    h![U64.Word4.encode 3, U64.Word4.encode 4]).decode == 41)
#guard [bn254Fr, secpBase, secpScalar].all (fun f =>
  ((u64FieldProgram f).eval (U64.allLibrary.model U64.primitive)
    h![U64.Word4.encode (modulus f - 1), U64.Word4.encode (modulus f - 1)]).decode == 4)

#guard (u64FieldProgramJson secpScalar).toOption.isSome

end Witgen.Typed.U64IntegrationTests
