import Witgen.Typed.Export
import Witgen.Typed.MethodTests

namespace Witgen.Typed.ExportTests
open Witgen Methods Lean

def codec : OpCodec MethodTests.Prim := fun .add =>
  Json.mkObj [("op", .str "nat.add"), ("static", Json.mkObj [])]

#guard (typeJson (.field secpBase)).compress != (typeJson (.field secpScalar)).compress
#guard (libraryJson typeJson codec MethodTests.lib).size == 1
#guard ((programJson typeJson (withCallsCodec codec) MethodTests.caller).getObjValAs?
  String "op").toOption == some "method.call"

end Witgen.Typed.ExportTests
