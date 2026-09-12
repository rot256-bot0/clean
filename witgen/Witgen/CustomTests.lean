import Witgen.Custom

namespace Witgen.CustomTests
open Custom

example : (splitProgram 256).eval nativeModel h![1000] = (⟨232, 3⟩ : SplitWitness) := rfl
example : ((splitProgram 256).lower lowerSplit).eval targetModel h![1000] = h![232, 3] := rfl
example : (Custom.exportSplit 256).isOk = true := rfl

#eval (show IO Unit from do
  for base in [2, 17, 256, 65536] do
    for x in [0, 1, 16, 1000, 65537, 2^128 + 19] do
      let native := (splitProgram base).eval nativeModel h![x]
      let structural := ((splitProgram base).lower lowerSplit).eval targetModel h![x]
      match structural with
      | .cons lo (.cons hi .nil) =>
        unless lo == native.low && hi == native.high && lo + base * hi == x do
          throw (IO.userError "custom-to-structure lowering disagrees")
  IO.println "custom SplitWitness: 24 source/structural/reconstruction checks passed")
end Witgen.CustomTests
