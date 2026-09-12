import Witgen.Typed.AffineExamples
namespace Witgen.Typed.Secp.AffineExampleTests
open Witgen
example [Fact (modulus secpBase).Prime] :
    generatorRoundtrip.eval affineModel .nil = some generator := generatorRoundtrip_correct
example [Fact (modulus secpBase).Prime] :
    invalidPair.eval affineModel h![(Residue.ofNat (modulus_pos secpBase) 0,
      Residue.ofNat (modulus_pos secpBase) 0)] = none := invalidPair_rejects_zero
example [Fact (modulus secpBase).Prime] :
    roundtripProgram.eval affineModel h![(0 : Point)] = none := rfl
end Witgen.Typed.Secp.AffineExampleTests
