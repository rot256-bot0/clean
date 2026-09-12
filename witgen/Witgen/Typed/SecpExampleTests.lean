import Witgen.Typed.SecpExamples
namespace Witgen.Typed.Secp.ExampleTests
open Witgen
example [Fact (modulus secpBase).Prime] (s t : FieldValue secpScalar) :
    mixed.eval mixedModel h![s,t] = mixedSpec s t := mixed_correct s t
end Witgen.Typed.Secp.ExampleTests
