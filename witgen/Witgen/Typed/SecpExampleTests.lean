import Witgen.Typed.SecpExamples
namespace Witgen.Typed.Secp.ExampleTests
open Witgen

example [Fact (modulus secpBase).Prime] (s t : FieldValue secpScalar) (b : FieldValue secpBase) :
    (mixed.eval model h![s, t, b]).val = mixedSpec s t b := mixed_correct s t b

end Witgen.Typed.Secp.ExampleTests
