import Witgen.Examples.RSA4096.Compare
import Witgen.Examples.RSA4096.Arithmetic

namespace Witgen.Examples.RSA4096
open Typed

/-- Full auxiliary layout for zk.golf submission aa9cb03a-4312-476d-8ed8-761f781f6a86.
    Inputs are the fixed big-endian public byte strings packed into Nat.
    The digest is SHA-256's output, not a message to hash. -/
def witnessProgram {F : Signature Ty} [Has BigNumOp F] [Has ValueOp F]
    [Has VectorOp F] [Has (FieldOp bn254Fr) F] [Has (FieldBridgeOp bn254Fr) F]
    [Has (BranchOp .bool) F] : Program F [.nat, .nat, .nat] Scalars :=
  witgen [modulus, signature, digest] do
    let comparison ← vector.Apply h![modulus, signature] comparatorWitness
    let arithmetic ← vector.Apply h![modulus, signature, digest] arithmeticWitness
    let cells ← vector.Append comparison arithmetic
    return cells

end Witgen.Examples.RSA4096
