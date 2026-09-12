import Witgen.Crypto.Circuit

namespace Witgen.Crypto

/-- User-defined nested structure example: wrap a witness, access its named
field, and repack. Both operations use the same generic schema feature. -/
def envelopeRecord {F : Signature Ty} [Has (StructOp schemaDesc) F] :
    Program F [.quad, .scalar, .scalar] .envelope :=
  witgen [witness, x, y] do
    let envelope ← makeStruct schemaDesc .envelope h![witness]
    let trace ← getField schemaDesc .envelope "trace" envelope
    let result ← makeStruct schemaDesc .envelope h![trace]
    return result

/-- Compose actual finite programs; no host witness-computation adapter. -/
def envelopeField : Program FieldSig [.scalar, .scalar] .envelope :=
  quadraticField.bind envelopeRecord

def envelopeNat (p : Nat) : Program NatSig [.scalar, .scalar] .envelope :=
  envelopeField.lower (fieldToNat p)

theorem envelopeField_trace {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    (envelopeField.eval (fieldModel hp) (encodeField i)).trace =
      (quadFieldWitgen hp).generate i := rfl

theorem envelopeNat_raw_canonical {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    ((envelopeNat p).eval natModel (encodeNat i)).trace =
      Val.map (t := .quad) Fin.val ((quadFieldWitgen hp).generate i) :=
  congrArg QuadEnvelope.trace (fieldToNat_correct hp envelopeField (encodeField i)).symm

/-- Nested record paths transport the same complete circuit witness without
losing or altering either the internal square or the public output. -/
theorem envelopeNat_raw_buffer {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    encodeRawNat i (((envelopeNat p).eval natModel (encodeNat i)).trace) =
      QuadCircuit.populate (QuadCircuit.initial i) ((quadFieldWitgen hp).generate i) := by
  rw [envelopeNat_raw_canonical hp]
  rfl

theorem envelope_nat_buffer_correct {p : Nat} (hp : 0 < p) (i : QuadInput p) :
    QuadCircuit.Constraints i
      (encodeRawNat i (((envelopeNat p).eval natModel (encodeNat i)).trace)) := by
  rw [envelopeNat_raw_buffer]
  exact quad_field_buffer_correct hp i

/-- Metadata comes from the actual nested descriptor and proved inner layout. -/
def envelopeOutputPaths : List (List String × Nat) :=
  (QuadCircuit.outputPaths.map fun (name, slot) =>
    ([(schemaDesc .envelope).fields[0].1, name], slot))

theorem envelopeOutputPaths_exact : envelopeOutputPaths =
    [(["trace", "square"], 2), (["trace", "output"], 3)] := rfl

end Witgen.Crypto
