import Witgen.Typed.SecpFeature

namespace Witgen.Typed.Secp
open Witgen

/-- Both field identities are inferred at every nonconstant operation. The base
arithmetic consumes a coordinate of an actual computed point. -/
def mixed : Program Feature [.field secpScalar, .field secpScalar, .field secpBase]
    (.field secpBase) :=
  witgen [s, t, b] do
    let ss ← field.Square s
    let st ← field.Mul ss t
    let alpha ← field.Add st s
    let g ← secp.Generator
    let p ← secp.Scale alpha g
    let minusG ← secp.Inv g
    let q ← secp.Add p minusG
    let x ← secp.X q
    let gx ← secp.X g
    let bb ← field.Square b
    let bx ← field.Mul bb x
    let output ← field.Add bx gx
    return output

/-- Arithmetic/group specification independent of the Program evaluator. Scalars
are canonical representatives, and xCoord(0)=0 is the documented total view. -/
def mixedSpec [Fact (modulus secpBase).Prime]
    (s t : FieldValue secpScalar) (b : FieldValue secpBase) : Nat :=
  let n := modulus secpScalar
  let p := modulus secpBase
  let k := ((s.val ^ 2 % n * t.val) % n + s.val) % n
  (((b.val ^ 2 % p) * (xCoord (k • generator + -generator)).val) % p +
    (xCoord generator).val) % p

theorem mixed_correct [Fact (modulus secpBase).Prime]
    (s t : FieldValue secpScalar) (b : FieldValue secpBase) :
    (mixed.eval model h![s, t, b]).val = mixedSpec s t b := rfl

/-- Proof-model check: the actual point calculation at s=t=1 is 2G-G=G. -/
theorem mixed_one_one [Fact (modulus secpBase).Prime] (b : FieldValue secpBase) :
    (mixed.eval model h![Residue.ofNat (modulus_pos secpScalar) 1,
      Residue.ofNat (modulus_pos secpScalar) 1, b]).val =
      ((b.val ^ 2 % modulus secpBase * generatorX) % modulus secpBase + generatorX) %
        modulus secpBase := by
  rw [mixed_correct]
  change ((b.val ^ 2 % modulus secpBase * (xCoord ((2 : Nat) • generator + -generator)).val) %
    modulus secpBase + generatorX) % modulus secpBase = _
  rw [two_nsmul, add_neg_cancel_right]
  rfl

open Lean Methods in
def mixedJson : Except String Json :=
  moduleJson typeJson codec .nil "secp_mixed_fields" ["s", "t", "b"]
    (mixed.mapHandler Sum.inl)

end Witgen.Typed.Secp
