import Witgen.Examples.RSA4096.Basic

namespace Witgen.Examples.RSA4096
open Witgen.Typed

namespace Compare

variable {F : Signature Ty}

/-- Ninety big-endian six-byte chunks of a 512-byte big-endian Nat, left-padded
with 28 zero bytes. The ABI requires the input to be below `2^4096`. -/
def chunks [Has BigNumOp F] [Has ValueOp F] [Has VectorOp F] :
    Program F [.nat] (.list .nat) :=
  witgen [n] do
    let result ← vector.Tabulate 90 h![n] (witgen [i, n] do
      let last ← bignum.Const 89
      let width ← bignum.Const 48
      let base ← bignum.Const (2^48)
      let position ← bignum.Sub last i
      let shift ← bignum.Mul position width
      let high ← bignum.ShrBy n shift
      let qr ← bignum.DivMod high base
      let chunk ← value.Snd qr
      return chunk)
    return result

/-- Bounded first-difference scan over two 90-chunk vectors. The no-difference
sentinel is 90, so all subsequent group lookups safely use their zero fallback. -/
def firstDifference [Has BigNumOp F] [Has VectorOp F] [Has (BranchOp .bool) F] :
    Program F [.list .nat, .list .nat] .nat :=
  witgen [ns, ss] do
    let sentinel ← bignum.Const 90
    let first ← vector.Fold 90 sentinel h![ns, ss] (witgen [i, first, ns, ss] do
      let limit ← bignum.Const 90
      let found ← bignum.Lt first limit
      let next ← control.If found h![i, first, ns, ss]
        (witgen [_i, first, _ns, _ss] do return first)
        (witgen [i, first, ns, ss] do
          let zero ← bignum.Const 0
          let n ← vector.GetD ns i zero
          let s ← vector.GetD ss i zero
          let ns ← bignum.Sub n s
          let sn ← bignum.Sub s n
          let difference ← bignum.Add ns sn
          let differs ← bignum.Lt zero difference
          let next ← control.If differs h![i, first]
            (witgen [i, _first] do return i)
            (witgen [_i, first] do return first)
          return next)
      return next)
    return first

/-- Field Horner prefixes and successive products, using explicit limb captures. -/
private def prefixProducts [Has (FieldOp bn254Fr) F] [Has VectorOp F] :
    Program F [Scalar, Scalar, Scalar, Scalar, Scalar] Scalars :=
  witgen [dv, x0, x1, x2, x3] do
    let one ← field.Const bn254Fr 1
    let base ← field.Const bn254Fr (2^48)
    let delta ← field.Add dv one
    let l0 ← field.Sub x0 delta
    let h ← field.Mul base x0
    let h ← field.Add h x1
    let l ← field.Sub h delta
    let p ← field.Mul l0 l
    let cells ← vector.Singleton p
    let h ← field.Mul base h
    let h ← field.Add h x2
    let l ← field.Sub h delta
    let p ← field.Mul p l
    let next ← vector.Singleton p
    let cells ← vector.Append cells next
    let h ← field.Mul base h
    let h ← field.Add h x3
    let l ← field.Sub h delta
    let p ← field.Mul p l
    let next ← vector.Singleton p
    let cells ← vector.Append cells next
    return cells

/-- Three allocated product-chain cells. Horner packing is in the field, so
negative extraction limbs retain the source's signed field semantics. The fifth
prefix is only an assertion expression in the source, not another witness cell. -/
def productCells [Has BigNumOp F] [Has (FieldOp bn254Fr) F] [Has VectorOp F] :
    Program F [Scalar, Scalars] Scalars :=
  witgen [dv, xs] do
    let zero ← field.Const bn254Fr 0
    let i ← bignum.Const 0
    let x0 ← vector.GetD xs i zero
    let i ← bignum.Const 1
    let x1 ← vector.GetD xs i zero
    let i ← bignum.Const 2
    let x2 ← vector.GetD xs i zero
    let i ← bignum.Const 3
    let x3 ← vector.GetD xs i zero
    let result ← vector.Apply h![dv, x0, x1, x2, x3] prefixProducts
    return result

end Compare

/-- Exact first 73 local witness cells of winning `LessThanBytes65.main`.

Inputs are `[modulus, signature]`, each the Nat value of a 512-byte big-endian
byte string (caller bound `< 2^4096`). Output order is 17 prefix flags, delta-minus-1,
5 signed field differences, 3 products, 47 low delta bits. There are no allocated
selector bits or implicit range-check top bit. All witness math is finite typed AST.

This is a total generator, not a validator: equal inputs use the original zero
`delta-minus-1` and zero-extraction fallback, and `signature ≥ modulus` may produce an unsatisfying
witness. No RSA-validity, modulus-width, or ordering assumption is concealed or
proved here. Correspondence is executable SOURCE_REVIEWED evidence, not a theorem
binding this DSL to the original Lean circuit. -/
def comparatorWitness {F : Signature Ty}
    [Has BigNumOp F] [Has ValueOp F] [Has VectorOp F]
    [Has (FieldOp bn254Fr) F] [Has (FieldBridgeOp bn254Fr) F]
    [Has (BranchOp .bool) F] : Program F [.nat, .nat] Scalars :=
  witgen [modulus, signature] do
    let ns ← vector.Apply h![modulus] Compare.chunks
    let ss ← vector.Apply h![signature] Compare.chunks
    let first ← vector.Apply h![ns, ss] Compare.firstDifference
    let flags ← vector.Tabulate 17 h![first] (witgen [g, first] do
      let one ← bignum.Const 1
      let five ← bignum.Const 5
      let next ← bignum.Add g one
      let endPrefix ← bignum.Mul five next
      let different ← bignum.Lt first endPrefix
      let flag ← control.If different h![]
        (witgen [] do
          let zero ← field.Const bn254Fr 0
          return zero)
        (witgen [] do
          let one ← field.Const bn254Fr 1
          return one)
      return flag)
    let zero ← bignum.Const 0
    let one ← bignum.Const 1
    let five ← bignum.Const 5
    let n ← vector.GetD ns first zero
    let s ← vector.GetD ss first zero
    let difference ← bignum.Sub n s
    let dv ← bignum.Sub difference one
    let dvf ← field.FromNat bn254Fr dv
    let deltaCells ← vector.Singleton dvf
    let groupQR ← bignum.DivMod first five
    let group ← value.Fst groupQR
    let start ← bignum.Mul group five
    let xs ← vector.Tabulate 5 h![ns, ss, start] (witgen [i, ns, ss, start] do
      let zero ← bignum.Const 0
      let j ← bignum.Add start i
      let n ← vector.GetD ns j zero
      let s ← vector.GetD ss j zero
      let nf ← field.FromNat bn254Fr n
      let sf ← field.FromNat bn254Fr s
      let x ← field.Sub nf sf
      return x)
    let products ← vector.Apply h![dvf, xs] Compare.productCells
    let canonical ← field.ToNat dvf
    let bits ← vector.Tabulate 47 h![canonical] (witgen [i, canonical] do
      let two ← bignum.Const 2
      let shifted ← bignum.ShrBy canonical i
      let qr ← bignum.DivMod shifted two
      let bit ← value.Snd qr
      let bf ← field.FromNat bn254Fr bit
      return bf)
    let a ← vector.Append flags deltaCells
    let b ← vector.Append a xs
    let c ← vector.Append b products
    let result ← vector.Append c bits
    return result

end Witgen.Examples.RSA4096
