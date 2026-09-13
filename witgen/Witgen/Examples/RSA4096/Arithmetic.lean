import Witgen.Examples.RSA4096.Basic
import Witgen.Examples.RSA4096.Tables

namespace Witgen.Examples.RSA4096
open Witgen.Typed

/-- The winner's byte-centered shift, NOT a half-radix limb shift. -/
def sigma : Nat := ((List.range 510).map (fun j => 2^(8*j+7))).sum + 2^4095

variable {F : Signature Ty} [Has BigNumOp F] [Has ValueOp F] [Has VectorOp F]
  [Has (FieldOp bn254Fr) F] [Has (FieldBridgeOp bn254Fr) F] [Has (BranchOp .bool) F]

/-- Fixed little-endian radix limbs, with explicit Nat-to-field conversion. -/
def limbFields (bits count : Nat) : Program F [.nat] Scalars :=
  witgen [x] do
    let out ← vector.Tabulate count h![x] (witgen [i, x] do
      let width ← bignum.Const bits
      let shift ← bignum.Mul i width
      let shifted ← bignum.ShrBy x shift
      let radix ← bignum.Const (2^bits)
      let qr ← bignum.DivMod shifted radix
      let low ← value.Snd qr
      let cell ← field.FromNat bn254Fr low
      return cell)
    return out

/-- A width-w range check allocates only its w-1 LOW bits. -/
def lowBits (width : Nat) : Program F [Scalar] Scalars :=
  witgen [x] do
    let n ← field.ToNat x
    let out ← vector.Tabulate (width-1) h![n] (witgen [i, n] do
      let shifted ← bignum.ShrBy n i
      let two ← bignum.Const 2
      let qr ← bignum.DivMod shifted two
      let bit ← value.Snd qr
      let cell ← field.FromNat bn254Fr bit
      return cell)
    return out

/-- Normalization emits low bits per limb, not the implicit high expressions. -/
def normalizeLimbs (bits count top : Nat) : Program F [Scalars] Scalars :=
  witgen [xs] do
    let blocks ← vector.Tabulate (count-1) h![xs] (witgen [i, xs] do
      let zero ← field.Const bn254Fr 0
      let x ← vector.GetD xs i zero
      let block ← vector.Apply h![x] (lowBits bits)
      return block)
    let lows ← vector.Flatten blocks
    let last ← bignum.Const (count-1)
    let zero ← field.Const bn254Fr 0
    let high ← vector.GetD xs last zero
    let highBits ← vector.Apply h![high] (lowBits top)
    let out ← vector.Append lows highBits
    return out

/-- Horner evaluation of a fixed-size coefficient segment at radix 2^bits. -/
def segment (bits count : Nat) : Program F [Scalars, .nat] Scalar :=
  witgen [xs, start] do
    let zero ← field.Const bn254Fr 0
    let out ← vector.Fold count zero h![xs, start] (witgen [i, acc, xs, start] do
      let last ← bignum.Const (count-1)
      let reverse ← bignum.Sub last i
      let index ← bignum.Add start reverse
      let zero ← field.Const bn254Fr 0
      let x ← vector.GetD xs index zero
      let radix ← field.Const bn254Fr (2^bits)
      let shifted ← field.Mul acc radix
      let next ← field.Add shifted x
      return next)
    return out

/-- Finite coefficient convolution. Negative indices are excluded by a finite branch. -/
def convolution (leftCount outCount : Nat) : Program F [Scalars, Scalars] Scalars :=
  witgen [a, b] do
    let out ← vector.Tabulate outCount h![a, b] (witgen [k, a, b] do
      let zero ← field.Const bn254Fr 0
      let coefficient ← vector.Fold leftCount zero h![k, a, b] (witgen [i, acc, k, a, b] do
        let outside ← bignum.Lt k i
        let next ← control.If outside h![i, acc, k, a, b]
          (witgen [_i, acc, _k, _a, _b] do return acc)
          (witgen [i, acc, k, a, b] do
            let j ← bignum.Sub k i
            let zero ← field.Const bn254Fr 0
            let x ← vector.GetD a i zero
            let y ← vector.GetD b j zero
            let xy ← field.Mul x y
            let next ← field.Add acc xy
            return next)
        return next)
      return coefficient)
    return out

/-- Subtract the same integer shift coefficientwise at either radix. -/
def shiftLimbs (bits count : Nat) : Program F [Scalars] Scalars :=
  witgen [xs] do
    let shift ← bignum.Const sigma
    let ds ← vector.Apply h![shift] (limbFields bits count)
    let out ← vector.Tabulate count h![xs, ds] (witgen [i, xs, ds] do
      let zero ← field.Const bn254Fr 0
      let x ← vector.GetD xs i zero
      let d ← vector.GetD ds i zero
      let shifted ← field.Sub x d
      return shifted)
    return out

/-- Nine radix-scaled lane evaluations at one public interpolation point. -/
def windowHs : Program F [Scalars, Scalar] Scalars :=
  witgen [a, c] do
    let hs ← vector.Tabulate 9 h![a, c] (witgen [i, a, c] do
      let zero ← field.Const bn254Fr 0
      let h ← vector.Fold 19 zero h![a, c, i] (witgen [u, acc, a, c, i] do
        let last ← bignum.Const 18
        let rev ← bignum.Sub last u
        let nine ← bignum.Const 9
        let base ← bignum.Mul rev nine
        let index ← bignum.Add base i
        let zero ← field.Const bn254Fr 0
        let x ← vector.GetD a index zero
        let cx ← field.Mul acc c
        let next ← field.Add cx x
        return next)
      let powers ← vector.Nats ((List.range 9).map (fun j => 2^(24*j)))
      let zero ← bignum.Const 0
      let power ← vector.GetD powers i zero
      let scale ← field.FromNat bn254Fr power
      let out ← field.Mul scale h
      return out)
    return hs

/-- The four source formulas; j is static AST construction data. -/
def windowProduct (j : Nat) : Program F [Scalars] Scalar :=
  if j < 3 then
    witgen [hs] do
      let zero ← field.Const bn254Fr 0
      let index ← bignum.Const (8-j)
      let h ← vector.GetD hs index zero
      let start ← bignum.Const (j+1)
      let sum ← vector.Apply h![hs, start] (segment 0 (3-j))
      let two ← field.Const bn254Fr 2
      let twice ← field.Mul two h
      let out ← field.Mul twice sum
      return out
  else
    witgen [hs] do
      let start ← bignum.Const 5
      let a5 ← vector.Apply h![hs, start] (segment 0 4)
      let i4 ← bignum.Const 4
      let zero ← field.Const bn254Fr 0
      let h4 ← vector.GetD hs i4 zero
      let a4 ← field.Add h4 a5
      let two ← field.Const bn254Fr 2
      let twice ← field.Mul two a4
      let term ← field.Sub twice a5
      let out ← field.Mul a5 term
      return out

/-- WindowSquare's four products, point-major; no implicit point-38 cells. -/
def windowProducts : Program F [Scalars] Scalars :=
  witgen [a] do
    let blocks ← vector.Tabulate 37 h![a] (witgen [point, a] do
      let one ← bignum.Const 1
      let cn ← bignum.Add point one
      let c ← field.FromNat bn254Fr cn
      let hs ← vector.Apply h![a, c] windowHs
      let p0 ← vector.Apply h![hs] (windowProduct 0)
      let p1 ← vector.Apply h![hs] (windowProduct 1)
      let p2 ← vector.Apply h![hs] (windowProduct 2)
      let p3 ← vector.Apply h![hs] (windowProduct 3)
      let s0 ← vector.Singleton p0
      let s1 ← vector.Singleton p1
      let s2 ← vector.Singleton p2
      let s3 ← vector.Singleton p3
      let s01 ← vector.Append s0 s1
      let s23 ← vector.Append s2 s3
      let out ← vector.Append s01 s23
      return out)
    let out ← vector.Flatten blocks
    return out

/-- Returns sparse Pc and its 38+148 allocated cells. Pc is NOT the dense convolution. -/
def windowWitness : Program F [Scalars] (.pair Scalars Scalars) :=
  witgen [a] do
    let full ← vector.Apply h![a, a] (convolution 171 341)
    let sums ← vector.Tabulate 38 h![full] (witgen [w, full] do
      let nine ← bignum.Const 9
      let start ← bignum.Mul w nine
      let group ← vector.Apply h![full, start] (segment 24 9)
      return group)
    let products ← vector.Apply h![a] windowProducts
    let cells ← vector.Append sums products
    let pc ← vector.Tabulate 341 h![sums] (witgen [k, sums] do
      let nine ← bignum.Const 9
      let qr ← bignum.DivMod k nine
      let w ← value.Fst qr
      let rem ← value.Snd qr
      let one ← bignum.Const 1
      let isStart ← bignum.Lt rem one
      let x ← control.If isStart h![sums, w]
        (witgen [sums, w] do
          let zero ← field.Const bn254Fr 0
          let x ← vector.GetD sums w zero
          return x)
        (witgen [_sums, _w] do
          let zero ← field.Const bn254Fr 0
          return zero)
      return x)
    let out ← value.Pair pc cells
    return out

/-- Append the affine implicit top coefficient: field division, never a witness cell. -/
def withTop (bits count : Nat) : Program F [Scalars, Scalars] Scalars :=
  witgen [lhs, rhsLow] do
    let zero ← bignum.Const 0
    let left ← vector.Apply h![lhs, zero] (segment bits count)
    let right ← vector.Apply h![rhsLow, zero] (segment bits (count-1))
    let delta ← field.Sub left right
    let power ← field.Const bn254Fr (2^(bits*(count-1)))
    let inverse ← field.Inv power
    let top ← field.Mul delta inverse
    let last ← vector.Singleton top
    let out ← vector.Append rhsLow last
    return out

/-- Exact final active grouping; the final proof-table tail is not traversed. -/
def finalGroupSize (k : Nat) : Nat :=
  if k == 0 then 9 else if k < 10 then 13 else if k < 52 then 12 else 13

/-- A runtime width under a static cap. Empty blocks beyond width-1 are NOT cells. -/
def lowBitsBounded (maxWidth : Nat) : Program F [.nat, Scalar] Scalars :=
  witgen [width, x] do
    let n ← field.ToNat x
    let one ← bignum.Const 1
    let allocated ← bignum.Sub width one
    let blocks ← vector.Tabulate (maxWidth-1) h![allocated, n] (witgen [i, allocated, n] do
      let inRange ← bignum.Lt i allocated
      let block ← control.If inRange h![i, n]
        (witgen [i, n] do
          let shifted ← bignum.ShrBy n i
          let two ← bignum.Const 2
          let qr ← bignum.DivMod shifted two
          let bit ← value.Snd qr
          let cell ← field.FromNat bn254Fr bit
          let block ← vector.Singleton cell
          return block)
        (witgen [_i, _n] do
          let empty ← vector.Empty Scalar
          return empty)
      return block)
    let out ← vector.Flatten blocks
    return out

/-- Square carry recurrence in FIELD arithmetic, before the negative-side offset. -/
def squareCarryValue : Program F [Scalars, Scalars, .nat, Scalar] Scalar :=
  witgen [lhs, rhs, k, signed] do
    let nine ← bignum.Const 9
    let start ← bignum.Mul k nine
    let left ← vector.Apply h![lhs, start] (segment 24 9)
    let right ← vector.Apply h![rhs, start] (segment 24 9)
    let delta ← field.Sub left right
    let numerator ← field.Add signed delta
    let power ← field.Const bn254Fr (2^216)
    let inverse ← field.Inv power
    let carry ← field.Mul numerator inverse
    return carry

/-- Table-indexed canonical carry low bits. -/
def squareCarryBits (first : Bool) : Program F [.nat, Scalar] Scalars :=
  witgen [k, carry] do
    let offsets ← vector.Nats (if first then Tables.first_offset_negative else Tables.middle_offset_negative)
    let widths ← vector.Nats (if first then Tables.first_widths else Tables.middle_widths)
    let zero ← bignum.Const 0
    let off ← vector.GetD offsets k zero
    let width ← vector.GetD widths k zero
    let offset ← field.FromNat bn254Fr off
    let shifted ← field.Add carry offset
    let bits ← vector.Apply h![width, shifted] (lowBitsBounded 33)
    return bits

/-- Only the 37 active boundaries; carries themselves remain local expressions. -/
def squareCarries (first : Bool) : Program F [Scalars, Scalars] Scalars :=
  witgen [lhs, rhs] do
    let zero ← field.Const bn254Fr 0
    let empty ← vector.Empty Scalar
    let initial ← value.Pair zero empty
    let final ← vector.Fold 37 initial h![lhs, rhs] (witgen [k, acc, lhs, rhs] do
      let signed ← value.Fst acc
      let cells ← value.Snd acc
      let carry ← vector.Apply h![lhs, rhs, k, signed] squareCarryValue
      let bits ← vector.Apply h![k, carry] (squareCarryBits first)
      let all ← vector.Append cells bits
      let out ← value.Pair carry all
      return out)
    let cells ← value.Snd final
    return cells

/-- Exact absolute value of stored-Sigma, computed with two truncated subtractions. -/
def squareMagnitude (first : Bool) : Program F [.nat] .nat :=
  if first then witgen [input] do return input
  else witgen [input] do
    let shift ← bignum.Const sigma
    let positive ← bignum.Sub input shift
    let negative ← bignum.Sub shift input
    let magnitude ← bignum.Add positive negative
    return magnitude

/-- Selected quotient and stored residue; first input unsigned, later inputs shifted. -/
def squareQR (first : Bool) : Program F [.nat, .nat] (.pair .nat .nat) :=
  witgen [n, input] do
    let magnitude ← vector.Apply h![input] (squareMagnitude first)
    let product ← bignum.Square magnitude
    let qr ← bignum.DivMod product n
    let q0 ← value.Fst qr
    let r0 ← value.Snd qr
    let shift ← bignum.Const sigma
    let threshold ← bignum.Const (2^4096-sigma)
    let unadjusted ← bignum.Lt r0 threshold
    let shifted ← bignum.Add r0 shift
    let selected ← control.If unadjusted h![q0, shifted, n]
      (witgen [q0, shifted, _n] do
        let out ← value.Pair q0 shifted
        return out)
      (witgen [q0, shifted, n] do
        let one ← bignum.Const 1
        let q ← bignum.Add q0 one
        let r ← bignum.Sub shifted n
        let out ← value.Pair q r
        return out)
    return selected

/-- q limbs, r limbs, then the two normalization blocks. -/
def squareRange (first : Bool) : Program F [.nat, .nat] (.pair Scalars (.pair Scalars Scalars)) :=
  witgen [qNat, rNat] do
    let q ← vector.Apply h![qNat] (limbFields 24 171)
    let r ← vector.Apply h![rNat] (limbFields 24 171)
    let qrCells ← vector.Append q r
    let qBits ← vector.Apply h![q] (normalizeLimbs 24 171 (if first then 16 else 15))
    let rBits ← vector.Apply h![r] (normalizeLimbs 24 171 16)
    let bits ← vector.Append qBits rBits
    let initial ← vector.Append qrCells bits
    let rc ← value.Pair r initial
    let out ← value.Pair q rc
    return out

/-- Low q*N coefficients, affine top, and table-offset carry bits. -/
def squareTail (first : Bool) : Program F [.nat, Scalars, Scalars, Scalars] Scalars :=
  witgen [n, q, r, pc] do
    let ns ← vector.Apply h![n] (limbFields 24 171)
    let qn ← vector.Apply h![q, ns] (convolution 171 340)
    let signedR ← vector.Apply h![r] (shiftLimbs 24 171)
    let rhsLow ← vector.Tabulate 340 h![qn, signedR] (witgen [k, qn, signedR] do
      let zero ← field.Const bn254Fr 0
      let x ← vector.GetD qn k zero
      let r ← vector.GetD signedR k zero
      let y ← field.Add x r
      return y)
    let rhs ← vector.Apply h![pc, rhsLow] (withTop 24 341)
    let carries ← vector.Apply h![pc, rhs] (squareCarries first)
    let cells ← vector.Append qn carries
    return cells

/-- Unsigned first input or coefficientwise signed middle input. -/
def squareInputFields (first : Bool) : Program F [.nat] Scalars :=
  if first then limbFields 24 171
  else witgen [input] do
    let limbs ← vector.Apply h![input] (limbFields 24 171)
    let shifted ← vector.Apply h![limbs] (shiftLimbs 24 171)
    return shifted

/-- One complete square's stored output and all allocated cells, in source order. -/
def squareWitness (first : Bool) : Program F [.nat, .nat] (.pair .nat Scalars) :=
  witgen [n, input] do
    let qr ← vector.Apply h![n, input] (squareQR first)
    let qNat ← value.Fst qr
    let rNat ← value.Snd qr
    let range ← vector.Apply h![qNat, rNat] (squareRange first)
    let q ← value.Fst range
    let rc ← value.Snd range
    let r ← value.Fst rc
    let initial ← value.Snd rc
    let a ← vector.Apply h![input] (squareInputFields first)
    let win ← vector.Apply h![a] windowWitness
    let pc ← value.Fst win
    let windowCells ← value.Snd win
    let withWindow ← vector.Append initial windowCells
    let tail ← vector.Apply h![n, q, r, pc] (squareTail first)
    let cells ← vector.Append withWindow tail
    let out ← value.Pair rNat cells
    return out

/-- Fifteen reductions: one unsigned square followed by a bounded fourteen-step region. -/
def squaresWitness : Program F [.nat, .nat] (.pair .nat Scalars) :=
  witgen [n, signature] do
    let initial ← vector.Apply h![n, signature] (squareWitness true)
    let out ← vector.Fold 14 initial h![n] (witgen [_i, acc, n] do
      let stored ← value.Fst acc
      let cells ← value.Snd acc
      let next ← vector.Apply h![n, stored] (squareWitness false)
      let residue ← value.Fst next
      let more ← value.Snd next
      let all ← vector.Append cells more
      let out ← value.Pair residue all
      return out)
    return out

/-- Reconstruct implicit high expressions from the ALLOCATED low-bit cells.
    This returns a local expression vector, never additional witness cells. -/
def returnedLimbBits (width : Nat) : Program F [Scalar, Scalars, .nat] Scalars :=
  witgen [limb, lowCells, start] do
    let lows ← vector.Tabulate (width-1) h![lowCells, start] (witgen [i, lowCells, start] do
      let index ← bignum.Add start i
      let zero ← field.Const bn254Fr 0
      let bit ← vector.GetD lowCells index zero
      return bit)
    let zero ← bignum.Const 0
    let sum ← vector.Apply h![lows, zero] (segment 1 (width-1))
    let delta ← field.Sub limb sum
    let power ← field.Const bn254Fr (2^(width-1))
    let inverse ← field.Inv power
    let top ← field.Mul delta inverse
    let last ← vector.Singleton top
    let out ← vector.Append lows last
    return out

/-- Read the last square's residue limbs and low bits from the arithmetic trace;
    preserve the source's implicit-high-bit reconstruction before radix-16 packing. -/
def returnedSquareBits : Program F [Scalars] Scalars :=
  witgen [cells] do
    let last ← vector.Drop (9851+13*9832) cells
    let afterQ ← vector.Drop 171 last
    let r ← vector.Take 171 afterQ
    let afterQBits ← vector.Drop (342+3924) last
    let lowCells ← vector.Take 3925 afterQBits
    let blocks ← vector.Tabulate 170 h![r, lowCells] (witgen [i, r, lowCells] do
      let zero ← field.Const bn254Fr 0
      let limb ← vector.GetD r i zero
      let width ← bignum.Const 23
      let start ← bignum.Mul i width
      let bits ← vector.Apply h![limb, lowCells, start] (returnedLimbBits 24)
      return bits)
    let lows ← vector.Flatten blocks
    let highIndex ← bignum.Const 170
    let zero ← field.Const bn254Fr 0
    let high ← vector.GetD r highIndex zero
    let start ← bignum.Const (170*23)
    let highBits ← vector.Apply h![high, lowCells, start] (returnedLimbBits 16)
    let out ← vector.Append lows highBits
    return out

/-- The source's 4096 returned bit expressions, regrouped into 256 radix-16 limbs. -/
def repackSquareBits : Program F [Scalars] Scalars :=
  witgen [cells] do
    let bits ← vector.Apply h![cells] returnedSquareBits
    let limbs ← vector.Tabulate 256 h![bits] (witgen [k, bits] do
      let sixteen ← bignum.Const 16
      let start ← bignum.Mul k sixteen
      let limb ← vector.Apply h![bits, start] (segment 1 16)
      return limb)
    return limbs

/-- PKCS1-v1_5 SHA-256's fixed 480-byte prefix (digest is NOT included here). -/
def pkcsPrefix : Nat :=
  ([0, 1] ++ List.replicate 458 255 ++ [0] ++
    [48, 49, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 1, 5, 0, 4, 32]).foldl
      (fun acc byte => 256*acc+byte) 0

/-- Complete EM computation stays inside the finite AST; input digest is raw Nat. -/
def encodeDigest : Program F [.nat] .nat :=
  witgen [digest] do
    let fixedBytes ← bignum.Const pkcsPrefix
    let shifted ← bignum.Shl fixedBytes 256
    let em ← bignum.Add shifted digest
    return em

/-- Bounded Horner region for a runtime group length, capped by the fixed schedule. -/
def segmentBounded (bits cap : Nat) : Program F [Scalars, .nat, .nat] Scalar :=
  witgen [xs, start, size] do
    let zero ← field.Const bn254Fr 0
    let out ← vector.Fold cap zero h![xs, start, size] (witgen [i, acc, xs, start, size] do
      let active ← bignum.Lt i size
      let next ← control.If active h![i, acc, xs, start, size]
        (witgen [i, acc, xs, start, size] do
          let one ← bignum.Const 1
          let last ← bignum.Sub size one
          let reverse ← bignum.Sub last i
          let index ← bignum.Add start reverse
          let zero ← field.Const bn254Fr 0
          let x ← vector.GetD xs index zero
          let radix ← field.Const bn254Fr (2^bits)
          let shifted ← field.Mul acc radix
          let next ← field.Add shifted x
          return next)
        (witgen [_i, acc, _xs, _start, _size] do return acc)
      return next)
    return out

/-- Final carry recurrence at the exact prefix-sum position and FIELD divisor. -/
def finalCarryValue : Program F [Scalars, Scalars, .nat, .nat, Scalar] (.pair .nat Scalar) :=
  witgen [lhs, rhs, k, pos, signed] do
    let sizes ← vector.Nats ((List.range 62).map (finalGroupSize))
    let powers ← vector.Nats ((List.range 62).map (fun j => 2^(16*finalGroupSize j)))
    let zero ← bignum.Const 0
    let size ← vector.GetD sizes k zero
    let powerNat ← vector.GetD powers k zero
    let power ← field.FromNat bn254Fr powerNat
    let inverse ← field.Inv power
    let left ← vector.Apply h![lhs, pos, size] (segmentBounded 16 13)
    let right ← vector.Apply h![rhs, pos, size] (segmentBounded 16 13)
    let delta ← field.Sub left right
    let numerator ← field.Add signed delta
    let carry ← field.Mul numerator inverse
    let nextPos ← bignum.Add pos size
    let out ← value.Pair nextPos carry
    return out

/-- Only low width-1 bits after adding VR's negative-side offset. -/
def finalCarryBits : Program F [.nat, Scalar] Scalars :=
  witgen [k, carry] do
    let offsets ← vector.Nats Tables.final_offset_negative
    let widths ← vector.Nats Tables.final_widths
    let zero ← bignum.Const 0
    let off ← vector.GetD offsets k zero
    let width ← vector.GetD widths k zero
    let offset ← field.FromNat bn254Fr off
    let shifted ← field.Add carry offset
    let bits ← vector.Apply h![width, shifted] (lowBitsBounded 47)
    return bits

/-- Sixty-two active carry boundaries; no final equality row/carry cell is invented. -/
def finalCarries : Program F [Scalars, Scalars] Scalars :=
  witgen [lhs, rhs] do
    let zeroNat ← bignum.Const 0
    let zero ← field.Const bn254Fr 0
    let empty ← vector.Empty Scalar
    let signedCells ← value.Pair zero empty
    let initial ← value.Pair zeroNat signedCells
    let final ← vector.Fold 62 initial h![lhs, rhs] (witgen [k, acc, lhs, rhs] do
      let pos ← value.Fst acc
      let signedCells ← value.Snd acc
      let signed ← value.Fst signedCells
      let cells ← value.Snd signedCells
      let next ← vector.Apply h![lhs, rhs, k, pos, signed] finalCarryValue
      let nextPos ← value.Fst next
      let carry ← value.Snd next
      let bits ← vector.Apply h![k, carry] finalCarryBits
      let all ← vector.Append cells bits
      let signedCells ← value.Pair carry all
      let out ← value.Pair nextPos signedCells
      return out)
    let signedCells ← value.Snd final
    let cells ← value.Snd signedCells
    return cells

/-- One fused quotient, 512 limbs and 7679 normalization bits. -/
def finalQuotient : Program F [.nat, .nat, .nat] (.pair Scalars Scalars) :=
  witgen [n, signature, stored] do
    let magnitude ← vector.Apply h![stored] (squareMagnitude false)
    let square ← bignum.Square magnitude
    let product ← bignum.Mul square signature
    let qr ← bignum.DivMod product n
    let quotient ← value.Fst qr
    let q ← vector.Apply h![quotient] (limbFields 16 512)
    let bits ← vector.Apply h![q] (normalizeLimbs 16 512 15)
    let cells ← vector.Append q bits
    let out ← value.Pair q cells
    return out

/-- Dense z1 and z2 field convolution coefficients, in source allocation order. -/
def finalProduct : Program F [Scalars, .nat] (.pair Scalars Scalars) :=
  witgen [a, signature] do
    let shifted ← vector.Apply h![a] (shiftLimbs 16 256)
    let z1 ← vector.Apply h![shifted, shifted] (convolution 256 511)
    let b ← vector.Apply h![signature] (limbFields 16 256)
    let z2 ← vector.Apply h![z1, b] (convolution 511 766)
    let cells ← vector.Append z1 z2
    let out ← value.Pair z2 cells
    return out

/-- The low q*N block, implicit coefficient 766, and final carry range bits. -/
def finalTail : Program F [.nat, Scalars, Scalars, .nat] Scalars :=
  witgen [n, q, z2, digest] do
    let ns ← vector.Apply h![n] (limbFields 16 256)
    let qn ← vector.Apply h![q, ns] (convolution 512 766)
    let emNat ← vector.Apply h![digest] encodeDigest
    let em ← vector.Apply h![emNat] (limbFields 16 256)
    let rhsLow ← vector.Tabulate 766 h![qn, em] (witgen [k, qn, em] do
      let zero ← field.Const bn254Fr 0
      let x ← vector.GetD qn k zero
      let r ← vector.GetD em k zero
      let y ← field.Add x r
      return y)
    let zero ← field.Const bn254Fr 0
    let last ← vector.Singleton zero
    let lhs ← vector.Append z2 last
    let rhs ← vector.Apply h![lhs, rhsLow] (withTop 16 767)
    let carries ← vector.Apply h![lhs, rhs] finalCarries
    let cells ← vector.Append qn carries
    return cells

/-- Fused (stored-Sigma)^2*S/N relation. a16 is repacked from existing residue bits. -/
def finalWitness : Program F [.nat, .nat, .nat, .nat, Scalars] Scalars :=
  witgen [n, signature, digest, stored, a16] do
    let quotient ← vector.Apply h![n, signature, stored] finalQuotient
    let q ← value.Fst quotient
    let qCells ← value.Snd quotient
    let product ← vector.Apply h![a16, signature] finalProduct
    let z2 ← value.Fst product
    let zCells ← value.Snd product
    let tail ← vector.Apply h![n, q, z2, digest] finalTail
    let qz ← vector.Append qCells zCells
    let cells ← vector.Append qz tail
    return cells

/-- All 160454 arithmetic witness cells, excluding the separate 73-cell comparator.
    Public runtime inputs are [modulus N, signature S, raw SHA-256 digest Nat].
    Honest-input bounds and RSA validity are caller assumptions, not checks added here. -/
def arithmeticWitness : Program F [.nat, .nat, .nat] Scalars :=
  witgen [n, signature, digest] do
    let squares ← vector.Apply h![n, signature] squaresWitness
    let stored ← value.Fst squares
    let squareCells ← value.Snd squares
    let a16 ← vector.Apply h![squareCells] repackSquareBits
    let finalCells ← vector.Apply h![n, signature, digest, stored, a16] finalWitness
    let cells ← vector.Append squareCells finalCells
    return cells

/-- A small model boundary, not a proof of the RSA circuit relation. -/
theorem squareMagnitude_unsigned_model (input : Nat) :
    (squareMagnitude (F := Feature) true).eval model h![input] = input := rfl

end Witgen.Examples.RSA4096
