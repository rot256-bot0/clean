import Witgen.Typed.Field
namespace Witgen.Typed.SqrtTests
open Witgen
/-- Public authoring needs only the field capability, not ValueOp. -/
def sqrtOnly {F : Signature Ty} (f : FieldId) [Has (FieldOp f) F] :
    Program F [.field f] (.option (.field f)) :=
  witgen [a] do
    let r ← field.Sqrt a
    return r

-- Exercise the actual accelerator at full modulus width before evaluating fallback.
#eval do
  for f in [bn254Fr, secpBase, secpScalar] do
    for n in ([0, 1, 4, 9, (modulus f - 2)^2 % modulus f,
        (2^128 + 12345)^2 % modulus f] : List Nat) do
      let a := ((n : Nat) : ZMod (modulus f))
      unless (FieldSqrt.candidate f a)^2 == a do
        throw (IO.userError s!"accelerator failed: field={f.val} input={n}")
  IO.println "sqrt fullwidth candidate checks passed"

-- Source model evaluation, not a host-language substitute or generated fixture.
#eval do
  for f in [bn254Fr, secpBase, secpScalar] do
    for r in ([0,1,2,3,modulus f-2,2^128+12345,modulus f-(2^128+12345)] : List Nat) do
      let a := Residue.ofNat (modulus_pos f) (r*r)
      let out := (sqrtOnly (F := FieldOp f) f).eval (fieldModel f) h![a]
      let expected := min r ((modulus f-r) % modulus f)
      unless out.map Fin.val == some expected do
        throw (IO.userError s!"source sqrt failed: field={f.val} root={r}")
    let z := if f = secpBase then 3 else 5
    let a := Residue.ofNat (modulus_pos f) z
    unless ((sqrtOnly (F := FieldOp f) f).eval (fieldModel f) h![a]).isNone do
      throw (IO.userError s!"source nonresidue failed: field={f.val}")
  IO.println "sqrt source zero/residue/both-sign/fullwidth/nonresidue checks passed (all fields)"
-- Every parent export boundary must take the checked fast path or Euler-none path.
#eval do
  for f in [bn254Fr, secpBase, secpScalar] do
    let p := modulus f
    let inputs : List Nat := [0,1,2,4,p-1,p-2,2^128+17,2^200+17,(p-1)/2,(2^200+17)^2]
    for n in inputs ++ inputs.map (fun n => n*n) do
      let a := ((n : Nat) : ZMod p)
      let accepted := a == 0 || a^(p/2) == 1
      if accepted then
        unless (FieldSqrt.candidate f a)^2 == a do
          throw (IO.userError s!"fallback boundary: field={f.val} input={n}")
      let out := sqrtNat f n
      unless out.isSome == accepted do
        throw (IO.userError s!"Euler decision mismatch: field={f.val} input={n}")
      match out with
      | none => pure ()
      | some r =>
        unless r*r % p == n % p && r ≤ (p-r)%p do
          throw (IO.userError s!"canonical square mismatch: field={f.val} input={n}")
  IO.println "sqrt parent boundary fast-path/Euler checks passed (all fields)"
end Witgen.Typed.SqrtTests
