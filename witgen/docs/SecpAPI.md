# secp256k1 typed feature

Implementation uses Mathlib `WeierstrassCurve.Affine.Point` over `ZMod (Typed.modulus Typed.secpBase)`, curve coefficients `(0,0,0,0,7)`. No discrete-log representation, synthetic point carrier, or host curve oracle.

Concrete entry point: `import Witgen.Typed.Secp`. Instances `Secp.basePrime` and `Secp.scalarPrime` use `Witgen.PrimeCertificates.secpBase_prime` and `.secpScalar_prime` for the exact decimal moduli in `Typed.Types`. These are closed kernel-checked Lucas certificates. The reusable curve foundation is parameterized, but this public entry point supplies both facts without assumptions.

**Computability finding:** pinned Mathlib `Affine/Point.lean` lines 768–772 defines the point `AddCommGroup.nsmul := nsmulBinRec` (not linear recursion). Canonical scalar multiplication `s.val • P` therefore already uses binary recursion; we should reuse the existing proven implementation rather than add another scale algorithm.

Checked checkpoint: `lake build Witgen.Typed.Secp Witgen.Typed.SecpConcreteTests` passes. Generator membership/nonsingularity use bounded kernel `decide` on the actual ZMod equation, not primality factoring. `mixed_correct` proves an explicit modular-arithmetic/point-group specification; `mixed_one_one` proves the real point calculation 2G−G=G. Exact `#guard_msgs` tests reject base-as-scalar. Concrete runtime checks evaluate known 2G and −G coordinates, high-width (n−1)G=−G, the mixed program, generator affine roundtrip, invalid(0,0) rejection, and infinity conversion. The high-width sample is a runtime test, not a proof of the generator's order.

Public aliases in `Witgen.Typed.Public` are `Witgen.curve.Add P Q`, `Scale scalar P`, `Inv P` (group inverse `-P`), `Generator`, `Identity`, and `X P` (base-field coordinate with explicit identity convention `X(0)=0`). The earlier `Witgen.secp.*` helpers remain available. `Scale` accepts only `.field secpScalar`; `X` returns `.field secpBase`. `Witgen.secp256k1.Base/Scalar` name the distinct field IDs.

## Affine conversion API and JSON seam

```lean
-- exact input/output types; explicit optionality
curve.ToAffine   : Var Γ .point → Step F Γ (.option (.pair (.field secpBase) (.field secpBase)))
curve.FromAffine : Var Γ (.pair (.field secpBase) (.field secpBase)) → Step F Γ (.option .point)
```

`ToAffine(0)=None`; `FromAffine(0,0)=None` (off curve); `FromAffine` never uses infinity as an error sentinel. `fromAffine_isSome_iff` proves acceptance iff `y²=x³+7` over the actual base field. `affine_roundtrip` proves every nonsingular affine point roundtrips, using the proved nonzero discriminant. `concrete_generator_roundtrip` evaluates a finite `Program` containing ToAffine, optional bind with a closed region, and FromAffine.

Type JSON: pair is `{"pair":[leftType,rightType]}`, option is `{"option":elementType}`; both affine component types retain `field:1` and the base modulus. Operation tags are `curve.toAffine`, `curve.fromAffine`. `option.bind` has one closed region with one unwrapped input and optional result. The optional `ValueOp` adds `value.pair/fst/snd`, `option.some/none/bind` without altering the core.

Commands: `lake env lean --run MainTyped.lean affine` emits the generator roundtrip; `... from-affine` emits a typed pair-input conversion. Native option implementations must preserve None/Some, not coerce invalid pairs to identity.
## Scope

The native implementation uses `ark-secp256k1`/`ark-ec` 0.6.0 and preserves these typed signatures. Its affine constructor checks the actual equation before constructing an Arkworks affine value, so Arkworks' distinguished infinity representation is not accepted as an ordinary coordinate pair. Source/native tests cover valid points, invalid `(0,0)`, and explicit infinity. A certified curve→field fallback would be a separate implementation of this same feature; it is not supplied here.

The mixed example computes scalar Mul/Add/Square, actual point scaling/addition/inverse, and base Mul/Add/Square using the actual computed point coordinate view. Base arithmetic is *not* silently used as scalar arithmetic. Scope excludes proving generator order/cofactor and lowering point arithmetic to U64; scalar representatives act by their canonical natural value, not by an unproved modulo-order action law.
