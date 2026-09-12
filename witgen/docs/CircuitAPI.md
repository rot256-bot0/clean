# Circuit API

The initial version of this document preceded implementation. The interfaces
below now compile on Lean 4.32.2 + Std. All names live in `Witgen.Circuits`,
importing only `Witgen.Core` and `Witgen.Arithmetic`.

## Generic certification

```lean
Circuit (Input Witness Output : Type)
-- Assumptions : Input → Prop
-- Relation    : Input → Witness → Prop
-- output      : Witness → Output
-- Spec        : Input → Output → Prop
-- sound       : ∀ i w, Assumptions i → Relation i w → Spec i (output w)

FormalWitgen (C : Circuit Input Witness Output)
  (M : Model F V) (Γ : List S) (t : S)
-- program       : Program F Γ t             (actual typed syntax)
-- encodeInput   : Input → HList V Γ
-- decodeWitness : V t → Witness             (the full witness record)
-- correct       : ∀ i, C.Assumptions i →
--   C.Relation i (decodeWitness (program.eval M (encodeInput i)))

Circuit.MathematicallyComplete C :=
  ∀ i, C.Assumptions i → ∃ w, C.Relation i w
CompleteOver C M encodeInput decodeWitness :=
  ∃ p : Program F Γ t, ∀ i, C.Assumptions i →
    C.Relation i (decodeWitness (p.eval M (encodeInput i)))
```

`FormalWitgen.generate`, `.satisfies`, `.spec`, `.mathematicallyComplete`, and
`.completeOver` expose the certificate. `FormalWitgen.lower` takes a
`CertifiedLowering M N R`, a target input encoder and whole-witness decoder,
a proof that source/target encoded inputs are related on admissible inputs,
and a proof that related returned values decode to equal **whole records**.
It stores `lowering.run source.program` and preserves the unchanged circuit.
`lower_generate` states whole-witness equality.

Mathematical completeness does not mention features. Executable completeness
is indexed by the exact signature/model through `M` AND fixed boundary adapters.
The ABI is supplied before the generator; it is not existentially chosen by
`CompleteOver`. This prevents a capability claim from silently hiding the whole
calculation in a newly chosen host encoder/decoder. `Generic.no_hidden_arithmetic`
proves an empty-feature identity program cannot implement increment with the
fixed identity boundary. Native admission still has to implement the chosen ABI.
Encoders and decoders are explicit semantic boundary adapters: the generic API
does not itself establish that they are cost-free or serialization-only, or
that arbitrary features can express a generator. Concrete demo IR bridges are
separate and may use semantic pairs/triples to construct these witness records.

## Quadratic: two internal witness cells

Namespace `Quadratic`:

```lean
Input   -- x y : Arithmetic.Field17
Witness -- square output : Arithmetic.Field17
Assumptions i := True
Relation i w := Field17.MulRel i.x i.x w.square ∧
                Field17.AddRel w.square i.y w.output
Spec i output := output = Field17.add (Field17.mul i.x i.x) i.y
gen i := { square := Field17.mul i.x i.x,
           output := Field17.add (Field17.mul i.x i.x) i.y }
```

`circuit`, `sound`, `gen_correct`, `mathematicallyComplete` are independent of
any demo-language feature set. Slot layout is **x=0, y=1, square=2, output=3**.
The square is a real reserved cell, not merely an unexported generator let.

## RSA-inspired modular multiplication slice

Namespace `ModMul`:

```lean
Input -- a b n : Nat
Witness := Arithmetic.MulModWitness -- product quotient remainder : Nat
Assumptions i := 0 < i.n ∧ i.n ≤ 16 ∧ i.a < i.n ∧ i.b < i.n
Relation i w := w.product < 257 ∧ w.quotient < i.n ∧ w.remainder < i.n ∧
  w.product % 257 = (i.a * i.b) % 257 ∧
  w.product % 257 = (w.quotient * i.n + w.remainder) % 257
Spec i output := output = (i.a * i.b) % i.n
gen i := Arithmetic.genMulMod i.a i.b i.n
```

`natRelation` uses `Arithmetic.mulModRel_of_field257`; `sound` then uses
`Arithmetic.mulMod_sound`. `gen_correct` supplies both gates and all ranges.
`circuit` and `mathematicallyComplete` expose the same generic interface.
This is a field257 modular-multiplication slice, not RSA exponentiation,
padding, a 4096-bit verifier, or production limb/carry arithmetization.
Slots are exactly **a=0, b=1, n=2, product=3, quotient=4, remainder=5**.

## Explicit vector population

Each concrete namespace provides a fixed-length `Buffer` of Nat cells backed
by a Lean `Vector`, `initial`, an actual pure `populate` updating only reserved
witness slots, `Inputs`, `WitnessCells`, and `Constraints` on the complete
buffer. Proofs cover unchanged input slots, every reserved cell, buffer
constraints from the full relation, and honest populated buffers. Concrete
negative controls reject swapped cells and a missing/zero internal cell even
when the output is correct.

```lean
-- Quadratic.Buffer = Vector Nat 4
Quadratic.populate b w :=
  (b.set 2 w.square.toNat).set 3 w.output.toNat
-- ModMul.Buffer = Vector Nat 6
ModMul.populate b w :=
  ((b.set 3 w.product).set 4 w.quotient).set 5 w.remainder
```

The definitions use the named constants in `Quadratic.Slots` and
`ModMul.Slots`. Both expose `layout`, `noAliases : layout.Nodup`, and `covers`
(every bounded index appears in the layout). `Buffer.toArray` is the native
comparison boundary; the statically checked length is not an extra cell.

Both namespaces expose:

| Endpoint | Guarantee |
|---|---|
| `initial_inputs i` | Initial input cells equal the external inputs. |
| `populate_inputs_unchanged b w` | Every input cell is preserved, even on otherwise invalid buffers/witnesses. |
| `populate_inputs i b w hb` | External input bindings are preserved. |
| `populate_witnessCells b w` | **Every** reserved cell equals its mapped witness field. |
| `constraints_of_cells` | Exact bindings plus the full relation imply buffer constraints. |
| `populate_constraints` | The actual writer produces a constrained buffer from an admissible full witness. |
| `honest_buffer` | `populate (initial i) (gen i)` satisfies all constraints. |
| `constraints_iff` | Buffer constraints are equivalent to exact inputs and a full related witness bound to its slots. Modmul includes `Assumptions i`. |
| `constraints_canonical` | Every bounded buffer index contains a Nat strictly below 17/257. |
| `constraints_sound` | Every accepted buffer's output cell satisfies the unchanged specification. |
| `certified_buffer g i` | Any `FormalWitgen circuit M Γ t` populates a constrained buffer; modmul also takes `hi : Assumptions i`. |

`Quadratic.populate_constraints i b w hb hw` requires `Inputs i b` and
`Relation i w`. `ModMul.populate_constraints i b w hi hb hw` additionally
requires its input-domain assumptions. Neither writer validates or silently
repairs invalid inputs: correctness is conditional on these explicit premises.

`Constraints` are direct arithmetic gates on the buffer, not equality to the
honest writer. Quadratic checks both witness ranges and
`square = x*x % 17`, `output = (square+y) % 17`. Modmul checks its assumptions,
exact inputs, canonical product, `quotient,remainder < n`, and both modulo-257
gates. The iff proofs decode the actual cells, not a generator's hidden locals.

These are canonical-field **Nat encodings**, not arbitrary integers interpreted
modulo the field prime. Constraints require canonical values and exact slot
bindings; adding 17/257 to a cell is not an accepted alias. Fixed length and
explicit pairwise-distinct slot indices prevent missing/overlapping allocation.
The writer does not infer witness cells from generator-local let bindings.

## Verification and trust boundary

Run `lake build Witgen.Circuits Witgen.CircuitTests`, then
`lake env lean -DwarningAsError=true Witgen/CircuitTests.lean`.
Tests print endpoint axioms. Observed RED/GREEN receipts are recorded below.
No proof placeholders, custom axioms, native decision proofs, blanket heartbeat
increases, or foreign framework dependency are permitted.

Lean certifies its program/model semantics and the pure vector writer only.
Serializers, Rust emission, rustc, arkworks F17/F257, GMP/rug, machine execution,
and comparison harnesses remain TCB unless separately verified. No native
backend or demo-language file is imported or modified by this lane.

## Test-first receipts

Each slice's tests were added and run before its implementation. RED command:
`lake env lean -DwarningAsError=true Witgen/CircuitTests.lean`.
GREEN command: `lake build Witgen.Circuits Witgen.CircuitTests && lake env lean
-DwarningAsError=true Witgen/CircuitTests.lean`.

| Slice | Observed RED excerpt (exit 1) | Observed GREEN |
|---|---|---|
| Generic certificate and lowering | ``Unknown identifier `Circuit` ``; ``Unknown identifier `FormalWitgen` `` | exit 0, build successful |
| Quadratic full witness | ``Unknown identifier `Quadratic.Input` `` | exit 0, build successful |
| Field257 modmul relation | ``Unknown identifier `ModMul.Input` `` | exit 0, build successful |
| Quadratic writer | ``Unknown identifier `populate_inputs_unchanged` `` | exit 0, build successful |
| Modmul writer | ``Unknown identifier `missing_product_rejected` `` | exit 0, build successful |
| Buffer/relation equivalence and generic certificate bridge | ``Unknown identifier `Quadratic.constraints_iff` ``; ``Unknown identifier `ModMul.certified_buffer` `` | exit 0, build successful |

The initial direct invocation first found an unbuilt `Arithmetic.olean`;
`lake build Witgen.Core Witgen.Arithmetic` resolved that setup prerequisite
before the generic RED receipt. No intentionally false production theorem or
proof placeholder was inserted to manufacture a RED result.

Final verification, exit 0:

```sh
lake build Witgen.CoreTests Witgen.ArithmeticTests Witgen.Circuits Witgen.CircuitTests
lake env lean -DwarningAsError=true Witgen/Circuits.lean
lake env lean -DwarningAsError=true Witgen/CircuitTests.lean
```

Actual example output:

```text
#[3, 4, 9, 13]
#[15, 15, 16, 225, 14, 1]
```

Tests include reduced quadratic wraparound, modmul modulus one, rejected zero
and oversized moduli, a product alias, a wrapped quotient-range countercheck,
swapped slots, and missing internal cells with correct outputs.

Printed axiom dependencies:

| Endpoints | Axioms |
|---|---|
| `FormalWitgen.spec`, `.mathematicallyComplete`, `.completeOver`, `.lower`, `.lower_generate` | none |
| Both circuits' `sound`, `gen_correct`, `mathematicallyComplete`; `ModMul.natRelation` | `propext` |
| Both circuits' population, iff, canonicality, buffer soundness, honest/certified-buffer endpoints | `propext`, `Quot.sound` |
| Both circuits' swapped/missing/alias rejection endpoints | `propext` |

Only standard Lean foundational axioms occur; no custom axioms or compiler
trust axiom. Source scanning of the owned Lean files found no proof
placeholders, unsafe declarations, native decision proofs, or heartbeat
overrides. Core/Arithmetic tests were replayed successfully; no claim is made
here about concurrent demo-language or native-backend integration tests.
