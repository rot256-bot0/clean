# Bounded Fixed-Shape Gated Batch API

This small-field suite is retained for regressions; [CryptoAPI.md](CryptoAPI.md) describes the main BN254 examples.

Module `Witgen.Batch`, namespace `Witgen.Batch`; imports Demo/Pipeline/Circuits.
This is separate from `Demo.conditionalBatchField`, whose disabled result remains empty.

## Native program ABI (declared before implementation)

`Input` fields: `enabled : Bool`, `x0 x1 x2 c : Arithmetic.Field17`.
`encodeField : Input → HList (Demo.Val Field17) [.bool, .list .scalar, .scalar]`
packs **only** `[enabled, [x0,x1,x2], c]`; packing performs no arithmetic.
`encodeNat` and `encodeWord` preserve the same structure, changing scalar representation.

All six programs return `.list .quad`, with native record `Quad { square, output }`:

- `gatedBatchField`: map over xs; each body branches on captured enabled, selecting
  `Demo.quadratic` or an AST-built zero Quad (`FieldOp.const 0`, generic `StructOp.make .quad`).
- `gatedBatchFoldField`: actual `gatedBatchField.lower (Demo.mapToFold Demo.FieldOp)`.
- `gatedBatchNat`: actual `gatedBatchField.lower Demo.fieldToNat`.
- `gatedBatchWord`: actual `gatedBatchNat.mapHandler Demo.natToWord`.
- `gatedBatchFoldNat`: actual `gatedBatchFoldField.lower Demo.fieldToNat`.
- `gatedBatchFoldWord`: actual `gatedBatchFoldNat.mapHandler Demo.natToWord`.

Source map arguments are `[xs, enabled, c]`; map body inputs are `[x, enabled, c]`.
Branch arguments are `[enabled, x, c]`; **both** regions take `[x,c]` and return one Quad.
Map therefore returns exactly three records even when disabled. Lowering inserts the
fold accumulator using the existing generic map-to-fold template.

## Checked decoder and independent relation

`Witness` is a fixed record with `q0 q1 q2 : Demo.Quad Nat`.
`decodeNat : List (Demo.Quad Nat) → Option Witness` matches **exactly** `[q0,q1,q2]`;
all other lengths return `none`. `decodeField` maps scalar `.toNat`, then checks length;
`decodeWord` maps scalar `UInt64.toNat`, then checks length. No missing-cell default exists.

`circuit : Circuits.Circuit Input (Option Witness) (Option (List Nat))` uses a relation
requiring `some w`, canonical scalar ranges, and three independent gated quadratic rows.
Enabled rows constrain square=x*x mod17 and output=square+c mod17; disabled rows
constrain BOTH square and output to zero. This relation does not reference any generator.

Certificates: `sourceWitgen`, `foldFieldWitgen`, `natWitgen`, `wordWitgen`,
`foldNatWitgen`, `foldWordWitgen`. Each uses the declared fixed encoder/decoder ABI.

## Complete buffer ABI

`Buffer := Vector Nat 11` (array-backed).

| Cell | Index |
|---|---:|
| enabled (0 or 1) | 0 |
| x0 | 1 |
| x1 | 2 |
| x2 | 3 |
| c | 4 |
| square0 | 5 |
| out0 | 6 |
| square1 | 7 |
| out1 | 8 |
| square2 | 9 |
| out2 | 10 |

`initial` binds inputs. `populate : Buffer → Witness → Buffer` writes all six reserved
witness cells, including disabled zeros, without modifying input cells.
`populateDecoded : Buffer → Option Witness → Option Buffer` rejects `none`.
`Constraints` checks input bindings, canonical witness ranges, and all six gated equations
on the buffer; it is not equality to a selected writer. Rust emission/driver execution
remains parent-owned.

## Compiled proof endpoints

All names below are in `Witgen.Batch`.

| Endpoint | Contract |
|---|---|
| `gatedBatchField_eval i` | Exact ordered list of three native Field17 Quads. |
| `gatedBatchFoldField_correct i` | Map-eliminated evaluation equals the source evaluation. |
| `gatedBatchNat_correct i`, `gatedBatchFoldNat_correct i` | Complete Nat records equal the mapped mathematical records. |
| `gatedBatchWord_correct i` | Every word record field decoded to Nat equals the actual Nat AST result. |
| `gatedBatchWord_eval i`, `gatedBatchFoldWord_eval i` | Exact native word records, not only their public outputs. |
| `gatedBatchFoldWord_correct i` | Complete composed map→fold→Field→Nat→Word endpoint. |
| `native_record_shape i` | Conjunction of length=3 for all six actual programs, both branch choices. |
| `decodeNat_complete_records xs w h` | Successful decoding implies `xs = [w.q0,w.q1,w.q2]`. |
| `decodeNat_wrong_length`, `decodeField_wrong_length`, `decodeWord_wrong_length` | Any non-three length decodes to `none`. |
| `none_rejected i` | `¬ Relation i none`. |
| `source_generates`, `foldField_generates`, `nat_generates`, `word_generates`, `foldNat_generates`, `foldWord_generates` | Each actual AST decodes to `some (expectedWitness i)`, including all six scalar fields. |
| `foldWord_generate_eq_source i` | Complete optional witness equality for the composed pipeline. |
| `sound i w hi h` | Generator-independent relation implies the three public-output equations. |
| `source_completeOver`, `nat_completeOver`, `word_completeOver` | Existing fixed-encoder/fixed-decoder `CompleteOver`; no generic API edits. |
| `Slots.noAliases`, `Slots.covers` | Layout indices are distinct and cover every `Fin 11`. |
| `populate_inputs_unchanged b w k` | Preserves every input index `k : Fin 5`, even for arbitrary buffer contents. |
| `populate_witnessCells b w` | Every reserved witness slot equals its precise record field. |
| `disabled_populates_all i b h k` | Every witness index `k.val+5`, `k : Fin 6`, becomes zero on a disabled input, even from a dirty buffer. |
| `constraints_iff i b` | Constraints iff exact inputs plus a complete, cell-bound witness satisfying the independent relation. |
| `constraints_sound i b h` | Every accepting buffer has the specified three public outputs. |
| `constraints_canonical i b h k` | Every cell, `k : Fin 11`, is below 17. |
| `populate_constraints i b w hb hw` | Actual six-store writer satisfies all gates. |
| `honest_buffer i` | Complete mathematical witness populates a satisfying buffer. |
| `certified_buffer g i` | Any `FormalWitgen circuit ...` returns Some and produces a complete satisfying buffer with all input/witness bindings. |

`certified_buffer` concludes exactly:

```lean
∃ w b, g.generate i = some w ∧
  populateDecoded (initial i) (g.generate i) = some b ∧
  WitnessCells b w ∧ Inputs i b ∧ Constraints i b
```

`expectedQuad`, `expectedRecords`, `expectedWitness`, and `expectedOutput` are mathematical
specifications only. Neither input encoders nor output decoders call them. Nat/Word
encoders change scalar representation only. The Nat decoder checks shape, not scalar
range; `Relation` and `Constraints` require the canonical ranges explicitly.

## Exact parent integration

1. Import `Witgen.Batch` in the parent driver/root where needed. No parent-owned file was
   edited by this lane. `lake build Witgen.Batch Witgen.BatchTests` works without root edits.
2. Serialize the six `.program` values from the certificates above using the matching
   `Demo.fieldInfo`, `Demo.natInfo`, or `Demo.wordInfo`. The module input names must be
   **three** names, `["enabled", "xs", "c"]`, not the five physical buffer-cell names.
   For example, the existing serializer call is:

   ```lean
   Export.moduleJson Demo.wordInfo "generate" "word" ["enabled", "xs", "c"]
     Batch.foldWordWitgen.program none "field17"
   ```

   `none` here omits parent-owned wire-layout JSON; it does not skip the batch decoder.
   Attach the 11-cell driver layout using the parent's supported schema. The existing
   scalar-only layouts must not silently treat `xs` as a single field cell.
3. Native arguments are `enabled`, a structural list `[x0,x1,x2]`, and `c`. Admit only
   canonical scalar inputs 0..16 and the exact three-element input packing. Field17→Word
   proofs do not authorize arbitrary unbounded Nat inputs. Boolean buffer encoding is 0/1.
4. Check native result length **equals 3 before indexing**. Copy result `[0].square`,
   `[0].output`, `[1].square`, `[1].output`, `[2].square`, `[2].output` into cells
   5,6,7,8,9,10 respectively. Preserve cells 0..4. Disabled output is three zero records,
   never an empty result; do not skip writes because enabled is false.
5. Reference results are actual `program.eval` results, with `Export.valueJson` at
   `.list .quad`. Compare the entire record list and all 11 buffer cells, not just the
   three public outputs. `certified_buffer Batch.foldWordWitgen i` is the complete
   Lean endpoint; `foldWord_generate_eq_source i` supplies exact source agreement.

For input `(enabled,3,4,16,4)`, actual Lean buffers are:

```text
enabled=true:  #[1,3,4,16,4,9,13,16,3,1,5]
enabled=false: #[0,3,4,16,4,0,0,0,0,0,0]
```

## Executed checks and trust

```sh
lake build Witgen.Batch Witgen.BatchTests Witgen.CoreTests Witgen.ArithmeticTests Witgen.CircuitTests Witgen.DemoTests
lake env lean -DwarningAsError=true Witgen/Batch.lean
lake env lean -DwarningAsError=true Witgen/BatchTests.lean
```

All exited 0. The existing Core/Arithmetic/Circuit/Demo test targets were replayed by Lake;
the batch module and batch test file were also re-elaborated directly with warnings as errors.
Actual executable output:

```text
batch: 578 fixed triples; 3468 full-record and dirty-buffer checks passed
some #[1, 3, 4, 16, 4, 9, 13, 16, 3, 1, 5]
some #[0, 3, 4, 16, 4, 0, 0, 0, 0, 0, 0]
```

The bounded regression enumerates both Booleans and every x/c pair with triple
`[x,(x+1)%17,16]`, checking all six programs against independently written Nat equations,
then populating deliberately dirty witness slots and checking every field and gate. This is
not an exhaustive enumeration of all Inputs; the theorems quantify over every Input.
Negative controls include short/extra result lists, the existing empty-disabled demo,
missing square with otherwise correct outputs, stale disabled square, swapped fields,
a noncanonical alias, and a changed enable cell.

Five test-first RED/GREEN slices are retained in `artifacts/batch-red-{1..5}.txt` and
`artifacts/batch-green-{1..5}.txt`. The first RED was the absent Batch module; subsequent
REDs were missing named APIs. `batch-verification-initial.txt` retains the missing
`Decidable WitnessCells` test failure subsequently fixed. `batch-tests.txt` and
`batch-final-verification.txt` contain successful outputs and endpoint axiom inspections.

The independent `sound` theorem needs no axioms. Inspected batch certificates and
pipeline/buffer endpoints use at most standard Lean `propext` and `Quot.sound`; no compiler
trust or custom axioms. No proof placeholders, unsafe shortcuts, native decision proofs,
heartbeat increases, foreign imports, or generic API changes were added. These proofs
cover Lean AST/model semantics and the pure vector writer. Serialization, Rust emission,
Rust compilation, foreign arithmetic, and native driver execution remain separate TCB;
this lane does not claim native backend execution.
