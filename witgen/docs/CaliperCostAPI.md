# Actual Caliper witness-output and cost API

```lean
import Witgen.Backends.CaliperExamples
open Caliper Witgen.Backends.CaliperWitness Witgen.Backends.CaliperExamples

#check writeRegs_exec
#check writeRegs_triple
#check quadratic_circuit_exec
#check modMul_circuit_exec
#check fixedGated_unit_triple
```

Caliper pin: `b62f7c8be35df0aa728e5a6aac7bae85eef67449`; Lean 4.32.2.
These modules use actual `Caliper.Stmt`, `State`, `Exec`, `Triple`, and `run`.
Machine words are `BitVec 64`; source `UInt64` values are bridged by
`UInt64.ofBitVec`. No Rust runtime is bounded by these cost numbers.

## Generic writer (API published before implementation)

Module/namespace: `Witgen.Backends.CaliperWitness`.

```lean
pushRegs (b : Caliper.BufId) (rs : List Caliper.Reg) : Caliper.Stmt w
writeRegs (b : Caliper.BufId) (rs : List Caliper.Reg) : Caliper.Stmt w
writerTime (C : Caliper.CostModel) (rs : List Caliper.Reg) : Nat
```

`pushRegs` emits one `memPush b r` per entry, in order. `writeRegs` emits
`memAllocI b rs.length ;; pushRegs b rs`. Duplicates are copied in list order.
No scratch register is allocated. `writerState` merely names the exact final state
in the specification; the execution proof is built from Caliper constructors.

`writeRegs_exec C tape s b rs hfresh` quantifies over every width, cost table, tape,
state, buffer name and register list. Its freshness assumption is `s.caps b = 0`.
It proves termination, memory-safe execution and the **exact** resource profile:

- time `C.memAlloc + rs.length * C.allocPerWord + rs.length * C.memPush`;
- net and peak buffer-capacity growth both `rs.length` words.

`writerState_post` / `WriterPost` prove exact filled contents
`(rs.map s.regs).toArray`, final capacity `rs.length`, unchanged **all** registers,
unchanged tape cursor, and unchanged contents/capacities at every other buffer name.
`writeRegs_unique` extends the exact state/cost result to every other execution by
Caliper determinism. `pushRegs_exec` exposes the generalized free-capacity premise
`(s.bufs b).size + rs.length ≤ s.caps b` for use without allocating again.

`writeRegs_triple` additionally assumes `State.WellFormed` and preserves it. That
assumption requires filled sizes within reserved capacities and finite reservation
support, so a fresh buffer is genuinely empty and memory credits are physical.
`writeRegs_liveMem` gives exact final absolute footprint; `writeRegs_reaches_bound`
bounds every instruction-boundary state, for any support bound covering `b`.
`writeRegs_noWrites` proves the writer's empty register write-set.

**Reserve is not initialization.** Allocation creates an empty filled prefix;
pushes initialize each cell and are charged separately. `reserved_load_noExec`
proves no load from a newly reserved empty buffer has an execution. `full_push_noExec`
rejects full or overfull buffers. No automatic growth or amortized push is assumed.

`writerTime_unit` and `writerTime_cycles` prove times `2*n` and `6*n` respectively.
No `memLen` or indexed load occurs in the writer: arbitrary finite `n` is allowed
by Caliper's mathematical semantics. Downstream length-as-word code must additionally
require `n < 2^w`; the concrete layouts below satisfy that bound.

## Compiler integration and complete layouts

Module/namespace: `Witgen.Backends.CaliperExamples`.
Compiler API: [CaliperBackendAPI.md](CaliperBackendAPI.md).

```lean
withWitness (c : Witgen.Backends.Caliper.Compiled t)
  (b : Caliper.BufId) (inputs : List Caliper.Reg) : Caliper.Stmt 64
```

The code is **the actual checked compiler result** `c.code`, followed by
`writeRegs b (inputs ++ Loc.regs c.result)`. It does not reconstruct a handwritten
arithmetic program. `withWitness_exec` is the reusable composition theorem:
consume a memory-neutral producer execution, its full-cell value correspondence,
and syntactic register/buffer frame obligations. `produce_write_exec` exposes the
lower-level generic Caliper sequencing seam.

| Artifact | Initial input registers | Returned witness registers | Full buffer contents, in order |
|---|---|---|---|
| `quadraticCode b` | `r0=x`, `r1=y` | `r4=square`, `r7=output` | `[x,y,square,output]` |
| `modMulCode b` | `r0=a`, `r1=b`, `r2=n` | `r3=product`, `r4=quotient`, `r5=remainder` | `[a,b,n,product,quotient,remainder]` |
| `fixedGatedCode b` | `r0=flag`, `r1=x0`, `r2=x1`, `r3=c` | `r18,r19` row 0; `r20,r21` row 1 | `[flag,x0,x1,c,square0,out0,square1,out1]` |

For all three: scratch registers may initially contain anything; output buffer `b`
has zero initial capacity; all other buffers may already be populated, subject to
`WellFormed` for physical-memory claims. Input registers and all other buffers and
capacities are preserved. Tape cursor is preserved, for **every** supplied tape.
Nonzero flags enable the gated branch; the raw flag word is copied unchanged.
Disabled execution still initializes all four witness cells, to zero.

`OutputPost` contains the full array equality, exact capacity, input-register
preservation, tape frame, and other-buffer frame. The source record/list value is
computed by the existing source `Program.eval wordModel`, not by a host witness oracle.

## Proved execution and costs

These totals **include full input-plus-witness buffer allocation and population**.
They are exact Caliper time/net/peak profiles, except rows explicitly marked as
worst-case bounds. `.cycles` is an abstract shipped cost table, not measured cycles.

| Artifact/path | `.unit` time | `.cycles` time | Net words | Peak growth words |
|---|---:|---:|---:|---:|
| Quadratic | 14 | 90 | 4 | 4 |
| ModMul | 15 | 99 | 6 | 6 |
| Fixed gated, enabled | 33 | 186 | 8 | 8 |
| Fixed gated, disabled | 23 | 56 | 8 | 8 |
| Fixed gated, worst-case bound | ≤33 | ≤186 | ≤8 | ≤8 |

Verified declarations (all under `Witgen.Backends.CaliperExamples`):

- `quadratic_witness_exec`, `modMul_witness_exec`, `fixedGated_witness_exec`:
  universally quantified exact execution, complete output layout, frames; every
  initial word state, arbitrary cost table and tape, fresh output buffer.
- `quadratic_triple`, `modMul_triple`: total correctness and well-formedness,
  generic cost table with exact-derived upper bounds.
- `quadratic_unit_cost`, `quadratic_cycles_cost`, `modMul_unit_cost`,
  `modMul_cycles_cost`, `fixedGated_unit_cost`, `fixedGated_cycles_cost`: exact
  reductions of the proved symbolic time formulas, including per-word allocation.
- `quadratic_unit_resources`, `modMul_unit_resources`: every completed execution
  has the stated exact `.unit` time/net/peak, using determinism.
- `fixedGated_unit_triple`, `fixedGated_cycles_triple`: total-correctness worst-case
  bounds for both flag values, plus full output/frame and well-formedness.
- `quadratic_intermediate_memory`, `modMul_intermediate_memory`: every state reached
  within the complete emitted program stays within initial live capacity plus 4/6.

### Circuit correspondence, with precise applicability

`quadratic_circuit_exec` combines `.unit` execution `(14,4,4)`, well-formedness,
input/frame preservation and **the actual buffer's Nat view** satisfying
`Circuits.Quadratic.Constraints`. Inputs must decode to `fieldWord i.x` /
`fieldWord i.y`, for `Field17` inputs. `quadratic_cells_circuit` is the complete
layout correspondence lemma.

`modMul_circuit_exec` similarly combines `(15,6,6)` with the actual buffer satisfying
`Circuits.ModMul.Constraints`. Inputs must decode to `UInt64.ofNat i.a/i.b/i.n` and
satisfy the existing circuit assumptions **`0 < n ≤ 16`, `a < n`, `b < n`**.
`modMul_cells_circuit` bridges the full product/quotient/remainder layout.

The stronger circuit results are not claimed for arbitrary word inputs. The word-level
execution/cost certificates still cover wrapping arithmetic and zero divisors, in
agreement with the source's total `UInt64`/`BitVec` semantics.

The gated artifact is the compiler's **two-row** `fixedGatedWord`, not the separate
three-row `Witgen.Batch.gatedBatchWord`. Its certificate covers full source word
semantics and witness-buffer layout, not that separate three-row circuit relation.
No generic whole-compiler semantic-preservation theorem is claimed here.

### Registers versus buffers

Caliper's `Exec` net/peak count **reserved buffer words only**, not registers.
`compiled_register_endpoints` proves static SSA endpoints `8`, `6`, `22` for these
artifacts (inputs start at register 0; fresh endpoints are 2, 3, 4 respectively).
The writer adds no registers. These are unrecycled static register namespaces, **not**
`Caliper.Stmt.regPeak₀` liveness results; this layer does not claim a minimal register
allocation or a combined registers-plus-buffers physical footprint theorem.
The 4/6/8 memory figures must not be advertised as total machine memory.

## Executed validation and trust boundary

From `witgen/`:

```sh
lake build Witgen.Backends.CaliperWitness Witgen.Backends.CaliperExamples Witgen.Backends.CaliperTests
lake env lean Witgen/Backends/CaliperTests.lean
```

`CaliperTests.lean` executes pinned `Caliper.run`, checks exact full arrays and costs
for both tables and both gated paths, all **289** canonical quadratic input pairs,
and all **1496** ModMul inputs with `1 ≤ n ≤ 16` and `a,b < n`. Additional checks
exercise zero divisors, maximal-word wraparound, and noncanonical nonzero flag words.

Observed reference-interpreter receipts include:

```text
quadratic: #[3,5,9,14], unit (14,4,4), cycles (90,4,4)
modMul:    #[7,9,11,63,5,8], unit (15,6,6), cycles (99,6,6)
gated on:  #[1,3,4,5,9,14,16,4], unit (33,8,8), cycles (186,8,8)
gated off: #[0,3,4,5,0,0,0,0], unit (23,8,8), cycles (56,8,8)
writer [2,0,2], r2=42: #[42,0,42], unit (6,3,3), cycles (18,3,3)
```

Negative controls reject uninitialized load/store, push without capacity, push after
full population, overfull-buffer push and an out-of-range load. Raw Caliper `run`
is **not a global state validator**: `skip` can succeed with an irrelevant malformed
buffer. The tests explicitly record that limitation rather than claiming blanket
malformed-state rejection. `WellFormed` is the formal physical-memory precondition.

Axiom inspection of the execution/triple/circuit endpoints reports only standard
`propext`, `Classical.choice`, `Quot.sound` (some smaller theorems use a subset).
No custom axioms, `sorry`, `admit`, `native_decide`, unsafe proof shortcut, or heartbeat
increase is used. Runtime `#guard`/`#eval` checks are validation; universal claims come
from kernel-checked theorems. No dependency source/cache was edited by this layer.

Development receipts: the first writer test failed because its module did not exist,
then passed after implementation; the next integration import failed before the module
existed; the gated test failed on missing `fixedGatedCode`, then passed after that slice.
Temporary concurrent compiler-build failures were resolved by the compiler owner;
no local surrogate or weakened proof was substituted.
