# Caliper backend API (coordination contract)

Module: `Witgen.Backends.Caliper`. Namespace: `Witgen.Backends.Caliper`.
Imports: `Witgen.Pipeline`, `Caliper.Render` (imports `Caliper.Core`; pinned dependency only).
Caliper is an analysis target, **not** the Rust execution engine.

Public names/types:

```lean
-- open Witgen Witgen.Demo
@[reducible] def Loc : Ty → Type
-- scalar/bool := Caliper.Reg; quad := Quad Caliper.Reg;
-- modmul := ModMul Caliper.Reg; list t := List (Loc t)

def Loc.regs : {t : Ty} → Loc t → List Caliper.Reg
def Loc.read : {t : Ty} → Loc t → Caliper.State64 → Val UInt64 t
-- Scalars decode with UInt64.ofBitVec; booleans decode as nonzero.
-- This module introduces reducible Caliper.Stmt64 := Caliper.Stmt 64
-- and Caliper.State64 := Caliper.State 64 (the pin calls its surface Caliper64).

inductive CompileError where
  | inputNotFresh (register firstFresh : Caliper.Reg)
  | branchShapeMismatch
  deriving Repr, DecidableEq

structure Compiled (t : Ty) where
  code : Caliper.Stmt64
  result : Loc t
  nextReg : Caliper.Reg

def compile (p : Program WordSig Γ t) (inputs : HList Loc Γ)
    (firstFresh : Caliper.Reg) : Except CompileError (Compiled t)

def render (compiled : Compiled t) : String
-- Integration seam: Caliper.Stmt.renderString of the actual generated Stmt.
```

`compile` checks every input register is strictly below `firstFresh`. Inputs may
alias each other; generated destinations never alias live input bindings. Typed
`Var.get` selects arguments/captures. Registers increase monotonically. Records
and lists are generation-time layouts, not opaque machine instructions.

All `WordOp`s lower to `imm`/`bin`: const/add/mul/div/mod/eq. `StructOp` construction/projection and separate `ListOp`s manipulate
locations without emitted instructions. Map/fold unroll compile-time-known lists,
including captures and accumulator locations. Branch compiles both actual regions,
emits `ifNZ`, and copies each selected result into a fresh common layout. Nested
list lengths must agree at every corresponding branch output; otherwise compilation
returns `branchShapeMismatch` (including the nonempty/empty conditional batch).
No dynamic list ABI, Field/Nat/GMP operations, opaque calls, or runtime generators.
Generation work is unpriced; every emitted arithmetic/copy/branch is Caliper-priced.

Proof boundary: generic UInt64/BitVec64 primitive correspondence and layout
preservation, plus universally quantified execution certificates for the **actual
compiler output** of `Demo.quadraticWord`, `Demo.modMulWord`, and the two-element
`fixedGatedWord`. There is no generic whole-compiler preservation theorem. Sibling
Caliper witness/examples modules should consume `compile`, `Compiled.code`,
`Compiled.result`, `Compiled.nextReg`, and `Loc.read` directly.

## Verification and exact certificates

Implemented and building (Lean 4.32.2):

- `compile_inputs_fresh`: checked success implies every recursively collected
  input register is below `firstFresh`, for any source AST and input layout.
- `compileWord_correct`: every word primitive, every typed operand location,
  every initial state, destination, tape and cost table; actual one-instruction
  `Caliper.run` agrees with `wordScalarModel` (including overflow and zero divisor).
- `compileStruct_correct`, `compileList_correct`, `compileAggregate_correct`: generic structural operations and separate list-layout operations commute with `Loc.read`; `locSchema_respects` supplies the layout representation law.
- `quadraticCompiled`, `modMulCompiled`: checked extraction of actual `compile`
  results at input registers `[0,1]`/`[0,1,2]`, fresh endpoints `2`/`3`.
- `quadratic_compiles`, `modMul_compiles`: exact checked-success equations.
- `quadratic_code`, `modMul_code`: kernel-checked generated constructor equalities.
- `quadratic_run`, `modMul_run`: unrestricted initial state, arbitrary tape/cost
  table; full record equals the source `Program.eval wordModel`, with exact time
  and zero net/peak dynamic memory. No word-range assumptions.
- `compileWord_frame`, `quadratic_frame`, `modMul_frame`, `fixedGated_frame`:
  registers outside the fresh allocation and (for whole examples)
  buffer/capacity/tape state remain unchanged.
- `fixedGatedWord`: real finite branch/map WordSig AST; false produces a zero quad
  for every input (not an empty list). `fixedGatedCompiled` fixes input locations
  `bool=0`, list `[1,2]`, captured scalar `3`, first fresh `4`.
- `fixedGated_compiles`, `fixedGated_run`: exact successful compilation and full
  two-element record-list preservation for **all** machine states/tapes/cost
  models, both branches, including all join copies. Results `[⟨18,19⟩,⟨20,21⟩]`,
  endpoint `22`. `fixedGatedTime C b = C.branch +
  (if b then 2 * quadraticTime C else 2 * C.imm) + 4 * C.mov`.
- `observe : Compiled t → (Caliper.State64 × Nat × Int × Int) →
  (Val UInt64 t × Nat × Int × Int)` reads the full result and cost profile.
- `exec_of_observed_run`: turns any such observation theorem into an existential
  `Caliper.Exec` derivation with exact profile and full-result equality, using
  pinned `Caliper.run_sound`.
- `quadratic_exec`, `modMul_exec`, `fixedGated_exec`: the corresponding named,
  universally quantified total-execution endpoints, with full returned values.

**Scope:** generic whole-compiler preservation/freshness is not claimed. Primitive
contracts are generic; whole-program certificates use the explicit layouts above.
Map/fold compile arbitrary finite static lists; their general semantic preservation
is tested, not covered by a generic theorem. The fixed gated batch is covered by
its universal certificate. All methods named `compileProgram`/`compileOp`/`join`
are internal traversal helpers and do not independently check input freshness;
external integrations must call `compile`.

Focused commands (from `witgen/`):

```sh
lake build Witgen.Backends.Caliper Witgen.Backends.CaliperCompilerTests
lake env lean Witgen/Backends/CaliperCompilerTests.lean
```

## Test and trust receipt

The focused build and direct Lean test command pass. Tests include **26 kernel
examples** and **one executable rendering check**: generated constructor inspection,
both gated branches and exact costs (unit model: true `17`, false `7`), wrapping
addition/multiplication/constants, division/remainder at zero, equality, operand
aliasing, reads of original bindings, captured map, empty map, real map-to-fold
transformation with a growing static accumulator, captured arithmetic fold,
runtime-dependent and nested branch-shape rejection, deep input freshness checks,
branch-to-continuation capture preservation, and fresh endpoints `8`/`6`/`22`.

Observed RED/GREEN slices: the initial scalar tests failed because the backend
module did not exist; fixed-gated tests failed on its missing source/compiled
definitions, then passed; the assembly rendering test failed on constructor
`Repr` output, then passed using the pinned `Stmt.renderString`. Remaining tests
are regression coverage. The renderer is executable-tested, not kernel-verified.

The retained `#print axioms` audit reports only standard Lean axioms:
`propext` and `Quot.sound` for run/Exec/frame/word contracts;
`propext` for layout preservation and checked example compilation equations.
No custom axioms, `sorry`, `admit`, `native_decide`, unsafe proof shortcuts,
`trustCompiler`, or heartbeat overrides occur in the backend.

Implementation note: nested joins recurse structurally on `Ty`, with a separately
structural list traversal. A mutual size-based join was replaced because its
well-founded recursion blocked kernel reduction of checked concrete compilation.
The compiler traverses finite source programs without a generation-fuel parameter;
checked applicability above still governs success. A large
static shape may generate large code; generation time is deliberately outside
Caliper's instruction-cost claim. `Caliper.run` fuel is interpreter fuel, not cost.
