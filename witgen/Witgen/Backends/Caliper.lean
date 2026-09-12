import Witgen.Pipeline
import Caliper.Render

/-! A static-shape compiler into the actual Caliper machine. Generation-time
closures below traverse finite region syntax; no closure enters the output IR.
This is an analysis backend, not an implementation of the Rust execution engine. -/
namespace Caliper
abbrev Stmt64 := Stmt 64
abbrev State64 := State 64
end Caliper

namespace Witgen.Backends.Caliper
open Witgen Demo

@[reducible] def Loc : Ty → Type
  | .scalar | .bool => _root_.Caliper.Reg
  | .quad => Quad _root_.Caliper.Reg
  | .modmul => ModMul _root_.Caliper.Reg
  | .list t => List (Loc t)

namespace Loc

def regs : {t : Ty} → Loc t → List _root_.Caliper.Reg
  | .scalar, r | .bool, r => [r]
  | .quad, q => [q.square, q.output]
  | .modmul, q => [q.product, q.quotient, q.remainder]
  | .list _, xs => xs.flatMap regs

def read : {t : Ty} → Loc t → _root_.Caliper.State64 → Val UInt64 t
  | .scalar, r, s => UInt64.ofBitVec (s.regs r)
  | .bool, r, s => decide (s.regs r ≠ 0)
  | .quad, q, s => ⟨UInt64.ofBitVec (s.regs q.square), UInt64.ofBitVec (s.regs q.output)⟩
  | .modmul, q, s =>
      ⟨UInt64.ofBitVec (s.regs q.product), UInt64.ofBitVec (s.regs q.quotient),
        UInt64.ofBitVec (s.regs q.remainder)⟩
  | .list _, xs, s => xs.map (fun x => read x s)
end Loc

inductive CompileError where
  | inputNotFresh (register firstFresh : _root_.Caliper.Reg)
  | branchShapeMismatch
  deriving Repr, DecidableEq

structure Compiled (t : Ty) where
  code : _root_.Caliper.Stmt64
  result : Loc t
  nextReg : _root_.Caliper.Reg

/-- Generation-time compiled region, never a target instruction. -/
abbrev CompilerBody (sh : RegionShape Ty) :=
  HList Loc sh.inputs → _root_.Caliper.Reg → Except CompileError (Compiled sh.output)

/-- No source bindings are updated: every arithmetic destination is fresh. -/
def compileWord : WordOp args shapes t → HList Loc args → Nat → Compiled t
  | .const n, .nil, fresh => ⟨.imm fresh (BitVec.ofNat 64 n), fresh, fresh + 1⟩
  | .add, .cons a (.cons b .nil), fresh => ⟨.bin .add fresh a b, fresh, fresh + 1⟩
  | .mul, .cons a (.cons b .nil), fresh => ⟨.bin .mul fresh a b, fresh, fresh + 1⟩
  | .div, .cons a (.cons b .nil), fresh => ⟨.bin .udiv fresh a b, fresh, fresh + 1⟩
  | .mod, .cons a (.cons b .nil), fresh => ⟨.bin .umod fresh a b, fresh, fresh + 1⟩
  | .eq, .cons a (.cons b .nil), fresh => ⟨.bin .eq fresh a b, fresh, fresh + 1⟩

/-- Records and containers are layouts; construction/projection emits no work. -/
def compileData : DataOp args shapes t → HList Loc args → Loc t
  | .quad, .cons a (.cons b .nil) => ⟨a, b⟩
  | .square, .cons q .nil => q.square
  | .output, .cons q .nil => q.output
  | .modmul, .cons p (.cons q (.cons r .nil)) => ⟨p, q, r⟩
  | .product, .cons q .nil => q.product
  | .quotient, .cons q .nil => q.quotient
  | .remainder, .cons q .nil => q.remainder
  | .empty _, .nil => []
  | .push _, .cons xs (.cons x .nil) => xs ++ [x]

/-- Both arms write into the same *new* layout, so parallel-copy cycles cannot
occur even when records share registers or a branch returns its captures. -/
structure Join (t : Ty) where
  result : Loc t
  yesCopies : _root_.Caliper.Stmt64
  noCopies : _root_.Caliper.Stmt64
  nextReg : Nat

def joinList {t : Ty}
    (element : Loc t → Loc t → Nat → Except CompileError (Join t)) :
    List (Loc t) → List (Loc t) → Nat → Except CompileError (Join (.list t))
  | [], [], n => .ok ⟨[], .skip, .skip, n⟩
  | a :: as, b :: bs, n => do
      let h ← element a b n
      let tail ← joinList element as bs h.nextReg
      pure ⟨h.result :: tail.result, .seq h.yesCopies tail.yesCopies,
        .seq h.noCopies tail.noCopies, tail.nextReg⟩
  | _, _, _ => .error .branchShapeMismatch

def join : {t : Ty} → Loc t → Loc t → Nat → Except CompileError (Join t)
  | .scalar, a, b, n | .bool, a, b, n => .ok ⟨n, .mov n a, .mov n b, n + 1⟩
  | .quad, a, b, n => .ok ⟨⟨n, n + 1⟩,
      .seq (.mov n a.square) (.mov (n + 1) a.output),
      .seq (.mov n b.square) (.mov (n + 1) b.output), n + 2⟩
  | .modmul, a, b, n => .ok ⟨⟨n, n + 1, n + 2⟩,
      .seq (.mov n a.product) (.seq (.mov (n + 1) a.quotient) (.mov (n + 2) a.remainder)),
      .seq (.mov n b.product) (.seq (.mov (n + 1) b.quotient) (.mov (n + 2) b.remainder)), n + 3⟩
  | .list _, as, bs, n => joinList join as bs n

/-- Static unrolling preserves the same capture locations on every iteration. -/
def compileMap {caps : List Ty} {a b : Ty} (body : CompilerBody ⟨a :: caps, b⟩)
    (captures : HList Loc caps) : List (Loc a) → Nat → Except CompileError (Compiled (.list b))
  | [], n => .ok ⟨.skip, [], n⟩
  | x :: xs, n => do
      let h ← body (.cons x captures) n
      let tail ← compileMap body captures xs h.nextReg
      pure ⟨.seq h.code tail.code, h.result :: tail.result, tail.nextReg⟩

/-- The accumulator may itself be a static list, including a growing one. -/
def compileFold {caps : List Ty} {a b : Ty} (body : CompilerBody ⟨a :: b :: caps, b⟩)
    (captures : HList Loc caps) : List (Loc a) → Loc b → Nat → Except CompileError (Compiled b)
  | [], acc, n => .ok ⟨.skip, acc, n⟩
  | x :: xs, acc, n => do
      let h ← body (.cons x (.cons acc captures)) n
      let tail ← compileFold body captures xs h.result h.nextReg
      pure ⟨.seq h.code tail.code, tail.result, tail.nextReg⟩

def compileControl : Control args shapes t → HList Loc args →
    HList CompilerBody shapes → Nat → Except CompileError (Compiled t)
  | .branch _ _, .cons c captures, .cons yes (.cons no .nil), n => do
      let y ← yes captures n
      let z ← no captures y.nextReg
      let j ← join y.result z.result z.nextReg
      pure ⟨.ifNZ c (.seq y.code j.yesCopies) (.seq z.code j.noCopies), j.result, j.nextReg⟩
  | .map _ _ _, .cons xs captures, .cons body .nil, n => compileMap body captures xs n
  | .fold _ _ _, .cons xs (.cons acc captures), .cons body .nil, n =>
      compileFold body captures xs acc n

def compileOp : WordSig args shapes t → HList Loc args →
    HList CompilerBody shapes → Nat → Except CompileError (Compiled t)
  | .inl op, args, _, n => .ok (compileWord op args n)
  | .inr (.inl op), args, _, n => .ok ⟨.skip, compileData op args, n⟩
  | .inr (.inr op), args, bodies, n => compileControl op args bodies n

mutual
  /-- Internal traversal. External callers use `compile` for the freshness check. -/
  def compileProgram : Program WordSig Γ t → HList Loc Γ → Nat →
      Except CompileError (Compiled t)
    | .ret r, env, n => .ok ⟨.skip, r.get env, n⟩
    | .let_ op args regions next, env, n => do
        let h ← compileOp op (args.map (fun r => r.get env)) (compileRegions regions) n
        let tail ← compileProgram next (.cons h.result env) h.nextReg
        pure ⟨.seq h.code tail.code, tail.result, tail.nextReg⟩
  def compileRegions : Regions WordSig shapes → HList CompilerBody shapes
    | .nil => .nil
    | .cons body rest => .cons (compileProgram body) (compileRegions rest)
end

def inputRegs : HList Loc Γ → List Nat
  | .nil => []
  | .cons x xs => Loc.regs x ++ inputRegs xs

/-- Checked applicability: all input locations precede the fresh endpoint.
Region output shapes are checked by `join`; neither arm can hide a shape error. -/
def compile (p : Program WordSig Γ t) (inputs : HList Loc Γ) (firstFresh : Nat) :
    Except CompileError (Compiled t) :=
  match (inputRegs inputs).find? (fun r => firstFresh ≤ r) with
  | some r => .error (.inputNotFresh r firstFresh)
  | none => compileProgram p inputs firstFresh

/-- Successful public compilation certifies the input-side freshness check,
including registers nested inside arbitrarily deep static layouts. -/
theorem compile_inputs_fresh (p : Program WordSig Γ t) (inputs : HList Loc Γ)
    (firstFresh : Nat) (out : Compiled t) (h : compile p inputs firstFresh = .ok out) :
    ∀ r ∈ inputRegs inputs, r < firstFresh := by
  unfold compile at h
  split at h
  · contradiction
  · rename_i hf
    have hs := List.find?_eq_none.mp hf
    simpa using hs

/-- Rendering seam for the actual generated Caliper AST, not a second compiler. -/
def render (compiled : Compiled t) : String := compiled.code.renderString

/-! Universal primitive and layout contracts. -/

@[simp] theorem decode_add (a b : BitVec 64) :
    UInt64.ofBitVec (a + b) = UInt64.ofBitVec a + UInt64.ofBitVec b := rfl
@[simp] theorem decode_mul (a b : BitVec 64) :
    UInt64.ofBitVec (a * b) = UInt64.ofBitVec a * UInt64.ofBitVec b := rfl
@[simp] theorem decode_div (a b : BitVec 64) :
    UInt64.ofBitVec (a / b) = UInt64.ofBitVec a / UInt64.ofBitVec b := rfl
@[simp] theorem decode_mod (a b : BitVec 64) :
    UInt64.ofBitVec (a % b) = UInt64.ofBitVec a % UInt64.ofBitVec b := rfl

/-- The real generated single-instruction program has source semantics, including
wrapping arithmetic and the shared total division/remainder convention at zero. -/
theorem compileWord_correct (op : WordOp args [] t) (xs : HList Loc args)
    (n : Nat) (s : _root_.Caliper.State64) (C : _root_.Caliper.CostModel)
    (tape : _root_.Caliper.RandomTape 64) :
    (_root_.Caliper.run C tape 1 (compileWord op xs n).code s).map
      (fun r => Loc.read (compileWord op xs n).result r.1) =
    some (wordScalarModel.eval op (xs.map (fun x => Loc.read x s)) .nil) := by
  cases op <;> cases_type* HList
  all_goals simp [compileWord, _root_.Caliper.run, Loc.read, wordScalarModel, HList.map]
  rfl

/-- Layout construction/projection commutes with reading the machine state. -/
theorem compileData_correct (op : DataOp args [] t) (xs : HList Loc args)
    (s : _root_.Caliper.State64) :
    Loc.read (compileData op xs) s =
      (dataModel UInt64).eval op (xs.map (fun x => Loc.read x s)) .nil := by
  cases op <;> cases_type* HList
  all_goals simp [compileData, Loc.read, dataModel, HList.map]

/-- Exact compiler results, obtained by checked extraction without any fallback. -/
def quadraticCompiled : Compiled .quad :=
  (compile quadraticWord (.cons 0 (.cons 1 .nil)) 2).toOption.get (by decide)
def modMulCompiled : Compiled .modmul :=
  (compile modMulWord (.cons 0 (.cons 1 (.cons 2 .nil))) 3).toOption.get (by decide)

theorem quadratic_compiles : compile quadraticWord (.cons 0 (.cons 1 .nil)) 2 =
    .ok quadraticCompiled := rfl
theorem modMul_compiles : compile modMulWord (.cons 0 (.cons 1 (.cons 2 .nil))) 3 =
    .ok modMulCompiled := rfl

/-- Constructor equality is checked against the compiler, not a hand-selected target. -/
theorem quadratic_code : quadraticCompiled.code =
    .seq (.bin .mul 2 0 0) (.seq (.imm 3 17) (.seq (.bin .umod 4 2 3)
      (.seq (.bin .add 5 4 1) (.seq (.imm 6 17) (.seq (.bin .umod 7 5 6)
        (.seq .skip .skip)))))) := rfl

theorem modMul_code : modMulCompiled.code =
    .seq (.bin .mul 3 0 1) (.seq (.bin .udiv 4 3 2)
      (.seq (.bin .umod 5 3 2) (.seq .skip .skip))) := rfl

@[simp] theorem quadratic_result : quadraticCompiled.result = ⟨4, 7⟩ := rfl
@[simp] theorem modMul_result : modMulCompiled.result = ⟨3, 4, 5⟩ := rfl

/-- Observe the complete returned value and the actual Caliper cost profile. -/
def observe (c : Compiled t) (r : _root_.Caliper.State64 × Nat × Int × Int) :
    Val UInt64 t × Nat × Int × Int := (Loc.read c.result r.1, r.2)

theorem quadraticWord_eval_u64 (x c : UInt64) :
    quadraticWord.eval wordModel (.cons x (.cons c .nil)) =
    (⟨x * x % 17, (x * x % 17 + c) % 17⟩ : Quad UInt64) := rfl

/-- Universal over *every* initial machine state, tape and cost table. No field
range, no no-overflow assumption, and no constraint on scratch registers. -/
theorem quadratic_run (s : _root_.Caliper.State64) (C : _root_.Caliper.CostModel)
    (tape : _root_.Caliper.RandomTape 64) :
    (_root_.Caliper.run C tape 10 quadraticCompiled.code s).map (observe quadraticCompiled) =
    some (quadraticWord.eval wordModel
      (.cons (UInt64.ofBitVec (s.regs 0)) (.cons (UInt64.ofBitVec (s.regs 1)) .nil)),
      C.bin .mul + (C.imm + (C.bin .umod + (C.bin .add + (C.imm + C.bin .umod)))), 0, 0) := by
  simp [quadratic_code, observe, Loc.read, _root_.Caliper.run,
    _root_.Caliper.State.setReg, quadraticWord_eval_u64]

theorem modMul_run (s : _root_.Caliper.State64) (C : _root_.Caliper.CostModel)
    (tape : _root_.Caliper.RandomTape 64) :
    (_root_.Caliper.run C tape 10 modMulCompiled.code s).map (observe modMulCompiled) =
    some (modMulWord.eval wordModel
      (.cons (UInt64.ofBitVec (s.regs 0)) (.cons (UInt64.ofBitVec (s.regs 1))
        (.cons (UInt64.ofBitVec (s.regs 2)) .nil))),
      C.bin .mul + (C.bin .udiv + C.bin .umod), 0, 0) := by
  simp [modMul_code, observe, Loc.read, _root_.Caliper.run,
    _root_.Caliper.State.setReg, modMulWord_eval]

/-- A shape-preserving gated batch: false emits zero records, not an empty
runtime list. The list length is supplied by the compile-time input layout. -/
def zeroQuadWord : Program WordSig [.scalar, .scalar] .quad :=
  .let_ (.inl (.const 0)) .nil .nil <|
  .let_ (.inr (.inl .quad)) (.cons .zero (.cons .zero .nil)) .nil (.ret .zero)

def mapQuadWord (body : Program WordSig [.scalar, .scalar] .quad) :
    Program WordSig [.list .scalar, .scalar] (.list .quad) :=
  emit (.inr (.inr (.map [.scalar] .scalar .quad))) (.cons body .nil)

def fixedGatedWord : Program WordSig [.bool, .list .scalar, .scalar] (.list .quad) :=
  emit (.inr (.inr (.branch [.list .scalar, .scalar] (.list .quad))))
    (.cons (mapQuadWord quadraticWord) (.cons (mapQuadWord zeroQuadWord) .nil))

def fixedGatedCompiled : Compiled (.list .quad) :=
  (compile fixedGatedWord (.cons 0 (.cons [1, 2] (.cons 3 .nil))) 4).toOption.get (by decide)

theorem fixedGated_compiles :
    compile fixedGatedWord (.cons 0 (.cons [1, 2] (.cons 3 .nil))) 4 =
      .ok fixedGatedCompiled := rfl

@[simp] theorem fixedGated_result :
    fixedGatedCompiled.result = [⟨18, 19⟩, ⟨20, 21⟩] := rfl

theorem fixedGatedWord_eval (b : Bool) (xs : List UInt64) (c : UInt64) :
    fixedGatedWord.eval wordModel (.cons b (.cons xs (.cons c .nil))) =
      if b then xs.map (fun x => (⟨x * x % 17, (x * x % 17 + c) % 17⟩ : Quad UInt64))
      else xs.map (fun _ => (⟨0, 0⟩ : Quad UInt64)) := by cases b <;> rfl

def quadraticTime (C : _root_.Caliper.CostModel) : Nat :=
  C.bin .mul + (C.imm + (C.bin .umod + (C.bin .add + (C.imm + C.bin .umod))))

def fixedGatedTime (C : _root_.Caliper.CostModel) (b : Bool) : Nat :=
  C.branch + (if b then 2 * quadraticTime C else 2 * C.imm) + 4 * C.mov

/-- Complete two-element batch certificate. Every initial state and every cost
model/tape are quantified; both runtime branches and all four returned cells are
covered. The layout fixes the length, but word values are unrestricted. -/
theorem fixedGated_run (s : _root_.Caliper.State64) (C : _root_.Caliper.CostModel)
    (tape : _root_.Caliper.RandomTape 64) :
    (_root_.Caliper.run C tape 40 fixedGatedCompiled.code s).map (observe fixedGatedCompiled) =
      some (fixedGatedWord.eval wordModel
        (.cons (decide (s.regs 0 ≠ 0)) (.cons [UInt64.ofBitVec (s.regs 1), UInt64.ofBitVec (s.regs 2)]
          (.cons (UInt64.ofBitVec (s.regs 3)) .nil))),
        fixedGatedTime C (decide (s.regs 0 ≠ 0)), 0, 0) := by
  conv_lhs => arg 2; arg 4; cbv
  by_cases h : s.regs 0 = 0#64
  all_goals simp [observe, Loc.read, _root_.Caliper.run, _root_.Caliper.State.setReg,
    h, fixedGatedWord_eval, fixedGatedTime, quadraticTime, Nat.mul_add,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals omega

/-- Convert an observed interpreter certificate into Caliper's total execution
relation, retaining all returned cells and the exact resource profile. -/
theorem exec_of_observed_run (c : Compiled t) (s : _root_.Caliper.State64)
    (C : _root_.Caliper.CostModel) (tape : _root_.Caliper.RandomTape 64)
    (fuel time : Nat) (net peak : Int) (value : Val UInt64 t)
    (h : (_root_.Caliper.run C tape fuel c.code s).map (observe c) =
      some (value, time, net, peak)) :
    ∃ s', _root_.Caliper.Exec C tape c.code s s' time net peak ∧ Loc.read c.result s' = value := by
  cases hr : _root_.Caliper.run C tape fuel c.code s with
  | none => simp [hr] at h
  | some r =>
    rcases r with ⟨s', time', net', peak'⟩
    simp only [hr, Option.map_some, Option.some.injEq, observe, Prod.mk.injEq] at h
    rcases h with ⟨hv, ht, hd, hp⟩
    subst time'; subst net'; subst peak'
    exact ⟨s', _root_.Caliper.run_sound fuel c.code hr, hv⟩

/-- Generic scalar frame: primitive compilation never mutates another register. -/
theorem compileWord_frame (op : WordOp args [] t) (xs : HList Loc args)
    (n r : Nat) (h : r ≠ n) (s : _root_.Caliper.State64)
    (C : _root_.Caliper.CostModel) (tape : _root_.Caliper.RandomTape 64) :
    (_root_.Caliper.run C tape 1 (compileWord op xs n).code s).map
      (fun out => out.1.regs r) = some (s.regs r) := by
  cases op <;> cases_type* HList
  all_goals simp [compileWord, _root_.Caliper.run, _root_.Caliper.State.setReg, h]

/-- For the compiled quadratic, all registers outside its fresh allocation are
unchanged; buffers, capacities and tape cursor are likewise unchanged. -/
theorem quadratic_frame (s : _root_.Caliper.State64) (r : Nat) (h : r < 2 ∨ 8 ≤ r)
    (C : _root_.Caliper.CostModel) (tape : _root_.Caliper.RandomTape 64) :
    (_root_.Caliper.run C tape 10 quadraticCompiled.code s).map
      (fun out => (out.1.regs r, out.1.bufs, out.1.caps, out.1.tapePos)) =
        some (s.regs r, s.bufs, s.caps, s.tapePos) := by
  have h2 : r ≠ 2 := by omega
  have h3 : r ≠ 3 := by omega
  have h4 : r ≠ 4 := by omega
  have h5 : r ≠ 5 := by omega
  have h6 : r ≠ 6 := by omega
  have h7 : r ≠ 7 := by omega
  simp [quadratic_code, _root_.Caliper.run, _root_.Caliper.State.setReg, h2, h3, h4, h5, h6, h7]

theorem modMul_frame (s : _root_.Caliper.State64) (r : Nat) (h : r < 3 ∨ 6 ≤ r)
    (C : _root_.Caliper.CostModel) (tape : _root_.Caliper.RandomTape 64) :
    (_root_.Caliper.run C tape 10 modMulCompiled.code s).map
      (fun out => (out.1.regs r, out.1.bufs, out.1.caps, out.1.tapePos)) =
        some (s.regs r, s.bufs, s.caps, s.tapePos) := by
  have h3 : r ≠ 3 := by omega
  have h4 : r ≠ 4 := by omega
  have h5 : r ≠ 5 := by omega
  simp [modMul_code, _root_.Caliper.run, _root_.Caliper.State.setReg, h3, h4, h5]

theorem fixedGated_frame (s : _root_.Caliper.State64) (r : Nat) (h : r < 4 ∨ 22 ≤ r)
    (C : _root_.Caliper.CostModel) (tape : _root_.Caliper.RandomTape 64) :
    (_root_.Caliper.run C tape 40 fixedGatedCompiled.code s).map
      (fun out => (out.1.regs r, out.1.bufs, out.1.caps, out.1.tapePos)) =
        some (s.regs r, s.bufs, s.caps, s.tapePos) := by
  have hne (k : Nat) (lo : 4 ≤ k) (hi : k < 22) : r ≠ k := by omega
  conv_lhs => arg 2; arg 4; cbv
  by_cases hz : s.regs 0 = 0#64
  all_goals simp [hz, _root_.Caliper.run, _root_.Caliper.State.setReg, hne]

theorem quadratic_exec (s : _root_.Caliper.State64) (C : _root_.Caliper.CostModel)
    (tape : _root_.Caliper.RandomTape 64) :
    ∃ s', _root_.Caliper.Exec C tape quadraticCompiled.code s s' (quadraticTime C) 0 0 ∧
      Loc.read quadraticCompiled.result s' = quadraticWord.eval wordModel
        (.cons (UInt64.ofBitVec (s.regs 0)) (.cons (UInt64.ofBitVec (s.regs 1)) .nil)) :=
  exec_of_observed_run _ s C tape 10 _ 0 0 _ (quadratic_run s C tape)

theorem modMul_exec (s : _root_.Caliper.State64) (C : _root_.Caliper.CostModel)
    (tape : _root_.Caliper.RandomTape 64) :
    ∃ s', _root_.Caliper.Exec C tape modMulCompiled.code s s'
      (C.bin .mul + (C.bin .udiv + C.bin .umod)) 0 0 ∧
      Loc.read modMulCompiled.result s' = modMulWord.eval wordModel
        (.cons (UInt64.ofBitVec (s.regs 0)) (.cons (UInt64.ofBitVec (s.regs 1))
          (.cons (UInt64.ofBitVec (s.regs 2)) .nil))) :=
  exec_of_observed_run _ s C tape 10 _ 0 0 _ (modMul_run s C tape)

theorem fixedGated_exec (s : _root_.Caliper.State64) (C : _root_.Caliper.CostModel)
    (tape : _root_.Caliper.RandomTape 64) :
    ∃ s', _root_.Caliper.Exec C tape fixedGatedCompiled.code s s'
      (fixedGatedTime C (decide (s.regs 0 ≠ 0))) 0 0 ∧
      Loc.read fixedGatedCompiled.result s' = fixedGatedWord.eval wordModel
        (.cons (decide (s.regs 0 ≠ 0)) (.cons [UInt64.ofBitVec (s.regs 1), UInt64.ofBitVec (s.regs 2)]
          (.cons (UInt64.ofBitVec (s.regs 3)) .nil))) :=
  exec_of_observed_run _ s C tape 40 _ 0 0 _ (fixedGated_run s C tape)

end Witgen.Backends.Caliper
