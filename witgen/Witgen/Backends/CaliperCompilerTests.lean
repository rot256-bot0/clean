import Witgen.Backends.Caliper

namespace Witgen.Backends.Caliper.Tests
set_option autoImplicit false
open Witgen Demo

private def addProgram : Program WordSig [.scalar, .scalar] .scalar :=
  emit (.inl .add) .nil

-- RED: compile must inspect typed argument references and emit real bin.
example : (compile addProgram (.cons 0 (.cons 1 .nil)) 2).map
    (fun c => c.code == (.seq (.bin .add 2 0 1) .skip)) = .ok true := by decide

example : (compile addProgram (.cons 0 (.cons 1 .nil)) 1).map
    (fun c => c.nextReg) = .error (.inputNotFresh 1 1) := by decide

example : (do
    let c ← compile addProgram (.cons 0 (.cons 1 .nil)) 2
    pure ((Caliper.run .unit .zero 10 c.code
      (((Caliper.State.init 64).setReg 0 7).setReg 1 9)).map
        (fun r : _root_.Caliper.State64 × Nat × Int × Int => (Loc.read c.result r.1, r.2.1)))) = .ok (some (16, 1)) := by decide

/- The fixed-size gated batch is an actual finite source AST, not target code. -/
example : (compile fixedGatedWord (.cons 0 (.cons [1, 2] (.cons 3 .nil))) 4).map
    (fun c => match c.code with | .seq (.ifNZ 0 _ _) .skip => true | _ => false) = .ok true := by decide

example : (_root_.Caliper.run .unit .zero 40 fixedGatedCompiled.code
    ((((_root_.Caliper.State.init 64).setReg 0 1).setReg 1 3).setReg 2 4 |>.setReg 3 2)).map
    (observe fixedGatedCompiled) = some ([⟨9, 11⟩, ⟨16, 1⟩], 17, 0, 0) := by decide

example : (_root_.Caliper.run .unit .zero 40 fixedGatedCompiled.code
    ((((_root_.Caliper.State.init 64).setReg 0 0).setReg 1 3).setReg 2 4 |>.setReg 3 2)).map
    (observe fixedGatedCompiled) = some ([⟨0, 0⟩, ⟨0, 0⟩], 7, 0, 0) := by decide

private def execute {Γ : List Ty} {t : Ty} (p : Program WordSig Γ t)
    (inputs : HList Loc Γ) (fresh : Nat) (s : _root_.Caliper.State64) :
    Except CompileError (Option (Val UInt64 t × Nat × Int × Int)) := do
  let c ← compile p inputs fresh
  pure ((_root_.Caliper.run .unit .zero 100 c.code s).map (observe c))

private def binary (op : WordOp [.scalar, .scalar] [] .scalar) :=
  emit (F := WordSig) (.inl op) .nil
private def pairInputs : HList Loc [.scalar, .scalar] := .cons 0 (.cons 1 .nil)
private def pairState (x y : BitVec 64) : _root_.Caliper.State64 :=
  ((_root_.Caliper.State.init 64).setReg 0 x).setReg 1 y

-- Wrapping, zero-divisor and comparison conventions exercise actual generated bin.
example : execute (binary .add) pairInputs 2 (pairState 0xffffffffffffffff 1) =
    .ok (some (0, 1, 0, 0)) := by decide
example : execute (binary .mul) pairInputs 2 (pairState 0xffffffffffffffff 2) =
    .ok (some (0xfffffffffffffffe, 1, 0, 0)) := by decide
example : execute (binary .div) pairInputs 2 (pairState 23 0) =
    .ok (some (0, 1, 0, 0)) := by decide
example : execute (binary .mod) pairInputs 2 (pairState 23 0) =
    .ok (some (23, 1, 0, 0)) := by decide
example : execute (emit (F := WordSig) (.inl (.const 0x10000000000000005)) .nil)
    .nil 0 (_root_.Caliper.State.init 64) = .ok (some (5, 1, 0, 0)) := by decide
example : execute (emit (F := WordSig) (.inl .eq) .nil) pairInputs 2 (pairState 23 23) =
    .ok (some (true, 1, 0, 0)) := by decide
example : execute (emit (F := WordSig) (.inl .eq) .nil) pairInputs 2 (pairState 23 24) =
    .ok (some (false, 1, 0, 0)) := by decide

-- Aliasing source operands is legal; the new result never replaces the source.
private def readOld : Program WordSig [.scalar] .scalar :=
  .let_ (.inl .mul) (.cons .zero (.cons .zero .nil)) .nil (.ret (.succ .zero))
example : execute readOld (.cons 5 .nil) 6 ((_root_.Caliper.State.init 64).setReg 5 7) =
    .ok (some (7, 1, 0, 0)) := by decide
example : execute addProgram (.cons 0 (.cons 0 .nil)) 1 (pairState 7 100) =
    .ok (some (14, 1, 0, 0)) := by decide

-- Captured c is read on each unrolled iteration, never replaced by earlier output.
example : execute (mapQuadWord quadraticWord) (.cons [0, 1] (.cons 2 .nil)) 3
    ((pairState 3 4).setReg 2 2) = .ok (some ([⟨9, 11⟩, ⟨16, 1⟩], 12, 0, 0)) := by decide
example : execute (mapQuadWord quadraticWord) (.cons [] (.cons 0 .nil)) 1
    (pairState 3 4) = .ok (some ([], 0, 0, 0)) := by decide
-- Actual map-to-fold transformed AST grows a compile-time list accumulator.
example : execute ((mapQuadWord quadraticWord).lower (mapToFold WordOp))
    (.cons [0, 1] (.cons 2 .nil)) 3 ((pairState 3 4).setReg 2 2) =
    .ok (some ([⟨9, 11⟩, ⟨16, 1⟩], 12, 0, 0)) := by decide

private def foldBody : Program WordSig [.scalar, .scalar, .scalar] .scalar :=
  .let_ (.inl .add) (.cons .zero (.cons (.succ .zero) .nil)) .nil <|
  .let_ (.inl .add) (.cons .zero (.cons (.succ (.succ (.succ .zero))) .nil)) .nil (.ret .zero)
private def foldCaptured : Program WordSig [.list .scalar, .scalar, .scalar] .scalar :=
  emit (.inr (.inr (.fold [.scalar] .scalar .scalar))) (.cons foldBody .nil)
example : execute foldCaptured (.cons [0, 1] (.cons 2 (.cons 3 .nil))) 4
    (((pairState 3 4).setReg 2 10).setReg 3 2) = .ok (some (21, 4, 0, 0)) := by decide

-- The original conditional batch has runtime-dependent result length: reject it.
private def dynamicBatch := conditionalBatchField.lower fieldToWord
example : (compile dynamicBatch (.cons 0 (.cons [1] (.cons 2 .nil))) 3).map
    (fun c => c.nextReg) = .error .branchShapeMismatch := by decide
example : (compile dynamicBatch (.cons 0 (.cons [] (.cons 2 .nil))) 3).map
    (fun c => c.nextReg) = .ok 3 := by decide
-- Equal flattened counts do not make incompatible nested shapes compatible.
example : (join (t := .list (.list .scalar)) [[0], [1]] [[2, 3], []] 4).map
    (fun j => j.nextReg) = .error .branchShapeMismatch := by decide
-- Freshness inspection descends into every nested record/list location.
example : (compile (Program.ret (F := WordSig) (Γ := [.list (.list .modmul)]) .zero)
    (.cons [[⟨0, 1, 9⟩]] .nil) 9).map (fun c => c.nextReg) =
      .error (.inputNotFresh 9 9) := by decide

private def branchThenAdd : Program WordSig [.bool, .scalar, .scalar] .scalar :=
  .let_ (.inr (.inr (.branch [.scalar, .scalar] .scalar))) (refs _)
    (.cons (.ret .zero) (.cons (.ret (.succ .zero)) .nil)) <|
  .let_ (.inl .add) (.cons .zero (.cons (.succ (.succ .zero)) .nil)) .nil (.ret .zero)
example : execute branchThenAdd (.cons 0 (.cons 1 (.cons 2 .nil))) 3
    ((pairState 2 7).setReg 2 100) = .ok (some (14, 3, 0, 0)) := by decide
example : execute branchThenAdd (.cons 0 (.cons 1 (.cons 2 .nil))) 3
    ((pairState 0 7).setReg 2 100) = .ok (some (107, 3, 0, 0)) := by decide

example : (quadraticCompiled.nextReg, modMulCompiled.nextReg, fixedGatedCompiled.nextReg) =
    (8, 6, 22) := rfl
-- Runtime renderer test: pretty-printing is not a kernel-computable theorem.
#eval show IO Unit from do
  unless render modMulCompiled == "mul  r3, r0, r1\nudiv r4, r3, r2\numod r5, r3, r2\nskip\nskip" do
    throw (IO.userError "renderer must use Caliper's own assembly dialect")

#print axioms compile_inputs_fresh
#print axioms compileWord_correct
#print axioms compileAggregate_correct
#print axioms compileWord_frame
#print axioms quadratic_run
#print axioms modMul_run
#print axioms fixedGated_run
#print axioms quadratic_frame
#print axioms modMul_frame
#print axioms exec_of_observed_run
#print axioms fixedGated_frame
#print axioms quadratic_exec
#print axioms modMul_exec
#print axioms fixedGated_exec
#print axioms quadratic_compiles
#print axioms modMul_compiles
#print axioms fixedGated_compiles

end Witgen.Backends.Caliper.Tests
