import Witgen.Backends.CaliperWitness
import Witgen.Backends.CaliperExamples

open Caliper Witgen.Backends.CaliperWitness

-- Reference interpreter checks: observable result, not a surrogate evaluator.
#guard (run .unit RandomTape.zero 20 (writeRegs (w := 64) 7 [2, 0, 2])
  ((State.init 64).setReg 2 42)).map
  (fun (s, t, d, p) => (s.bufs 7, s.caps 7, s.regs 2, t, d, p)) =
  some (#[42, 0, 42], 3, 42, 6, 3, 3)

#guard (run .cycles RandomTape.zero 20 (writeRegs (w := 64) 7 [2, 0, 2])
  ((State.init 64).setReg 2 42)).map
  (fun (s, t, d, p) => (s.bufs 7, t, d, p)) = some (#[42, 0, 42], 18, 3, 3)

#guard (run .unit RandomTape.zero 20 (writeRegs (w := 64) 7 []) (State.init 64)).map
  (fun (s, t, d, p) => (s.bufs 7, s.caps 7, t, d, p)) = some (#[], 0, 0, 0, 0)

-- Acquiring capacity does not create readable or storable cells.
#guard (run .unit RandomTape.zero 20
  (.seq (.memAllocI 0 4) (.memLoad 1 0 0)) (State.init 64)).isNone
#guard (run .unit RandomTape.zero 20
  (.seq (.memAllocI 0 4) (.memStore 0 0 1)) (State.init 64)).isNone

-- No implicit allocation/growth, including deliberately malformed overfull states.
#guard (run .unit RandomTape.zero 20 (.memPush 0 0) (State.init 64)).isNone
#guard (run .unit RandomTape.zero 20
  (.seq (writeRegs 0 [0]) (.memPush 0 0)) (State.init 64)).isNone
#guard (run .unit RandomTape.zero 20 (.memPush 0 0)
  ((State.init 64).setBuf 0 #[1, 2])).isNone

-- Filled size, not capacity, bounds load indices.
#guard (run .unit RandomTape.zero 20
  (.seq (writeRegs 0 [0]) (.seq (.imm 1 1) (.memLoad 2 0 1))) (State.init 64)).isNone
#guard (run .unit RandomTape.zero 20
  (.seq (writeRegs 0 [2]) (.memLoad 1 0 0)) ((State.init 64).setReg 2 42)).map
  (fun (s, t, d, p) => (s.regs 1, t, d, p)) = some (42, 3, 1, 1)

-- Raw `run` is not a global state validator. Physical-memory theorems require
-- WellFormed; a malformed irrelevant buffer does not make `skip` fail.
#guard (run .unit RandomTape.zero 20 .skip ((State.init 64).setBuf 0 #[1])).isSome

#eval (run .unit RandomTape.zero 20 (writeRegs (w := 64) 7 [2, 0, 2])
  ((State.init 64).setReg 2 42)).map
  (fun (s, t, d, p) => (s.bufs 7, s.caps 7, t, d, p))

#print axioms writeRegs_exec
#print axioms writeRegs_triple
#print axioms writeRegs_reaches_bound
#print axioms reserved_load_noExec
#print axioms full_push_noExec

open Witgen.Backends.CaliperExamples

#guard (run .unit RandomTape.zero 100 (quadraticCode 0)
  (((State.init 64).setReg 0 3).setReg 1 5)).map
  (fun (s, t, d, p) => ((s.bufs 0).map BitVec.toNat, t, d, p)) =
  some (#[3, 5, 9, 14], 14, 4, 4)
#guard (run .unit RandomTape.zero 100 (modMulCode 0)
  ((((State.init 64).setReg 0 7).setReg 1 9).setReg 2 11)).map
  (fun (s, t, d, p) => ((s.bufs 0).map BitVec.toNat, t, d, p)) =
  some (#[7, 9, 11, 63, 5, 8], 15, 6, 6)

-- Next vertical slice: complete two-row gated output, including disabled zeros.
#guard (run .unit RandomTape.zero 100 (fixedGatedCode 0)
  (((((State.init 64).setReg 0 1).setReg 1 3).setReg 2 4).setReg 3 5)).map
  (fun (s, t, d, p) => ((s.bufs 0).map BitVec.toNat, t, d, p)) =
  some (#[1, 3, 4, 5, 9, 14, 16, 4], 33, 8, 8)

namespace CaliperValidation

def quadState (x y : Nat) : State 64 :=
  ((State.init 64).setReg 0 (BitVec.ofNat 64 x)).setReg 1 (BitVec.ofNat 64 y)
def mulState (a b n : Nat) : State 64 :=
  (((State.init 64).setReg 0 (BitVec.ofNat 64 a)).setReg 1 (BitVec.ofNat 64 b)).setReg 2 (BitVec.ofNat 64 n)
def gatedState (flag x y c : Nat) : State 64 :=
  ((((State.init 64).setReg 0 (BitVec.ofNat 64 flag)).setReg 1 (BitVec.ofNat 64 x)).setReg 2
    (BitVec.ofNat 64 y)).setReg 3 (BitVec.ofNat 64 c)

def receipt (C : CostModel) (code : Stmt 64) (s : State 64) : Option (Array Nat × Nat × Int × Int) :=
  (run C RandomTape.zero 100 code s).map (fun (s', t, d, p) => ((s'.bufs 0).map BitVec.toNat, t, d, p))

#guard receipt .cycles (quadraticCode 0) (quadState 3 5) = some (#[3, 5, 9, 14], 90, 4, 4)
#guard receipt .cycles (modMulCode 0) (mulState 7 9 11) = some (#[7, 9, 11, 63, 5, 8], 99, 6, 6)
#guard receipt .unit (fixedGatedCode 0) (gatedState 0 3 4 5) = some (#[0, 3, 4, 5, 0, 0, 0, 0], 23, 8, 8)
#guard receipt .cycles (fixedGatedCode 0) (gatedState 1 3 4 5) = some (#[1, 3, 4, 5, 9, 14, 16, 4], 186, 8, 8)
#guard receipt .cycles (fixedGatedCode 0) (gatedState 0 3 4 5) = some (#[0, 3, 4, 5, 0, 0, 0, 0], 56, 8, 8)

-- Exhaustive small circuit domains are runtime validation, not the universal proofs.
def quadCases : List (State 64) := (List.range 17).flatMap fun x => (List.range 17).map (quadState x)
def mulCases : List (State 64) := (List.range 17).flatMap fun n =>
  (List.range n).flatMap fun a => (List.range n).map fun b => mulState a b n
#guard quadCases.all (fun s => receipt .unit (quadraticCode 0) s ==
  some ((quadraticCells s).map UInt64.toNat, 14, 4, 4))
#guard mulCases.all (fun s => receipt .unit (modMulCode 0) s ==
  some ((modMulCells s).map UInt64.toNat, 15, 6, 6))

-- Word-level execution includes division by zero and wrapping products. These
-- inputs are deliberately OUTSIDE the stronger Nat circuit theorem's assumptions.
#guard [mulState 7 9 0, mulState (2^64 - 1) 2 17, mulState (2^64 - 1) (2^64 - 1) 1].all
  (fun s => receipt .unit (modMulCode 0) s == some ((modMulCells s).map UInt64.toNat, 15, 6, 6))
#guard [quadState (2^64 - 1) (2^64 - 1), quadState 0 0].all
  (fun s => receipt .unit (quadraticCode 0) s == some ((quadraticCells s).map UInt64.toNat, 14, 4, 4))
#guard [0, 1, 2, 2^64 - 1].all (fun flag =>
  let s := gatedState flag 16 15 16
  receipt .unit (fixedGatedCode 0) s ==
    some ((fixedGatedCells s).map UInt64.toNat, if flag == 0 then 23 else 33, 8, 8))

#eval ("exhaustive domains", quadCases.length, mulCases.length)
#eval ("quadratic/unit", receipt .unit (quadraticCode 0) (quadState 3 5))
#eval ("quadratic/cycles", receipt .cycles (quadraticCode 0) (quadState 3 5))
#eval ("modMul/unit", receipt .unit (modMulCode 0) (mulState 7 9 11))
#eval ("modMul/cycles", receipt .cycles (modMulCode 0) (mulState 7 9 11))
#eval ("gated/on/unit", receipt .unit (fixedGatedCode 0) (gatedState 1 3 4 5))
#eval ("gated/off/unit", receipt .unit (fixedGatedCode 0) (gatedState 0 3 4 5))
#eval ("gated/on/cycles", receipt .cycles (fixedGatedCode 0) (gatedState 1 3 4 5))
#eval ("gated/off/cycles", receipt .cycles (fixedGatedCode 0) (gatedState 0 3 4 5))

end CaliperValidation

#print axioms quadratic_witness_exec
#print axioms modMul_witness_exec
#print axioms quadratic_triple
#print axioms modMul_triple
#print axioms quadratic_circuit_exec
#print axioms modMul_circuit_exec
#print axioms fixedGated_witness_exec
#print axioms fixedGated_unit_triple
#print axioms fixedGated_cycles_triple
#print axioms compiled_register_endpoints
#print axioms quadratic_intermediate_memory
#print axioms modMul_intermediate_memory
