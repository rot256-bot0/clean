import Lean
import Witgen.Backends.CaliperExamples

/-! Executable export of the actual checked compiler output plus witness writer.
JSON and assembly rendering are tested serialization, not kernel theorems. -/
set_option autoImplicit false

namespace Witgen.Backends.CaliperExport
open Lean _root_.Caliper

structure Artifact where
  name : String
  ty : Witgen.Demo.Ty
  compiled : Caliper.Compiled ty
  code : Stmt 64
  inputRegisters : List Reg
  samples : List (String × List Nat)
  validationInputs : List (List Nat)
  sourceCells : State 64 → Array UInt64

def artifacts : List Artifact := [
  ⟨"quadratic", .quad, Caliper.quadraticCompiled, CaliperExamples.quadraticCode 0,
    [0, 1], [("quadratic", [3, 5])],
    (List.range 17).flatMap (fun x => (List.range 17).map (fun y => [x, y])),
    CaliperExamples.quadraticCells⟩,
  ⟨"modMul", .modmul, Caliper.modMulCompiled, CaliperExamples.modMulCode 0,
    [0, 1, 2], [("modMul", [7, 9, 11])],
    (List.range 17).flatMap (fun n => (List.range n).flatMap
      (fun a => (List.range n).map (fun b => [a, b, n]))),
    CaliperExamples.modMulCells⟩,
  ⟨"fixedGated", .list .quad, Caliper.fixedGatedCompiled, CaliperExamples.fixedGatedCode 0,
    [0, 1, 2, 3], [("fixedGated/on", [1, 3, 4, 5]), ("fixedGated/off", [0, 3, 4, 5])],
    [], CaliperExamples.fixedGatedCells⟩]

def initialState (a : Artifact) (values : List Nat) : State 64 :=
  (a.inputRegisters.zip values).foldl
    (fun s (r, v) => s.setReg r (BitVec.ofNat 64 v)) (State.init 64)

/-- Every observation is read from a successful invocation of pinned `Caliper.run`. -/
def runJson (a : Artifact) (label : String) (values : List Nat)
    (costName : String) (cost : CostModel) : IO Json := do
  unless values.length == a.inputRegisters.length do
    throw (IO.userError "input layout length mismatch")
  let s := initialState a values
  match _root_.Caliper.run cost RandomTape.zero 100 a.code s with
  | none => throw (IO.userError s!"Caliper.run failed: {label}/{costName}")
  | some (s', time, net, peak) => do
    unless (s'.bufs 0).map UInt64.ofBitVec == a.sourceCells s do
      throw (IO.userError s!"full source-cell mismatch: {label}/{costName}")
    return Json.mkObj [
      ("case", toJson label), ("cost_model", toJson costName),
      ("input_values", toJson (a.inputRegisters.map (fun r => (s.regs r).toNat))),
      ("final_input_values", toJson (a.inputRegisters.map (fun r => (s'.regs r).toNat))),
      ("output_values", toJson ((Caliper.Loc.regs a.compiled.result).map
        (fun r => (s'.regs r).toNat))),
      ("final_registers", toJson ((List.range a.compiled.nextReg).map
        (fun r => (s'.regs r).toNat))),
      ("cells", toJson ((s'.bufs 0).map BitVec.toNat)),
      ("capacity", toJson (s'.caps 0)), ("tape_position", toJson s'.tapePos),
      ("time", toJson time), ("net_words", toJson net), ("peak_words", toJson peak)]

def programJson (a : Artifact) : IO Json := do
  let mut runs : Array Json := #[]
  for (label, values) in a.samples do
    for (costName, cost) in [("unit", CostModel.unit), ("cycles", CostModel.cycles)] do
      runs := runs.push (← runJson a label values costName cost)
  return Json.mkObj [
    ("name", toJson a.name), ("assembly", toJson a.code.renderString),
    ("input_registers", toJson a.inputRegisters),
    ("output_registers", toJson (Caliper.Loc.regs a.compiled.result)),
    ("first_fresh_register", toJson a.inputRegisters.length),
    ("next_register", toJson a.compiled.nextReg), ("buffer", toJson (0 : Nat)),
    ("runs", .arr runs)]

def validationJson (a : Artifact) : IO Json := do
  let mut runs : Array Json := #[]
  for values in a.validationInputs do
    for (costName, cost) in [("unit", CostModel.unit), ("cycles", CostModel.cycles)] do
      runs := runs.push (← runJson a (a.name ++ "/finite") values costName cost)
  return Json.mkObj [("name", toJson a.name), ("runs", .arr runs)]

def exportAll (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  let mut programs : Array Json := #[]
  let mut validations : Array Json := #[]
  for a in artifacts do
    let program ← programJson a
    programs := programs.push program
    validations := validations.push (← validationJson a)
    IO.FS.writeFile (directory / (a.name ++ ".caliper")) (a.code.renderString ++ "\n")
  let runtime := Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("interpreter", toJson "Caliper.run"),
    ("renderer", toJson "Caliper.Stmt.renderString"), ("word_bits", toJson (64 : Nat)),
    ("fuel", toJson (100 : Nat)), ("tape", toJson "Caliper.RandomTape.zero"),
    ("initial_state", toJson "Caliper.State.init 64 with the listed input registers set"),
    ("programs", .arr programs)]
  IO.FS.writeFile (directory / "runtime.json") (runtime.pretty ++ "\n")
  IO.FS.writeFile (directory / "validation.json")
    ((Json.mkObj [("interpreter", toJson "Caliper.run"), ("programs", .arr validations)]).compress ++ "\n")
  IO.println (Json.mkObj [("programs", toJson programs.size)]).compress

end Witgen.Backends.CaliperExport

def main (args : List String) : IO UInt32 := do
  match args with
  | ["export", directory] => Witgen.Backends.CaliperExport.exportAll directory; return 0
  | _ =>
    IO.eprintln "usage: witgen-caliper export DIR"
    return 1
