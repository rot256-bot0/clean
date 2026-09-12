import Witgen.Backends.Caliper
import Witgen.Backends.CaliperWitness
import Witgen.Integration

/-! Actual compiler artifacts with complete input-plus-witness buffers.
Caliper resource claims are separate from native Rust evaluation. -/
namespace Witgen.Backends.CaliperExamples
open _root_.Caliper Witgen Demo CaliperWitness

/-- Full circuit layout: immutable input bindings, followed by every witness cell. -/
def withWitness {t : Ty} (c : Caliper.Compiled t) (b : BufId) (inputs : List Reg) : Stmt 64 :=
  c.code ;; writeRegs b (inputs ++ Caliper.Loc.regs c.result)

def quadraticCode (b : BufId) : Stmt 64 := withWitness Caliper.quadraticCompiled b [0, 1]
def modMulCode (b : BufId) : Stmt 64 := withWitness Caliper.modMulCompiled b [0, 1, 2]

def quadraticTime (C : CostModel) : Nat :=
  C.bin .mul + (C.imm + (C.bin .umod + (C.bin .add + (C.imm + C.bin .umod))))
def modMulTime (C : CostModel) : Nat := C.bin .mul + (C.bin .udiv + C.bin .umod)

def quadraticValue (s : State 64) : Quad UInt64 :=
  quadraticWord.eval wordModel
    (.cons (UInt64.ofBitVec (s.regs 0)) (.cons (UInt64.ofBitVec (s.regs 1)) .nil))
def modMulValue (s : State 64) : Demo.ModMul UInt64 :=
  modMulWord.eval wordModel
    (.cons (UInt64.ofBitVec (s.regs 0)) (.cons (UInt64.ofBitVec (s.regs 1))
      (.cons (UInt64.ofBitVec (s.regs 2)) .nil)))

/-- Expected full layout is independent of the writer implementation. -/
def quadraticCells (s : State 64) : Array UInt64 :=
  #[UInt64.ofBitVec (s.regs 0), UInt64.ofBitVec (s.regs 1),
    (quadraticValue s).square, (quadraticValue s).output]
def modMulCells (s : State 64) : Array UInt64 :=
  #[UInt64.ofBitVec (s.regs 0), UInt64.ofBitVec (s.regs 1), UInt64.ofBitVec (s.regs 2),
    (modMulValue s).product, (modMulValue s).quotient, (modMulValue s).remainder]

/-- Extract a terminating execution from the compiler's universal run theorem.
No native decision procedure is involved: the reference interpreter is proved sound. -/
theorem quadratic_producer_exec (s : State 64) (C : CostModel) (tape : RandomTape 64) :
    ∃ s', Exec C tape Caliper.quadraticCompiled.code s s' (quadraticTime C) 0 0 ∧
      Caliper.Loc.read Caliper.quadraticCompiled.result s' = quadraticValue s :=
  Caliper.quadratic_exec s C tape

theorem modMul_producer_exec (s : State 64) (C : CostModel) (tape : RandomTape 64) :
    ∃ s', Exec C tape Caliper.modMulCompiled.code s s' (modMulTime C) 0 0 ∧
      Caliper.Loc.read Caliper.modMulCompiled.result s' = modMulValue s :=
  Caliper.modMul_exec s C tape

/-- Full-layout result, buffer frame, input register preservation, and tape frame. -/
def OutputPost (s : State 64) (b : BufId) (inputs : List Reg)
    (cells : Array UInt64) (s' : State 64) : Prop :=
  (s'.bufs b).map UInt64.ofBitVec = cells ∧ s'.caps b = cells.size ∧
  (∀ r ∈ inputs, s'.regs r = s.regs r) ∧ s'.tapePos = s.tapePos ∧
  (∀ q, q ≠ b → s'.bufs q = s.bufs q ∧ s'.caps q = s.caps q)

/-- Reusable producer-to-buffer rule. Source values must be related to all copied
cells; untouched-register and buffer obligations are syntactic Caliper predicates. -/
theorem withWitness_exec {t : Ty} (c : Caliper.Compiled t) (s s₁ : State 64)
    (C : CostModel) (tape : RandomTape 64) (T : Nat) (b : BufId) (inputs : List Reg)
    (cells : Array UInt64)
    (hc : Exec C tape c.code s s₁ T 0 0) (hfresh : s.caps b = 0)
    (hbuf : ∀ q, ¬ c.code.Touches q) (hrand : c.code.RandomFree)
    (hinputs : ∀ r ∈ inputs, ¬ c.code.Writes r)
    (hcells : ((inputs ++ Caliper.Loc.regs c.result).map
      (fun r => UInt64.ofBitVec (s₁.regs r))).toArray = cells) :
    ∃ s', Exec C tape (withWitness c b inputs) s s'
        (T + writerTime C (inputs ++ Caliper.Loc.regs c.result))
        (inputs ++ Caliper.Loc.regs c.result).length
        (inputs ++ Caliper.Loc.regs c.result).length ∧
      OutputPost s b inputs cells s' := by
  let rs := inputs ++ Caliper.Loc.regs c.result
  have hf : s₁.caps b = 0 := (hc.frame_cap (hbuf b)).trans hfresh
  refine ⟨writerState s₁ b rs, produce_write_exec C tape c.code s s₁ T b rs hc hf, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [rs, List.map_map, Function.comp_def] using hcells
  · have hl := congrArg Array.size hcells
    simpa [rs] using hl
  · intro r hr
    rw [writerState_regs]
    exact hc.frame_reg (hinputs r hr)
  · rw [writerState_tapePos]
    exact hc.tapePos_eq_of_randomFree hrand
  · intro q hq
    obtain ⟨hqb, hqc⟩ := writerState_other s₁ b rs q hq
    exact ⟨hqb.trans (hc.frame_buf (hbuf q)), hqc.trans (hc.frame_cap (hbuf q))⟩

/-- Every input state (including arbitrary scratch-register values), every tape,
and every cost model; all four actual circuit cells are initialized. -/
theorem quadratic_witness_exec (s : State 64) (C : CostModel) (tape : RandomTape 64)
    (b : BufId) (hfresh : s.caps b = 0) :
    ∃ s', Exec C tape (quadraticCode b) s s'
        (quadraticTime C + writerTime C [0, 1, 4, 7]) 4 4 ∧
      OutputPost s b [0, 1] (quadraticCells s) s' := by
  obtain ⟨s₁, hc, hv⟩ := quadratic_producer_exec s C tape
  apply withWitness_exec Caliper.quadraticCompiled s s₁ C tape (quadraticTime C) b [0, 1]
    (quadraticCells s) hc hfresh
  · intro q; simp [Caliper.quadratic_code, Stmt.Touches]
  · simp [Caliper.quadratic_code, Stmt.RandomFree]
  · intro r hr; simp at hr
    rcases hr with rfl | rfl <;> simp [Caliper.quadratic_code, Stmt.Writes]
  · have h0 := hc.frame_reg (r := 0) (by simp [Caliper.quadratic_code, Stmt.Writes])
    have h1 := hc.frame_reg (r := 1) (by simp [Caliper.quadratic_code, Stmt.Writes])
    have hv0 := congrArg Quad.square hv
    have hv1 := congrArg Quad.output hv
    simp [Caliper.Loc.regs, Caliper.Loc.read, quadraticCells, h0, h1,
      ← hv0, ← hv1]

/-- The complete modular-multiplication record includes the product and quotient,
not only the public remainder. Word semantics cover zero divisor and wraparound. -/
theorem modMul_witness_exec (s : State 64) (C : CostModel) (tape : RandomTape 64)
    (b : BufId) (hfresh : s.caps b = 0) :
    ∃ s', Exec C tape (modMulCode b) s s'
        (modMulTime C + writerTime C [0, 1, 2, 3, 4, 5]) 6 6 ∧
      OutputPost s b [0, 1, 2] (modMulCells s) s' := by
  obtain ⟨s₁, hc, hv⟩ := modMul_producer_exec s C tape
  apply withWitness_exec Caliper.modMulCompiled s s₁ C tape (modMulTime C) b [0, 1, 2]
    (modMulCells s) hc hfresh
  · intro q; simp [Caliper.modMul_code, Stmt.Touches]
  · simp [Caliper.modMul_code, Stmt.RandomFree]
  · intro r hr; simp at hr
    rcases hr with rfl | rfl | rfl <;> simp [Caliper.modMul_code, Stmt.Writes]
  · have h0 := hc.frame_reg (r := 0) (by simp [Caliper.modMul_code, Stmt.Writes])
    have h1 := hc.frame_reg (r := 1) (by simp [Caliper.modMul_code, Stmt.Writes])
    have h2 := hc.frame_reg (r := 2) (by simp [Caliper.modMul_code, Stmt.Writes])
    have hv0 := congrArg Demo.ModMul.product hv
    have hv1 := congrArg Demo.ModMul.quotient hv
    have hv2 := congrArg Demo.ModMul.remainder hv
    simp [Caliper.Loc.regs, Caliper.Loc.read, modMulCells, h0, h1, h2,
      ← hv0, ← hv1, ← hv2]

/-- Total correctness for physical memory: arbitrary well-formed initial buffers,
fresh output name, and arbitrary values in all registers. -/
theorem quadratic_triple (C : CostModel) (tape : RandomTape 64) (s₀ : State 64) (b : BufId) :
    Triple C tape (fun s => s = s₀ ∧ s.WellFormed ∧ s.caps b = 0)
      (quadraticCode b)
      (fun s' => OutputPost s₀ b [0, 1] (quadraticCells s₀) s' ∧ s'.WellFormed)
      (quadraticTime C + writerTime C [0, 1, 4, 7]) 4 4 := by
  rintro s ⟨rfl, hwf, hfresh⟩
  obtain ⟨s', he, hp⟩ := quadratic_witness_exec s C tape b hfresh
  exact ⟨s', _, _, _, he, ⟨hp, he.wellFormed_preserved hwf⟩, le_rfl, le_rfl, le_rfl⟩

theorem modMul_triple (C : CostModel) (tape : RandomTape 64) (s₀ : State 64) (b : BufId) :
    Triple C tape (fun s => s = s₀ ∧ s.WellFormed ∧ s.caps b = 0)
      (modMulCode b)
      (fun s' => OutputPost s₀ b [0, 1, 2] (modMulCells s₀) s' ∧ s'.WellFormed)
      (modMulTime C + writerTime C [0, 1, 2, 3, 4, 5]) 6 6 := by
  rintro s ⟨rfl, hwf, hfresh⟩
  obtain ⟨s', he, hp⟩ := modMul_witness_exec s C tape b hfresh
  exact ⟨s', _, _, _, he, ⟨hp, he.wellFormed_preserved hwf⟩, le_rfl, le_rfl, le_rfl⟩

@[simp] theorem quadratic_unit_cost : quadraticTime .unit + writerTime .unit [0, 1, 4, 7] = 14 := rfl
@[simp] theorem quadratic_cycles_cost : quadraticTime .cycles + writerTime .cycles [0, 1, 4, 7] = 90 := rfl
@[simp] theorem modMul_unit_cost : modMulTime .unit + writerTime .unit [0, 1, 2, 3, 4, 5] = 15 := rfl
@[simp] theorem modMul_cycles_cost : modMulTime .cycles + writerTime .cycles [0, 1, 2, 3, 4, 5] = 99 := rfl

/-- Exact, not only upper bounds: determinism pins every complete execution. -/
theorem quadratic_unit_resources (s s' : State 64) (tape : RandomTape 64)
    (b : BufId) (hfresh : s.caps b = 0) (t : Nat) (d p : Int)
    (h : Exec .unit tape (quadraticCode b) s s' t d p) :
    t = 14 ∧ d = 4 ∧ p = 4 := by
  obtain ⟨_, he, _⟩ := quadratic_witness_exec s .unit tape b hfresh
  have hd := h.deterministic he
  exact ⟨hd.2.1.trans quadratic_unit_cost, hd.2.2.1, hd.2.2.2⟩

theorem modMul_unit_resources (s s' : State 64) (tape : RandomTape 64)
    (b : BufId) (hfresh : s.caps b = 0) (t : Nat) (d p : Int)
    (h : Exec .unit tape (modMulCode b) s s' t d p) :
    t = 15 ∧ d = 6 ∧ p = 6 := by
  obtain ⟨_, he, _⟩ := modMul_witness_exec s .unit tape b hfresh
  have hd := h.deterministic he
  exact ⟨hd.2.1.trans modMul_unit_cost, hd.2.2.1, hd.2.2.2⟩

/-- The full Caliper buffer matches the existing generator-independent circuit
layout, not just its public output. Field17 inputs supply the no-overflow image. -/
theorem quadratic_cells_circuit (s : State 64) (i : Circuits.Quadratic.Input)
    (hx : UInt64.ofBitVec (s.regs 0) = fieldWord i.x)
    (hy : UInt64.ofBitVec (s.regs 1) = fieldWord i.y) :
    (quadraticCells s).map UInt64.toNat =
      (Circuits.Quadratic.populate (Circuits.Quadratic.initial i) (Circuits.Quadratic.gen i)).toArray := by
  simp [quadraticCells, quadraticValue, hx, hy, quadraticWord_eval, fieldWord_toNat,
    Circuits.Quadratic.populate, Circuits.Quadratic.initial, Circuits.Quadratic.gen]

/-- ModMul's Nat circuit guarantee needs its explicit small positive modulus and
canonical operands; arbitrary word inputs still have the word-level Exec theorem. -/
theorem modMul_cells_circuit (s : State 64) (i : Circuits.ModMul.Input)
    (hi : Circuits.ModMul.Assumptions i)
    (ha : UInt64.ofBitVec (s.regs 0) = UInt64.ofNat i.a)
    (hb : UInt64.ofBitVec (s.regs 1) = UInt64.ofNat i.b)
    (hn : UInt64.ofBitVec (s.regs 2) = UInt64.ofNat i.n) :
    (modMulCells s).map UInt64.toNat =
      (Circuits.ModMul.populate (Circuits.ModMul.initial i) (Circuits.ModMul.gen i)).toArray := by
  have hsmall : Arithmetic.SmallModulus i.n := ⟨hi.1, Nat.le_trans hi.2.1 (by decide)⟩
  have h := modMulWord_small_correct hsmall hi.2.2.1 hi.2.2.2
  have hp := congrArg Demo.ModMul.product h
  have hq := congrArg Demo.ModMul.quotient h
  have hr := congrArg Demo.ModMul.remainder h
  have hna := Arithmetic.u64_ofNat_toNat (Arithmetic.lt_small_modulus_fits hsmall hi.2.2.1)
  have hnb := Arithmetic.u64_ofNat_toNat (Arithmetic.lt_small_modulus_fits hsmall hi.2.2.2)
  have hnn := Arithmetic.u64_ofNat_toNat (Arithmetic.small_modulus_fits hsmall)
  simp [modMulCells, modMulValue, ha, hb, hn,
    Circuits.ModMul.populate, Circuits.ModMul.initial, Circuits.ModMul.gen, hna, hnb, hnn]
  exact ⟨hp, hq, hr⟩

/-- End-to-end circuit/cost certificate: the Nat view of the *actual* filled
Caliper buffer satisfies the pre-existing generator-independent constraints. -/
theorem quadratic_circuit_exec (s : State 64) (i : Circuits.Quadratic.Input)
    (tape : RandomTape 64) (b : BufId) (hwf : s.WellFormed) (hfresh : s.caps b = 0)
    (hx : UInt64.ofBitVec (s.regs 0) = fieldWord i.x)
    (hy : UInt64.ofBitVec (s.regs 1) = fieldWord i.y) :
    ∃ s', Exec .unit tape (quadraticCode b) s s' 14 4 4 ∧ s'.WellFormed ∧
      OutputPost s b [0, 1] (quadraticCells s) s' ∧
      ∃ v : Circuits.Quadratic.Buffer,
        v.toArray = (s'.bufs b).map BitVec.toNat ∧ Circuits.Quadratic.Constraints i v := by
  obtain ⟨s', he, hp⟩ := quadratic_witness_exec s .unit tape b hfresh
  refine ⟨s', by simpa only [quadratic_unit_cost] using he,
    he.wellFormed_preserved hwf, hp, _, ?_, Circuits.Quadratic.honest_buffer i⟩
  have h := congrArg (Array.map UInt64.toNat) hp.1
  rw [quadratic_cells_circuit s i hx hy] at h
  simpa [Array.map_map, Function.comp_def] using h.symm

theorem modMul_circuit_exec (s : State 64) (i : Circuits.ModMul.Input)
    (hi : Circuits.ModMul.Assumptions i) (tape : RandomTape 64) (b : BufId)
    (hwf : s.WellFormed) (hfresh : s.caps b = 0)
    (ha : UInt64.ofBitVec (s.regs 0) = UInt64.ofNat i.a)
    (hb : UInt64.ofBitVec (s.regs 1) = UInt64.ofNat i.b)
    (hn : UInt64.ofBitVec (s.regs 2) = UInt64.ofNat i.n) :
    ∃ s', Exec .unit tape (modMulCode b) s s' 15 6 6 ∧ s'.WellFormed ∧
      OutputPost s b [0, 1, 2] (modMulCells s) s' ∧
      ∃ v : Circuits.ModMul.Buffer,
        v.toArray = (s'.bufs b).map BitVec.toNat ∧ Circuits.ModMul.Constraints i v := by
  obtain ⟨s', he, hp⟩ := modMul_witness_exec s .unit tape b hfresh
  refine ⟨s', by simpa only [modMul_unit_cost] using he,
    he.wellFormed_preserved hwf, hp, _, ?_, Circuits.ModMul.honest_buffer i hi⟩
  have h := congrArg (Array.map UInt64.toNat) hp.1
  rw [modMul_cells_circuit s i hi ha hb hn] at h
  simpa [Array.map_map, Function.comp_def] using h.symm

/-- The compiler's fixed two-row branch/map artifact, not `Batch.gatedBatchWord`
(which has three rows and is a separate source program). -/
def fixedGatedCode (b : BufId) : Stmt 64 :=
  withWitness Caliper.fixedGatedCompiled b [0, 1, 2, 3]

def fixedGatedValue (s : State 64) : List (Quad UInt64) :=
  Caliper.fixedGatedWord.eval wordModel
    (.cons (decide (s.regs 0 ≠ 0)) (.cons [UInt64.ofBitVec (s.regs 1), UInt64.ofBitVec (s.regs 2)]
      (.cons (UInt64.ofBitVec (s.regs 3)) .nil)))

def fixedGatedCells (s : State 64) : Array UInt64 :=
  ([UInt64.ofBitVec (s.regs 0), UInt64.ofBitVec (s.regs 1), UInt64.ofBitVec (s.regs 2),
    UInt64.ofBitVec (s.regs 3)] ++
    (fixedGatedValue s).flatMap (fun q => [q.square, q.output])).toArray

theorem quadList_regs_read (xs : List (Quad Reg)) (s : State 64) :
    (Caliper.Loc.regs (t := .list .quad) xs).map (fun r => UInt64.ofBitVec (s.regs r)) =
      (Caliper.Loc.read (t := .list .quad) xs s).flatMap (fun q => [q.square, q.output]) := by
  induction xs with
  | nil => rfl
  | cons q qs ih => simpa [Caliper.Loc.regs, Caliper.Loc.read] using ih

/-- Both branches populate all four witness cells, including disabled zeros.
Time varies with the flag, but reserved buffer memory does not. -/
theorem fixedGated_witness_exec (s : State 64) (C : CostModel) (tape : RandomTape 64)
    (b : BufId) (hfresh : s.caps b = 0) :
    ∃ s', Exec C tape (fixedGatedCode b) s s'
        (Caliper.fixedGatedTime C (decide (s.regs 0 ≠ 0)) + writerTime C [0, 1, 2, 3, 18, 19, 20, 21]) 8 8 ∧
      OutputPost s b [0, 1, 2, 3] (fixedGatedCells s) s' := by
  obtain ⟨s₁, hc, hv⟩ := Caliper.fixedGated_exec s C tape
  apply withWitness_exec Caliper.fixedGatedCompiled s s₁ C tape _ b [0, 1, 2, 3]
    (fixedGatedCells s) hc hfresh
  · intro q; exact of_decide_eq_true rfl
  · decide
  · intro r hr; simp at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · have h0 := hc.frame_reg (r := 0) (by decide)
    have h1 := hc.frame_reg (r := 1) (by decide)
    have h2 := hc.frame_reg (r := 2) (by decide)
    have h3 := hc.frame_reg (r := 3) (by decide)
    simp only [List.map_append, quadList_regs_read, hv]
    simp [fixedGatedCells, fixedGatedValue, h0, h1, h2, h3]

/-- Worst-case upper bound covers both flags and every register/tape input. -/
theorem fixedGated_unit_triple (tape : RandomTape 64) (s₀ : State 64) (b : BufId) :
    Triple .unit tape (fun s => s = s₀ ∧ s.WellFormed ∧ s.caps b = 0)
      (fixedGatedCode b)
      (fun s' => OutputPost s₀ b [0, 1, 2, 3] (fixedGatedCells s₀) s' ∧ s'.WellFormed)
      33 8 8 := by
  rintro s ⟨rfl, hwf, hfresh⟩
  obtain ⟨s', he, hp⟩ := fixedGated_witness_exec s .unit tape b hfresh
  refine ⟨s', _, _, _, he, ⟨hp, he.wellFormed_preserved hwf⟩, ?_, le_rfl, le_rfl⟩
  simp [Caliper.fixedGatedTime, Caliper.quadraticTime, CostModel.unit, writerTime]
  split <;> decide

@[simp] theorem fixedGated_unit_cost (flag : Bool) :
    Caliper.fixedGatedTime .unit flag + writerTime .unit [0, 1, 2, 3, 18, 19, 20, 21] =
      if flag then 33 else 23 := by cases flag <;> rfl

@[simp] theorem fixedGated_cycles_cost (flag : Bool) :
    Caliper.fixedGatedTime .cycles flag + writerTime .cycles [0, 1, 2, 3, 18, 19, 20, 21] =
      if flag then 186 else 56 := by cases flag <;> rfl

/-- Cycles is another abstract cost table, not a measured runtime guarantee. -/
theorem fixedGated_cycles_triple (tape : RandomTape 64) (s₀ : State 64) (b : BufId) :
    Triple .cycles tape (fun s => s = s₀ ∧ s.WellFormed ∧ s.caps b = 0)
      (fixedGatedCode b)
      (fun s' => OutputPost s₀ b [0, 1, 2, 3] (fixedGatedCells s₀) s' ∧ s'.WellFormed)
      186 8 8 := by
  rintro s ⟨rfl, hwf, hfresh⟩
  obtain ⟨s', he, hp⟩ := fixedGated_witness_exec s .cycles tape b hfresh
  refine ⟨s', _, _, _, he, ⟨hp, he.wellFormed_preserved hwf⟩, ?_, le_rfl, le_rfl⟩
  rw [fixedGated_cycles_cost]
  split <;> decide

/-- Static SSA endpoints, not liveness peaks. The writer allocates no registers. -/
theorem compiled_register_endpoints :
    Caliper.quadraticCompiled.nextReg = 8 ∧ Caliper.modMulCompiled.nextReg = 6 ∧
    Caliper.fixedGatedCompiled.nextReg = 22 := by decide

/-- All intermediate buffer capacities stay within the actual proved peak.
`B` can be any common support bound; registers are not in this dynamic metric. -/
theorem quadratic_intermediate_memory (s m : State 64) (C : CostModel) (tape : RandomTape 64)
    (b B : Nat) (hb : b < B) (hfresh : s.caps b = 0)
    (hm : Reaches C tape (quadraticCode b) s m) :
    (m.liveMem B : Int) ≤ s.liveMem B + 4 := by
  obtain ⟨_, he, _⟩ := quadratic_witness_exec s C tape b hfresh
  apply he.reaches_liveMem_le_peak (B := B) hm
  intro q hq
  have h : q = b := by
    simpa [quadraticCode, withWitness, Caliper.quadratic_code, Stmt.Touches,
      writeRegs_touches] using hq
  simpa only [h] using hb

theorem modMul_intermediate_memory (s m : State 64) (C : CostModel) (tape : RandomTape 64)
    (b B : Nat) (hb : b < B) (hfresh : s.caps b = 0)
    (hm : Reaches C tape (modMulCode b) s m) :
    (m.liveMem B : Int) ≤ s.liveMem B + 6 := by
  obtain ⟨_, he, _⟩ := modMul_witness_exec s C tape b hfresh
  apply he.reaches_liveMem_le_peak (B := B) hm
  intro q hq
  have h : q = b := by
    simpa [modMulCode, withWitness, Caliper.modMul_code, Stmt.Touches,
      writeRegs_touches] using hq
  simpa only [h] using hb

end Witgen.Backends.CaliperExamples
