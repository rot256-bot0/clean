import Caliper.Triple

/-! Actual Caliper witness-buffer population; no compiler dependency.
The writer allocates empty capacity, then initializes exactly one cell per push.
`Exec` indices count buffer capacity, not static register slots. -/
namespace Witgen.Backends.CaliperWitness
open Caliper
variable {w : Nat}

/-- Push source registers in list order; duplicates are intentional. -/
def pushRegs (b : BufId) : List Reg → Stmt w
  | [] => .skip
  | r :: rs => .memPush b r ;; pushRegs b rs

/-- Reserve exact capacity, then populate the filled prefix. No scratch registers. -/
def writeRegs (b : BufId) (rs : List Reg) : Stmt w :=
  .memAllocI b rs.length ;; pushRegs b rs

/-- Both capacity acquisition and initialization are charged. -/
def writerTime (C : CostModel) (rs : List Reg) : Nat :=
  C.memAlloc + rs.length * C.allocPerWord + rs.length * C.memPush

/-- The exact state transformer used only to state and prove execution. -/
def pushState (s : State w) (b : BufId) : List Reg → State w
  | [] => s
  | r :: rs => pushState (s.setBuf b ((s.bufs b).push (s.regs r))) b rs

def writerState (s : State w) (b : BufId) (rs : List Reg) : State w :=
  pushState (s.allocBuf b rs.length) b rs

@[simp] theorem pushState_regs (s : State w) (b : BufId) (rs : List Reg) :
    (pushState s b rs).regs = s.regs := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp [pushState, ih]

@[simp] theorem pushState_caps (s : State w) (b : BufId) (rs : List Reg) :
    (pushState s b rs).caps = s.caps := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp [pushState, ih]

@[simp] theorem pushState_tapePos (s : State w) (b : BufId) (rs : List Reg) :
    (pushState s b rs).tapePos = s.tapePos := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    simpa only [pushState, State.setBuf] using
      (ih (s.setBuf b ((s.bufs b).push (s.regs r))))

theorem pushState_other (s : State w) (b : BufId) (rs : List Reg)
    (q : BufId) (hq : q ≠ b) : (pushState s b rs).bufs q = s.bufs q := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp [pushState, ih, hq]

theorem pushState_contents (s : State w) (b : BufId) (rs : List Reg) :
    (pushState s b rs).bufs b = s.bufs b ++ (rs.map s.regs).toArray := by
  induction rs generalizing s with
  | nil => simp [pushState]
  | cons r rs ih =>
    simp only [pushState, ih, bufs_setBuf_self, regs_setBuf, List.map_cons]
    apply Array.toList_inj.mp
    simp

/-- Every push fits reserved capacity. Indices are exact and memory-neutral. -/
theorem pushRegs_exec (C : CostModel) (tape : RandomTape w)
    (s : State w) (b : BufId) (rs : List Reg)
    (hcap : (s.bufs b).size + rs.length ≤ s.caps b) :
    Exec C tape (pushRegs b rs) s (pushState s b rs) (rs.length * C.memPush) 0 0 := by
  induction rs generalizing s with
  | nil => simpa [pushRegs, pushState] using (Exec.skip (C := C) (tape := tape) (s := s))
  | cons r rs ih =>
    have hp : (s.bufs b).size < s.caps b := by simp only [List.length_cons] at hcap; omega
    have hc : ((s.setBuf b ((s.bufs b).push (s.regs r))).bufs b).size + rs.length ≤
        (s.setBuf b ((s.bufs b).push (s.regs r))).caps b := by
      simpa only [bufs_setBuf_self, caps_setBuf, Array.size_push, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap
    simpa [pushRegs, pushState, Nat.add_mul, Nat.add_comm] using
      Exec.seq (Exec.memPush (C := C) (tape := tape) (src := r) hp) (ih _ hc)

/-- Exact execution certificate, universally quantified over all input registers.
Freshness means zero initial capacity. For a physical interpretation also require
`s.WellFormed`, which implies a fresh buffer's initial filled prefix is empty. -/
theorem writeRegs_exec (C : CostModel) (tape : RandomTape w)
    (s : State w) (b : BufId) (rs : List Reg) (hfresh : s.caps b = 0) :
    Exec C tape (writeRegs b rs) s (writerState s b rs)
      (writerTime C rs) rs.length rs.length := by
  have hp := pushRegs_exec C tape (s.allocBuf b rs.length) b rs (by simp)
  simpa [writeRegs, writerState, writerTime, hfresh] using
    Exec.seq (Exec.memAllocI (C := C) (tape := tape) (s := s) (b := b) (n := rs.length)) hp

@[simp] theorem writerState_regs (s : State w) (b : BufId) (rs : List Reg) :
    (writerState s b rs).regs = s.regs := by simp [writerState]

@[simp] theorem writerState_tapePos (s : State w) (b : BufId) (rs : List Reg) :
    (writerState s b rs).tapePos = s.tapePos := by simp [writerState, State.allocBuf]

@[simp] theorem writerState_contents (s : State w) (b : BufId) (rs : List Reg) :
    (writerState s b rs).bufs b = (rs.map s.regs).toArray := by
  simp [writerState, pushState_contents]

@[simp] theorem writerState_capacity (s : State w) (b : BufId) (rs : List Reg) :
    (writerState s b rs).caps b = rs.length := by simp [writerState]

theorem writerState_other (s : State w) (b : BufId) (rs : List Reg)
    (q : BufId) (hq : q ≠ b) :
    (writerState s b rs).bufs q = s.bufs q ∧ (writerState s b rs).caps q = s.caps q := by
  simp [writerState, pushState_other, hq]

/-- Complete value/frame postcondition, parameterized by the initial state. -/
def WriterPost (s : State w) (b : BufId) (rs : List Reg) (s' : State w) : Prop :=
  s'.bufs b = (rs.map s.regs).toArray ∧ s'.caps b = rs.length ∧
  s'.regs = s.regs ∧ s'.tapePos = s.tapePos ∧
  (∀ q, q ≠ b → s'.bufs q = s.bufs q ∧ s'.caps q = s.caps q)

theorem writerState_post (s : State w) (b : BufId) (rs : List Reg) :
    WriterPost s b rs (writerState s b rs) := by
  exact ⟨writerState_contents s b rs, writerState_capacity s b rs,
    writerState_regs s b rs, writerState_tapePos s b rs, writerState_other s b rs⟩

/-- Caliper total correctness: no out-of-range access, exact values, finite storage,
and time/net/peak upper bounds. The exact profile is `writeRegs_exec`. -/
theorem writeRegs_triple (C : CostModel) (tape : RandomTape w)
    (s₀ : State w) (b : BufId) (rs : List Reg) :
    Triple C tape (fun s => s = s₀ ∧ s.WellFormed ∧ s.caps b = 0)
      (writeRegs b rs) (fun s' => WriterPost s₀ b rs s' ∧ s'.WellFormed)
      (writerTime C rs) rs.length rs.length := by
  rintro s ⟨rfl, hwf, hfresh⟩
  have he := writeRegs_exec C tape s b rs hfresh
  exact ⟨writerState s b rs, _, _, _, he,
    ⟨writerState_post s b rs, he.wellFormed_preserved hwf⟩, le_rfl, le_rfl, le_rfl⟩

@[simp] theorem writerTime_unit (rs : List Reg) : writerTime .unit rs = 2 * rs.length := by
  simp [writerTime, CostModel.unit]; omega

@[simp] theorem writerTime_cycles (rs : List Reg) : writerTime .cycles rs = 6 * rs.length := by
  simp [writerTime, CostModel.cycles]; omega

/-- For any other execution, final state and all resource indices are identical. -/
theorem writeRegs_unique (C : CostModel) (tape : RandomTape w)
    (s s' : State w) (b : BufId) (rs : List Reg) (hfresh : s.caps b = 0)
    {t : Nat} {d p : Int} (h : Exec C tape (writeRegs b rs) s s' t d p) :
    s' = writerState s b rs ∧ t = writerTime C rs ∧ d = rs.length ∧ p = rs.length :=
  h.deterministic (writeRegs_exec C tape s b rs hfresh)

/-- The writer cannot change any register, including its source registers. -/
theorem pushRegs_noWrites (b : BufId) (rs : List Reg) (r : Reg) :
    ¬ (pushRegs (w := w) b rs).Writes r := by
  induction rs with
  | nil => simp [pushRegs]
  | cons a rs ih => simp [pushRegs, Stmt.Writes, ih]

theorem writeRegs_noWrites (b : BufId) (rs : List Reg) (r : Reg) :
    ¬ (writeRegs (w := w) b rs).Writes r := by
  simp [writeRegs, Stmt.Writes, pushRegs_noWrites]

theorem pushRegs_touches (b : BufId) (rs : List Reg) (q : BufId) :
    (pushRegs (w := w) b rs).Touches q → q = b := by
  induction rs with
  | nil => simp [pushRegs]
  | cons r rs ih =>
    intro h
    rcases h with h | h
    · exact h
    · exact ih h

theorem writeRegs_touches (b : BufId) (rs : List Reg) (q : BufId) :
    (writeRegs (w := w) b rs).Touches q ↔ q = b := by
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact pushRegs_touches b rs q h
  · exact fun h => Or.inl h

/-- Absolute final live-memory increase over any support bound covering `b`.
Well-formedness is needed for the interpretation as physical allocated storage. -/
theorem writeRegs_liveMem (C : CostModel) (tape : RandomTape w)
    (s : State w) (b : BufId) (rs : List Reg) (hfresh : s.caps b = 0)
    (B : Nat) (hb : b < B) :
    ((writerState s b rs).liveMem B : Int) = s.liveMem B + rs.length := by
  apply (writeRegs_exec C tape s b rs hfresh).liveMem_eq
  intro q hq
  rwa [(writeRegs_touches b rs q).mp hq]

/-- Every instruction-boundary state is within the same absolute memory bound. -/
theorem writeRegs_reaches_bound (C : CostModel) (tape : RandomTape w)
    (s m : State w) (b : BufId) (rs : List Reg) (hfresh : s.caps b = 0)
    (B : Nat) (hb : b < B) (hm : Reaches C tape (writeRegs b rs) s m) :
    (m.liveMem B : Int) ≤ s.liveMem B + rs.length := by
  apply (writeRegs_exec C tape s b rs hfresh).reaches_liveMem_le_peak hm
  intro q hq
  rwa [(writeRegs_touches b rs q).mp hq]

/-- Composition seam for any actual Caliper producer with a memory-neutral profile. -/
theorem produce_write_exec (C : CostModel) (tape : RandomTape w)
    (code : Stmt w) (s s₁ : State w) (t : Nat)
    (b : BufId) (rs : List Reg)
    (hc : Exec C tape code s s₁ t 0 0) (hfresh : s₁.caps b = 0) :
    Exec C tape (code ;; writeRegs b rs) s (writerState s₁ b rs)
      (t + writerTime C rs) rs.length rs.length := by
  simpa using Exec.seq hc (writeRegs_exec C tape s₁ b rs hfresh)

/-- Reserved but uninitialized memory has no load execution, for any capacity. -/
theorem reserved_load_noExec (C : CostModel) (tape : RandomTape w)
    (s s' : State w) (b : BufId) (n : Nat) (dst idx : Reg)
    (t : Nat) (d p : Int) :
    ¬ Exec C tape (.memLoad dst b idx) (s.allocBuf b n) s' t d p := by
  intro h
  cases h with
  | memLoad hlt => simp at hlt

/-- A full or malformed overfull buffer cannot be pushed. -/
theorem full_push_noExec (C : CostModel) (tape : RandomTape w)
    (s s' : State w) (b : BufId) (src : Reg) (t : Nat) (d p : Int)
    (hfull : s.caps b ≤ (s.bufs b).size) :
    ¬ Exec C tape (.memPush b src) s s' t d p := by
  intro h
  cases h with
  | memPush hlt => omega

end Witgen.Backends.CaliperWitness
