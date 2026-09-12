import Witgen.Backends.CaliperExamples

/-! Kernel-checked examples for the published runtime walkthrough.
The `.cycles` table is an abstract Caliper model, not a Rust/hardware timing claim. -/
namespace Witgen.Backends.CaliperRuntimeGuide
open _root_.Caliper Witgen.Backends.CaliperExamples

/-- Termination, complete witness output, memory safety, and an abstract runtime bound.
Registers start with arbitrary values; the named output buffer must be fresh. -/
theorem quadratic_runtime (tape : RandomTape 64) (s₀ : State 64) (b : BufId) :
    Triple .cycles tape
      (fun s => s = s₀ ∧ s.WellFormed ∧ s.caps b = 0)
      (quadraticCode b)
      (fun s' => OutputPost s₀ b [0, 1] (quadraticCells s₀) s' ∧ s'.WellFormed)
      90 4 4 := by
  exact quadratic_triple .cycles tape s₀ b

/-- Exact cost of every completed run, not merely the upper bounds of a Triple. -/
theorem quadratic_exact_cost (tape : RandomTape 64) (s s' : State 64)
    (b : BufId) (hfresh : s.caps b = 0) (t : Nat) (net peak : Int)
    (h : Exec .cycles tape (quadraticCode b) s s' t net peak) :
    t = 90 ∧ net = 4 ∧ peak = 4 := by
  obtain ⟨_, he, _⟩ := quadratic_witness_exec s .cycles tape b hfresh
  have hd := h.deterministic he
  exact ⟨hd.2.1.trans quadratic_cycles_cost, hd.2.2.1, hd.2.2.2⟩

/-- Parameterized word modular multiplication, not a fixed small field and not
BN254. Inputs are arbitrary words; the separate Nat-circuit link needs bounds. -/
theorem modMul_runtime (tape : RandomTape 64) (s₀ : State 64) (b : BufId) :
    Triple .cycles tape
      (fun s => s = s₀ ∧ s.WellFormed ∧ s.caps b = 0)
      (modMulCode b)
      (fun s' => OutputPost s₀ b [0, 1, 2] (modMulCells s₀) s' ∧ s'.WellFormed)
      99 6 6 := by
  exact modMul_triple .cycles tape s₀ b

/-- All completed executions have this exact abstract cost and memory usage. -/
theorem modMul_exact_cost (tape : RandomTape 64) (s s' : State 64)
    (b : BufId) (hfresh : s.caps b = 0) (t : Nat) (net peak : Int)
    (h : Exec .cycles tape (modMulCode b) s s' t net peak) :
    t = 99 ∧ net = 6 ∧ peak = 6 := by
  obtain ⟨_, he, _⟩ := modMul_witness_exec s .cycles tape b hfresh
  have hd := h.deterministic he
  exact ⟨hd.2.1.trans modMul_cycles_cost, hd.2.2.1, hd.2.2.2⟩

end Witgen.Backends.CaliperRuntimeGuide
