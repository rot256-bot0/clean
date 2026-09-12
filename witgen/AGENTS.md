# Prototype constraints

- Work only in this prototype directory; do not edit dependency checkouts or other projects.
- Standalone Lean 4.32.2 + Std; no external Lean framework dependency or references.
- No Codex. No main/master edits. No pushes. Commits, if made, include `Co-authored-by: Mathias Hall-Andersen <mathias@hall-andersen.dk>`.
- Use test-first vertical slices; retain honest RED/GREEN receipts. No `sorry`, custom axioms, `admit`, `unsafe` proof shortcuts, or `native_decide`.
- No extreme builds or blanket heartbeat increases. Kernel proofs should be structural; bounded kernel `decide` is allowed.
- Preserve the distinction between proofs about Lean semantics and testing of Rust emission / rustc / GMP / arkworks. Do not claim those foreign tools are kernel-verified.
- User-facing documentation is code-first and concise.
- Circuit soundness is independent of generator choice. Generators certify full satisfying witness assignments, not only the public outputs.
- A generator-local let is not an emitted witness cell. The explicit layout/encoder must cover every required internal cell.
