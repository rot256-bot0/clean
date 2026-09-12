# WitGen package constraints

- Work in this package and its design document at `../doc/witgen-dsl-design.md`; do not edit dependency checkouts or unrelated projects.
- The typed core uses Lean 4.32.2 + Std. The optional analysis backend uses the pinned Caliper dependency in `lakefile.toml`; it is not the native Rust execution engine. No dependency on or references to Weft.
- No Codex. No main/master edits. The user authorized continuing `feat/clean-witgen-dsl` and pushing only to the `rot256-bot0/clean` fork, never upstream or dependency repositories. Commits include `Co-authored-by: Mathias Hall-Andersen <mathias@hall-andersen.dk>`.
- Use test-first vertical slices; retain honest RED/GREEN receipts. No `sorry`, custom axioms, `admit`, `unsafe` proof shortcuts, or `native_decide`.
- No extreme builds or blanket heartbeat increases. Kernel proofs should be structural; bounded kernel `decide` is allowed.
- Preserve the distinction between proofs about Lean semantics and testing of Rust emission / rustc / GMP / arkworks. Do not claim those foreign tools are kernel-verified.
- User-facing documentation is code-first and concise.
- Circuit soundness is independent of generator choice. Generators certify full satisfying witness assignments, not only the public outputs.
- A generator-local let is not an emitted witness cell. The explicit layout/encoder must cover every required internal cell.
