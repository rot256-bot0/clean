# Caliper Review Scope

**Historical checkpoint:** this records the recovered backend review preceding
commit `3f31325a`, before migration to generic structural features. The current
Caliper audit has 88 entries, including the new structural correspondence and
ModMul runtime-guide endpoints. Run the current verification commands for the
current source hashes; the historical count below is not the present inventory.

The recovered compiler, writer and circuit/resource example sources were independently
reviewed before integration. No blocking semantic defect or proof hole was found in
that scope. Direct Lean checks, independent alias/control/arithmetic/buffer controls,
and a nonempty audit of all 82 named implementation/runtime-guide theorems passed.
The inspected proof dependencies were only `propext`, `Classical.choice`, `Quot.sound`.

This is not a claim of generic whole-compiler correctness. The checked source layouts
and their theorem hypotheses remain the scope, as documented in
[CaliperBackendAPI.md](CaliperBackendAPI.md) and [CaliperCostAPI.md](CaliperCostAPI.md).

The review identified integration requirements rather than compiler defects:

- Keep the ordinary `Witgen` import core-only, but run the optional Caliper suite from
  the standard verification entry point.
- Use a distinct explicit Caliper axiom policy; do not relax the stricter core audit.
- Include nested backend source hashes and directly check sources, not cached replay.
- Audit the published runtime guide and retain actual generated assembly/run receipts.

The final verification runner implements those gates. Reproduce with
`python3 tools/run_demo.py` and `python3 -m unittest discover -s tests -v` from `witgen/`.
The fresh `artifacts/caliper/verification.json` binds its executed commands and hashes;
this narrative is not a substitute for that receipt.

Independent source review additions exercised register/capture aliases, nested branch
shapes, noncanonical nonzero flags, static map/fold layouts, wrapping/zero-divisor word
operations, actual full circuit buffers, and custom allocation cost tables. These are
validation controls, not a universal theorem for unspecialized compiler outputs.
