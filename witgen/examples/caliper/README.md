# Generated Caliper Examples

These files are snapshots of actual compiler outputs, not handwritten assembly:

- `quadratic.caliper`: `quadraticCode 0` (input plus full quadratic witness).
- `modMul.caliper`: `modMulCode 0` (input, product, quotient, remainder).
- `fixedGated.caliper`: `fixedGatedCode 0` (two rows; both paths in one program).
- `runtime.json`: values and exact time/net/peak observed by pinned `Caliper.run`
  for the listed initialized input registers, both cost models and both gated paths.

Producer definitions and universal certificates are in
`Witgen/Backends/Caliper.lean` and `CaliperExamples.lean`; the writer is in
`CaliperWitness.lean`. `MainCaliper.lean` exports their actual `Stmt` values using
Caliper's renderer and reference interpreter. Rendering/JSON are tested, not proved.
The emitted `skip` instructions remain present; their Caliper cost is zero.

Reproduce from `witgen/`:

```sh
python3 tools/run_caliper.py
```

Compare the regenerated `artifacts/caliper/*.caliper` and `runtime.json` with this
snapshot. To intentionally update the publication examples after verified changes:

```sh
cp artifacts/caliper/quadratic.caliper artifacts/caliper/modMul.caliper \
   artifacts/caliper/fixedGated.caliper artifacts/caliper/runtime.json examples/caliper/
python3 tools/update_design.py
```

Costs are abstract Caliper charges, not native Rust runtime or measured hardware
cycles. Net/peak count reserved buffer-capacity growth, excluding registers.
The full circuit guarantee requires canonical Field17 inputs for quadratic and
`0 < n ≤ 16`, `a < n`, `b < n` for modular multiplication. The two-row gated proof
covers word semantics, not the separate three-row batch circuit.
