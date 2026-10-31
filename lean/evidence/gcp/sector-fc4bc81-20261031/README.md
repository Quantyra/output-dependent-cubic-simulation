# Dedicated GCP Lean replay: `fc4bc81`

Source commit: [`fc4bc81b9b5aca158d9bf78dc1a4f65cd838e5d3`](https://github.com/Quantyra/output-dependent-cubic-simulation/commit/fc4bc81b9b5aca158d9bf78dc1a4f65cd838e5d3).

The exact source archive was replayed on `quantyra-sector-lean-builder-02` in project `quantyra-lean-cert-20260915`, zone `us-central1-a`, using Lean 4.30.0 and the pinned Mathlib manifest. `lake build` completed 2,175 jobs. `Audit.lean` and `tools/check_lean_audit.py` passed; the audit reports no `sorryAx`. The updated `recordedCoordinateOrder_dimension_exists` declaration has only `propext` and `Quot.sound` axioms.

The exact source archive SHA-256 is `232022a54e2e71ecf5490fbc5e162ecafed2522b865a022268a2cb32457a53eb`. Component hashes are in `SHA256SUMS`; the evidence archive SHA-256 is in the adjacent `.sha256` file.

This checkpoint exposes both the equality between the recorded pair count and `k` and the residual dimension equation. It is structural support for the next source composition proof; no manuscript theorem is certified.
