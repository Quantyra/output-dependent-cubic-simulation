# Dedicated GCP Lean replay: `492153b`

Source commit: [`492153b07434832ddf5224fe45e5ee03181b815e`](https://github.com/Quantyra/output-dependent-cubic-simulation/commit/492153b07434832ddf5224fe45e5ee03181b815e).

The exact `git archive` source was replayed on `quantyra-sector-lean-builder-02`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`, using Lean 4.30.0 (`d024af099ca4bf2c86f649261ebf59565dc8c622`) and the pinned Mathlib manifest. A fresh archive workspace completed `lake build` with 2,175 jobs. `Audit.lean` and `tools/check_lean_audit.py` passed. The audited declaration `SectorSimulation.sourceWalshSum_recorded_interleaved_cast_closed` depends on `propext`, `Classical.choice`, and `Quot.sound`.

Exact source archive SHA-256: `2b0976890c40493bc0de3d95c962d4c70cdc84fde964ebc97b61b4521606a12f`. Pinned `lake-manifest.json` SHA-256: `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. The raw build log, complete integrated audit output, checker result, toolchain output, and source archive are in this directory and in the evidence tarball. Their hashes are listed in `SHA256SUMS`; the evidence tar hash is in the adjacent `.sha256` file.

The new theorem composes the recorded source Walsh sum with the arbitrary interleaved closed form after transporting vectors across the witnessed dimension equality. It remains a helper theorem. It does not establish normalization, boundedness, source costs, or any of the seven labeled manuscript claims; no paper theorem is certified.