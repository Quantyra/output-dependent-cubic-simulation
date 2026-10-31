# Dedicated GCP Lean replay: `9aaec54`

Source commit: [`9aaec54aee252899cc44f2428ded4de5935d6d00`](https://github.com/Quantyra/output-dependent-cubic-simulation/commit/9aaec54aee252899cc44f2428ded4de5935d6d00).

A Git archive of the complete Lean project and `tools/check_lean_audit.py` was replayed in a fresh source workspace on `quantyra-sector-lean-builder-02`, project `quantyra-lean-cert-20260915`, zone `us-central1-a`. Lean 4.30.0 (`d024af099ca4bf2c86f649261ebf59565dc8c622`) and the pinned Lake manifest were used. The archive excludes only `lean/evidence/**`; raw archive SHA-256: `9fdad1a068082108145f72beac289571c5f28fbf3efc6b03cdcef4e287cfe278`. Pinned `lake-manifest.json` SHA-256: `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`.

The full project build passed (2,175 jobs), as did `Audit.lean` and `tools/check_lean_audit.py` against the exact axiom baseline. New result `sourceWalshSum_recorded_interleaved_cast_zero_iff_residualCoordinate` states that the source Walsh sum is zero exactly when at least one residual coordinate of the transported character is true. It exposes the support constraint one coordinate at a time, providing a direct input to the affine support proof. New helper dependencies are recorded in the integrated audit and claim inventory; the coordinatewise theorem uses `propext`, `Classical.choice`, and `Quot.sound`.

This remains a generated-coordinate support statement. It does not yet identify the solution set with `l0 + im(B_q)`, prove its rank, establish normalized sector identity or matched-sector boundedness, connect literal circuit semantics, prove source costs, or certify any of the seven paper claims. No paper theorem is certified.

Raw build and audit logs, checker output, toolchain version, pinned manifest hash, and source archive are included. Component hashes are in `SHA256SUMS`; the outer evidence tar hash is in its adjacent `.sha256` file.
