# Dedicated GCP Lean replay: `5852639`

Source commit: [`5852639bebb6e5b26d0fc92ed03633d98388b7af`](https://github.com/Quantyra/output-dependent-cubic-simulation/commit/5852639bebb6e5b26d0fc92ed03633d98388b7af).

The dedicated builder `quantyra-sector-lean-builder-02` in project `quantyra-lean-cert-20260915`, zone `us-central1-a`, replayed the exact source archive using Lean 4.30.0 and the pinned Mathlib manifest. `lake build` completed 2,175 jobs; `Audit.lean` and `tools/check_lean_audit.py` passed, with no `sorryAx`.

The exact source archive SHA-256 is `32d8e64c9073477f2be634774bf38d72f829d51a234543739910557685787cbf`. The evidence archive SHA-256 is `7d8284fa77d67db146f280e564917557a1b7e6a9798f79a78021b698c20932ca`, recorded beside the archive. The bundle includes the source archive, build log, audit output, result receipt and component hashes.

The commit adds `recordedCoordinateOrder_dimension` and its existential helper, proving that the recorded paired coordinates plus residual coordinates account for the full dimension. This is a structural helper result only; no manuscript theorem is certified.
