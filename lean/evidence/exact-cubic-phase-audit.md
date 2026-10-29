# Exact normalized cubic-sign action

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactCubicPhase.lean` SHA-256 `5aae9007f3ac0de254cc2d00e6b2e94b3092f1f1a6a6219fd3eec81d8d40a06f`.

Lean 4.30.0 locked project build passed (72 jobs). Both declarations use `[propext, Classical.choice, Quot.sound]`. For any exact shared-denominator state and each control distinct from target, the defined normalized target-Hadamard, ideal Toffoli, target-Hadamard sequence yields the cubic controlled-sign amplitude at every basis vector, accounting for both denominator increments.

This assumes the ideal Toffoli model, not the compiler's decomposed gate sequence. Complex embedding, representation independence, norm preservation, literal native replay, Python correspondence, full circuit, cost and all labeled manuscript theorems remain open.
