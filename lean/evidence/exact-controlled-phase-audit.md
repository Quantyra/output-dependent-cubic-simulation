# Exact normalized controlled-sign action

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactControlledPhase.lean` SHA-256 `3a9a32c3e91a29994885a303db3be8d343dee334dc8737169508721980e9871f`.

Lean 4.30.0 locked project build passed (71 jobs). Both audited declarations use `[propext, Classical.choice, Quot.sound]`. On any exact shared-denominator state and distinct control and target wires, the defined normalized target-Hadamard, CNOT, target-Hadamard sequence yields the controlled-sign coefficient at every basis vector, accounting for both denominator increments.

This is a theorem of the defined exact model. Complex embedding, representation independence and general state coverage, norm preservation, literal native gate replay, Python correspondence, full circuit, cost and all labeled manuscript theorems remain open.
