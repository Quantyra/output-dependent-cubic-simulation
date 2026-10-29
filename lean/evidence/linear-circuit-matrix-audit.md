# Reversed Gaussian CNOT basis action

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/LinearCircuitCorrect.lean` SHA-256 `6864d03e793ae2b5a7b4813520c2d81b9bbe4f47248af36594c25b1897c64c07`.

Lean 4.30.0 locked project build passed (52 jobs). The distinct-wire and reverse-cancellation declarations use `[propext, Quot.sound]`; both Gaussian-action declarations use `[propext, Classical.choice, Quot.sound]`. Whenever the represented Gaussian row program succeeds, the reversed modeled CNOT list applies the original binary matrix to every represented basis vector. The corresponding forward list is its inverse on every matrix-applied vector.

This is a Boolean basis-action proof for the Lean model. Equivalence to Python's emitted gate records, quantum amplitude semantics, full circuit replay, cost, and all labeled manuscript theorem proofs remain open.
