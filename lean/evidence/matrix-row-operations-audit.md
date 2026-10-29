# Binary matrix row operations

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/MatrixRowOperations.lean` SHA-256 `c115f172fa387ea1b0afac09ace0ea1749fa4475fd1da047b86ab9c50d1f4626`.

Lean 4.30.0 with locked dependencies: `lake build` passed (27 jobs), and the 61-declaration axiom audit passed. Swapping two rows and their target entries preserves the exact solution set. XORing one distinct row into another and applying the corresponding target operation also preserves it. The proofs use the actual matrix evaluator, include identical swap indices and require distinct indices for row addition; all six declarations use `[propext, Quot.sound]`.

These elementary operations are foundations for elimination, not an elimination algorithm, pivot proof, invertibility check, operational complexity bound, or labeled manuscript theorem.
