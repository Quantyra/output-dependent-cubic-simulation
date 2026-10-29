# Represented descriptor validation

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/SourceValidation.lean` SHA-256 `da1d935afee4e61b0ed8ea6380f687fe87e1926afbdbf7ed9af2b7b7eb639016`.

Lean 4.30.0 with locked dependencies: `lake build` passed (42 jobs), the 108-declaration axiom audit passed, and source examples for valid, singular and asymmetric descriptors passed. The concrete represented-data validator accepts exactly cubic phases with a symmetric, injective pairing evaluator. Acceptance entails the proved pivot-based unique nonzero output shift and quadratic derivative construction. The symmetry theorem uses `[propext, Quot.sound]`; the other two use `[propext, Classical.choice, Quot.sound]`.

This validates the represented descriptor, not a byte decoder, native gate replay, finite-encoding runtime, physical circuit identity, Walsh/sector result, or any labeled manuscript theorem.
