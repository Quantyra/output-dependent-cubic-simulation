# Pivot-step invariants

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PivotStepInvariants.lean` SHA-256 `1ae8b823e2c595e1b6cb593634ec1e6b9d1d747e9ce3e06e60e8eead7d4cf205`.

Lean 4.30.0 with locked dependencies: `lake build` passed (32 jobs), and the 75-declaration axiom audit passed. The checked statements cover moving a set pivot to the diagonal, clearing a set target entry, preserving other rows and the pivot row, and exact eligibility/inclusion of generated clearing operations. The first four depend on `[propext]`, the last two on `[propext, Quot.sound]`.

These are local facts, not yet an induction over the complete clearing list, reduction completeness, a runtime proof, or certification of a labeled manuscript theorem.
