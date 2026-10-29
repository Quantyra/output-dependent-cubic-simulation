# Pivot-based source output derivative

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/SourceOutputPivot.lean` SHA-256 `5d56e18ef0f2e9d6d0f75f10caab5a67350c177d2022bed73eec30bff6c77383`.

Lean 4.30.0 with locked dependencies: `lake build` passed (41 jobs), and the 105-declaration axiom audit passed. For cubic source phases and an injective pairing matrix evaluator, the actual pivot-based construction returns the unique nonzero shift solving `Jj=e` and a quadratic bit-mask ANF with at most seven output masks per second-phase input mask, evaluating to the corresponding derivative. The theorem uses `[propext, Classical.choice, Quot.sound]`.

The matrix is function-valued and no finite-encoding runtime bound is established. Source validation, native circuit semantics, Walsh/sector results and all labeled manuscript theorem certifications remain open.
