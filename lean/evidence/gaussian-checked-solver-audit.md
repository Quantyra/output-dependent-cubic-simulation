# Checked pivot solver soundness

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/GaussianSolveChecked.lean` SHA-256 `86fbef02fa55f23db819e19473770c3e276aa2184c69b6b1697c094ff30fe760`.

Lean 4.30.0 with locked dependencies: `lake build` passed (31 jobs), the 69-declaration axiom audit passed, and `lake env lean PivotExamples.lean` passed nine finite checks including three nonzero-target solves and singular refusal. The solver runs the candidate pivot program and explicitly checks the returned vector against the original equation. `gaussianSolveChecked_sound` proves every returned result is valid, using `[propext, Quot.sound]`.

The solver can refuse; no completeness, invertibility-validation or finite-encoding runtime theorem is claimed. Function-valued matrices may have non-polynomial evaluation costs. Native circuit semantics and all labeled manuscript theorems remain open.
