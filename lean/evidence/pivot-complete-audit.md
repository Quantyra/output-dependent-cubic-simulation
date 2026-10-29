# Pivot generation and checked solver completeness

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PivotComplete.lean` SHA-256 `a75214cbdcc06a12a7cbd4cb9b758fbf5fea59d5758c019dfb772f0929340a4d`.

Lean 4.30.0 with locked dependencies: `lake build` passed (40 jobs), and the 104-declaration axiom audit passed. A well-founded induction on the remaining consecutive columns carries matrix injectivity and earlier unit columns through each actual pivot step. The full pivot generator succeeds if and only if the source matrix evaluator is injective; for any injective matrix and target, the checked solver returns a solution. Previously audited soundness shows every returned solution satisfies the original equation. All four new declarations use `[propext, Classical.choice, Quot.sound]`.

This establishes extensional correctness and completeness of the represented solver, not a finite-encoding runtime bound. Function-valued matrix evaluation may incur non-polynomial cost. Source validation, native circuit semantics and all labeled manuscript theorem certifications remain open.
