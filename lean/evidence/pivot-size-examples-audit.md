# Pivot program operation count and examples

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/GaussianPivotSize.lean` SHA-256 `954fe6bb00c405185655a5a31a854db71f4f7c9166a94292340671600ca15e10`.

Lean 4.30.0 with locked dependencies: `lake build` passed (30 jobs), the 68-declaration axiom audit passed, and `lake env lean PivotExamples.lean` passed five finite checks: dimension zero, identity, row swap, triangular invertible and singular refusal. CI runs these checks. Any successful pivot program contains at most `n(n+1)` row operations; all three audited size declarations use `[propext, Quot.sound]`.

The examples do not prove correctness or completeness of reduction. An operation count is not a runtime bound for the current function-valued matrix representation. Native source semantics and all labeled manuscript theorem certifications remain open.
