# Cubic-mask selected-index shapes

Target bridge: the cubic derivative argument in section 2 of https://doi.org/10.5281/zenodo.23754698. Audited historical source at commit `1295fee`, `lean/SectorSimulation/SupportShapes.lean`, SHA-256 `4c5075949b4932cc74f9dab7f5ac510de806d1608d5283e493da0727406e71ed`.

With Lean 4.30.0 and the locked Mathlib manifest, `lake build` passed with ten jobs. `lake env lean Audit.lean` and the 23-declaration `tools/check_lean_audit.py` check passed. The elaborated declarations prove that any list of length at most three is empty or has one, two or three displayed entries, and that any bit-mask monomial whose `monomialDegree` is at most three has such a selected-index list. Both report `[propext]` as their transitive axiom dependency, within the approved baseline.

The list proof is exhaustive case analysis, with the four-or-more case contradicted by the length bound. The source theorem uses the previously proved equality between mask degree and selected-list length. It covers all finite dimensions, including zero, and supplies actual index witnesses rather than assuming a decomposition.

This is a shape-extraction bridge. It does not yet construct a derivative ANF, prove that output masks have degree at most two, connect native decoder/gate semantics, or certify a manuscript theorem. Clean CI for this increment remains to be checked.
