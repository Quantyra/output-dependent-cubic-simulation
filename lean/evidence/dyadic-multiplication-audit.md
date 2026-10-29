# Dyadic multiplication compatibility

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/DyadicMultiplication.lean` SHA-256 `e5a3edd673acc42cac25b4881866ea0e0e722c738c9dbda75631ef9dc8e778f6`.

Lean 4.30.0 locked project build passed (67 jobs). Exact axiom sets are in `CLAIMS.json` and remain within the permitted baseline. Integer scaling distributes across represented multiplication; dyadic multiplication is commutative and preserves the cross-multiplication equivalence when either or both operands are replaced by equivalent representations.

Addition and subtraction compatibility, quotient construction, complex embedding, normalized gate behavior, native replay, Python equivalence, cost and all labeled manuscript theorems remain open.
