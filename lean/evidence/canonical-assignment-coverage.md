# Canonical assignment coverage and finite vectors

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalAssignmentCoverage.lean` SHA-256 `e64004dab718a04ce539a5bb8471b67b39d8813107353a0b13d5050085b0a7de`.

Lean 4.30.0 checked all 15 declarations locally with the axiom sets recorded in the claim inventory. The pair and radical list generators contain exactly the correctly sized lists, have no duplicates and have lengths `4^k` and `2^m`. The radical-list representation round-trips with finite binary vectors, so each enumerated radical assignment corresponds to exactly one vector; zero dimensions are included.

Pair lists have not yet been related to a single finite vector coordinate layout, and phase evaluation is not yet connected to source ANF or a computed general quadratic basis. Polar rank, general affine support and elimination costs remain open. No labeled paper theorem is certified.
