# Exact gate addition preservation

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactGateLinearity.lean` SHA-256 `ce792c99a1349d8c2b6a038f5be277db880c485b62d37be9bc9fc040984c67ee`.

Lean 4.30.0 locked project build passed (75 jobs). Exact axiom sets are in `CLAIMS.json` and within the permitted baseline. Each modeled H, X, Z, T, TDG and CNOT action preserves numerator addition for two shared-denominator states with equal denominator exponents, including the corresponding output denominator.

This is per-gate addition preservation, not yet replay-wide linearity, arbitrary-coefficient homogeneity, arbitrary-state Toffoli correctness, wire relabeling, complex embedding, Python equivalence, full circuit behavior, cost or any labeled manuscript theorem.
