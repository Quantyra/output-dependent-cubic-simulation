# Dyadic addition and subtraction compatibility

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/DyadicAddition.lean` SHA-256 `9c9c4f55ce02b331428db0564ed6d5bcfdef55030c5ed62610b82a951b367bae`.

Lean 4.30.0 locked project build passed (68 jobs). Exact axiom sets are in `CLAIMS.json` and within the permitted baseline. Addition, negation and subtraction preserve the defined dyadic equivalence, complementing the earlier multiplication proof. Addition is commutative and subtraction equals addition of negation at the representation level.

The quotient and its algebraic laws, complex embedding, normalized gate behavior, native replay, Python equivalence, cost and all labeled manuscript theorems remain open.
