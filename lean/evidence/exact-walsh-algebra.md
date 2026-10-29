# Exact-amplitude algebra for Walsh expansion

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactWalshAlgebra.lean` SHA-256 `93461a1a574a5a87a52f6df04165faaf7b62d59c2aeba908419ea145a8a17fdf`.

The locked Lean 4.30.0 build passed (118 jobs). The four declarations have exact transitive axioms recorded in the project audit baseline. Addition and multiplication are associative in the exact amplitude quotient; subtraction equals addition of the exact negation. The dyadic addition associativity theorem is proved at the representation level.

An attempted distributivity proof did not close and is not included or assumed. Distributivity, the closed normalized Walsh-sum formula, complex embedding, circuit-to-sector identities, costs and all paper theorem labels remain open.
