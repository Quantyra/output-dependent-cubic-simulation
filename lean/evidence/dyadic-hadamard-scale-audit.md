# Exact dyadic Hadamard scale

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/DyadicCyclo.lean` SHA-256 `d6fc9dd65d0951d27a2d7ec45e23cc44015197c73a8c0c7c75700eba205a0d1c`.

Lean 4.30.0 locked project build passed (65 jobs). All four declarations have no axiom dependencies. The representation stores an eighth-root integer numerator and a power-of-two denominator. Its cross-multiplication relation is reflexive and symmetric; the concrete represented scale (z-z^3)/2 has square one half and twice that square is equivalent to one.

Transitivity and arithmetic compatibility of the relation, complex embedding, normalized Hadamard action, native replay, Python correspondence, full circuit, cost and all labeled manuscript theorems remain open. The scalar identities use kernel reduction, not native evaluation.
