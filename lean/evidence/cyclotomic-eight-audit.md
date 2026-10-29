# Exact eighth-root coefficient model

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CyclotomicEight.lean` SHA-256 `44c8fe2133dd88c382a5bc3c6709cf3417c86776278e15f3aa48161781ea94dc`.

Lean 4.30.0 locked project build passed (63 jobs). Exact axiom sets appear in `CLAIMS.json` and are within the permitted baseline. The four-integer model defines multiplication modulo the relation z^4 = -1; distributivity, commutativity, z times its inverse, z^4 = -1, and (z-z^3)^2 = 2 are checked. A flip-invariant diagonal multiplier over these coefficients commutes with the modeled unnormalized Hadamard.

No complex embedding, division by two, physical normalized Hadamard, full native Toffoli execution, Python equivalence, cost or labeled manuscript theorem has been proved by these declarations.
