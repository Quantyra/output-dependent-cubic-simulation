# Native CNOT record replay on basis states

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NativeCNOTReplay.lean` SHA-256 `00ec05035488883a7ed5ee7ec7585f4ea48e2a53b572be54600851281cd1c693`.

Lean 4.30.0 locked project build passed (53 jobs). Audited declarations use only the permitted baseline; exact dependencies are in `CLAIMS.json`. Typed control-target CNOT records round-trip through literal `CX` gate records, and their executable decoding and distinct-wire replay agrees with typed execution. For a successful modeled Gaussian program, replaying its encoded reversed CNOT sequence on a Boolean basis vector yields the matrix-applied vector.

This does not establish that Python's compiler produces the same list, quantum amplitude semantics, full circuit replay, operational costs, or any labeled manuscript theorem.
