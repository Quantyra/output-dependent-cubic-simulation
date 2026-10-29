# Exact replay denominator shift and Toffoli basis bridge

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactReplayShift.lean` SHA-256 `0c2593e54a876a4f3829e05b5875cce016b93502ce0249d7b11dc8c775775049`.

Lean 4.30.0 locked project build passed (78 jobs). Both shift declarations use `[propext, Quot.sound]`; the Toffoli basis bridge uses `[propext, Classical.choice, Quot.sound]`. The interpreter and finite replay commute with adding a natural amount to a state's shared denominator exponent, including rejection. Combined with coefficient scaling, this gives an exact structural replay identity for any coefficient-scaled and denominator-shifted three-bit basis input, tied to an unscaled basis output with the previously established ideal amplitude equality.

The bridge does not itself prove equality of the scaled shifted output amplitude to the ideal scaled shifted output, or general arbitrary-state Toffoli correctness. Wire relabeling, complex embedding, Python correspondence, full circuit behavior, costs and all labeled manuscript theorems remain open.
