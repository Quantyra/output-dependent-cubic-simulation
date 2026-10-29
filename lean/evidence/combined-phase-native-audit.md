# Combined native phase layer and ANF

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CombinedPhaseNative.lean` SHA-256 `34844db2880bef4b331b1fbcab39213c19dc41fcf5d9e40f1464b3369fbd45ff`.

The locked Lean 4.30.0 build passed (93 jobs). The ideal lower phase evaluation uses `[propext]`, its exponent theorem uses no axioms, and combined native correctness uses `[propext, Classical.choice, Quot.sound]`. For any finite list of valid constant, linear and distinct-wire quadratic blocks followed by any finite list of injectively selected cubic blocks, the mapped native replay succeeds and its exact amplitudes equal the input amplitudes signed by the XOR evaluation of the combined Boolean ANF. Duplicate monomials cancel through XOR. Constant terms require an available wire.

The theorem applies to the constructed term lists; coverage and compilation of arbitrary source ANF descriptors, full Python compiler correspondence, complex embedding, complete circuit behavior, costs and all labeled manuscript theorems remain open.
