# Quadratic term to source bit-mask translation

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/QuadraticMasks.lean` SHA-256 `027d6c5f255efa461e98d217b29de508404e7b692738808406a3d68655050164`.

Under Lean 4.30.0 and the locked dependency manifest, `lake build` completed successfully (14 jobs). The 39-declaration `lake env lean Audit.lean` axiom report and exact baseline checker passed. Singleton and pair masks evaluate to the corresponding Boolean terms, including repeated coordinates; the term translation and the map over an entire list preserve evaluation. The four translation declarations depend on `[propext, Quot.sound]`; `evalPhase_cons` depends on `[propext]`.

This is an evaluation bridge, not yet a proof that output masks have degree at most two or a composition with the cubic derivative constructor. Resource bounds, native circuit decoding, Walsh support, sector identities and all seven labeled manuscript theorems remain open.
