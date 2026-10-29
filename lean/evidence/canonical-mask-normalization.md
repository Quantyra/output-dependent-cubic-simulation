# Canonical phase normalization

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalMaskNormalization.lean` SHA-256 `b632cb2b675f8339f54e9acfc59b92a2ec4e6a045d6299975554205fa576a787`.

The locked Lean 4.30.0 build passed (112 jobs); the three declarations use `[propext, Classical.choice, Quot.sound]`. For any finite natural-mask input, every sorted duplicate-free candidate with precisely the odd-count members equals the Lean normalizer output. Normalization is invariant under input permutations and idempotent.

The uniqueness result is conditional on a candidate satisfying its hypotheses and does not prove that the Python implementation does so. JSON parsing, compiler correspondence, circuit-to-sector identities, costs and all paper theorem labels remain open.
