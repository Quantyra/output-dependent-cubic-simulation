# Canonical pair assignments and finite vectors

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalPairVectors.lean` SHA-256 `3a655118aae45c81c2fb8a04511bb95f580207add15f65dd58550c6c0d19501b`.

Lean 4.30.0 checked all six declarations locally with the axiom sets in the claim inventory. A pair assignment of length `n` corresponds uniquely to two finite binary vectors of dimension `n`; extracting and reconstructing the coordinate lists round-trips, including `n=0`. This complements the earlier radical-list/vector correspondence.

The pair is represented as two vectors, not yet as a single `2n`-coordinate vector. The canonical phase evaluation is not yet connected to source ANF or to a computed canonical basis for arbitrary quadratics. Polar rank, general affine support and elimination costs remain open. No labeled paper theorem is certified.
