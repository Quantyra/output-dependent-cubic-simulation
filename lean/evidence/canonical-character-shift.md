# Canonical character coefficient shifts

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalCharacterShift.lean` SHA-256 `c84cdeebc10c2c1b5f7fdd8b02f3352077a5b0dea0d6e215deafeb34a00da1da`.

Lean 4.30.0 checked the two recorded shift declarations in a combined source probe; each reports `propext`, `Classical.choice`, and `Quot.sound`. For matching coefficient-list lengths, XORing an explicitly evaluated linear pair or radical character into the corresponding canonical phase evaluation is equivalent to XORing its coefficients into the canonical phase coefficients. The lemmas cover all finite lists, including mismatched assignment lengths and empty cases, with the stated coefficient length condition.

These are list-level identities. Connecting the character to the standard finite-vector dot product, deriving its whole Walsh sum, arbitrary-source canonicalization, rank, affine support and elimination costs remain open. No labeled manuscript theorem is certified.
