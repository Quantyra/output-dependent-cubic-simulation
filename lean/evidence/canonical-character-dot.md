# Canonical Walsh sum for every binary character

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalCharacterDot.lean` SHA-256 `b51798f5d391ffdedeca7e28b22bd4b016fea60e7e8f6fd31723184417effee6`.

Lean 4.30.0 checked both declarations in a combined source probe. The dot-product identity reports `propext` and `Quot.sound`; the closed sum reports `propext`, `Classical.choice`, and `Quot.sound`. For every binary character vector, its split canonical pair/radical coefficients define the same character as the standard binary dot product. For any constructed canonical source ANF, summation against that character is zero exactly when the displayed shifted radical test is true and otherwise equals the displayed signed power of two. All finite block dimensions, including zero, are covered.

The input ANF must already have the constructed canonical form; arbitrary-source canonicalization, general rank/support interpretation and elimination costs remain open. The full manuscript Walsh lemma and all other labeled manuscript theorems remain uncertified.
