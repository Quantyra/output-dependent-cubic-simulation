# Canonical Walsh phase in source ANF

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalSourceANF.lean` SHA-256 `8fbc568a9c3ea2af596ef1206376403c8b821a9be38bcd99dc9571c11f51ed75`.

Lean 4.30.0 checked all six declarations locally; each reports `propext`, `Classical.choice`, and `Quot.sound`. Given canonical pair and radical coefficients of the stated lengths and a constant bit, the construction produces degree-at-most-two source bit-mask ANF. Its evaluation equals the canonical finite-vector phase, and its zero-character integer Walsh sum has the exact canonical zero-or-signed-power-of-two form. Zero dimensions, constants and lower terms are included.

This constructs ANF from already canonical coefficients; it does not transform an arbitrary source quadratic to canonical coordinates, prove general affine support, polar rank, sign representation for every character, or elimination complexity. The full paper Walsh lemma and all other labeled paper theorems remain uncertified.
