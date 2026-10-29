# Canonical Walsh sum over finite vectors

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalVectorWalsh.lean` SHA-256 `7bca019d860193b8d8fb58435fe003ce86777fe65275710145a8748a3c4d12b7`.

Lean 4.30.0 checked all 11 declarations locally with the exact axiom sets in the claim inventory. The combined `(k+k)+m` binary-vector basis maps bijectively to the generated radical and pair assignment lists; the two enumerations are proved permutations. Reindexing their integer sums yields the canonical quadratic/linear phase sum over the exhaustive finite-vector basis and its exact zero-or-signed-power-of-two closed form, including zero dimensions and either constant bit.

This is the canonical-coordinate phase explicitly defined here. It is not yet connected to source ANF or an algorithm constructing a canonical basis for arbitrary quadratics, nor does it establish polar rank, general affine Walsh support or elimination complexity. No labeled paper theorem is certified.
