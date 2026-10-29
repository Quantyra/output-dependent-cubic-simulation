# Canonical quadratic Walsh sum

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalWalsh.lean` SHA-256 `f8355d3a60b1e2d4a57d22da73c2df722e938b57f4efcf189e07bc1ecb1a227a`.

Lean 4.30.0 checked all four declarations locally; their reported transitive axioms are `propext` and `Quot.sound`. For an arbitrary list of hyperbolic pair coefficients and constant bit, the recursively enumerated signed integer sum equals `2^k` times the quadratic sign given by the XOR of coefficient products. Adding arbitrary radical-coordinate coefficients yields zero whenever one is nonzero, and otherwise yields the signed value `2^(k+m)`. Zero pairs and zero radical coordinates are included. Lean also proves that the sum is zero exactly when a radical coefficient is nonzero, and gives its natural absolute value in both cases.

The recursive sum is an abstract canonical-coordinate enumeration. It is not yet connected to arbitrary quadratic ANF, a computed invertible basis, polar rank, affine Walsh support or elimination complexity. This does not certify the paper lemma or any other labeled paper theorem.
