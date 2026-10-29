# Canonical quadratic Walsh sum

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalWalsh.lean` SHA-256 `d1f058c2b8af78ac7295699990e2e08d9202bd25d376c067ec82858fff7aee37`.

Lean 4.30.0 checked both declarations locally; their reported transitive axioms are `propext` and `Quot.sound`. For an arbitrary list of hyperbolic pair coefficients and constant bit, the recursively enumerated signed integer sum equals `2^k` times the quadratic sign given by the XOR of coefficient products. Adding arbitrary radical-coordinate coefficients yields zero whenever one is nonzero, and otherwise yields the signed value `2^(k+m)`. Zero pairs and zero radical coordinates are included.

The recursive sum is an abstract canonical-coordinate enumeration. It is not yet connected to arbitrary quadratic ANF, a computed invertible basis, polar rank, affine Walsh support or elimination complexity. This does not certify the paper lemma or any other labeled paper theorem.
