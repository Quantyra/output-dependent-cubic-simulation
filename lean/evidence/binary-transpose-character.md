# Binary transpose character

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/BinaryTransposeCharacter.lean` SHA-256 `dc39d290154131d7de6621aa19b8ea0c60239427d533c5ca314b34f64cf1d1ea`.

Lean 4.30.0 checked all three recorded declarations locally. The finite-sum interchange and binary transpose identity report `propext` and `Quot.sound`; the fold identity reports no axioms. For every finite binary matrix and vectors, the standard binary character applied to the matrix-transformed vector equals the character whose coefficient vector is obtained by applying the transpose matrix. No invertibility assumption is required.

This constructs the transformed character needed by the conditional source Walsh result. It does not construct a canonical basis for arbitrary quadratics, prove rank or affine support, establish costs, or certify a labeled manuscript theorem.
