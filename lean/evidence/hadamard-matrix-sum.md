# Matrix-indexed exact Fourier sum

Target: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardMatrixSum.lean` SHA-256 `7a1147ddedcb3d4c50386c9a6b87cf81a2dd55afb31e416668c02798dec61842`.

The locked Lean 4.30.0 build passed (129 jobs). Four declarations were checked in the project axiom audit. For any successful Gaussian row program and finite width, Lean proves that its forward CNOT program is an inverse of the input matrix, that applying the matrix permutes the exhaustive binary basis, and that an exact finite sum is invariant under permutation. Consequently modeled Python-order native Fourier replay has the exact Walsh sum indexed by the original input basis, with sign parity computed from the matrix-applied input and the output vector.

This result is in the exact cyclotomic quotient and assumes the modeled gate records; it does not yet identify this parity with the manuscript bilinear pairing, embed the amplitudes in standard complex numbers, prove actual Python refinement, establish the quadratic Walsh-support or sector identities, or prove resource costs. No labeled paper theorem is certified by this increment.
