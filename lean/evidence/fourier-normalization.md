# Exact Fourier scale and normalization recurrence

Target: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/FourierNormalization.lean` SHA-256 `7c6bd1d2be1b17203cf4acebca734d7e657b7bd17048d5866a44a1277116228d`.

The locked Lean 4.30.0 build passed (131 jobs), and seven declarations are included in the transitive axiom audit. Lean proves exact multiplication has unit one, repeated Hadamard scaling factors through a single width-dependent scalar, and doubling the result after two further scales recovers the original amplitude. It factors that scalar outside the finite input-indexed modeled Fourier sum with the manuscript's binary pairing sign. All results include zero width and assume a successful modeled Gaussian program where applicable.

The scalar is still expressed inside the exact cyclotomic quotient, not as the standard real number 2^(-n/2); complex embedding, positivity and identification of the standard square-root branch remain open. Actual Python refinement, quadratic Walsh support, sector identities and costs also remain open. No labeled manuscript theorem is certified.
