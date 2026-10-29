# Modeled Fourier pairing sign

Target: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/MatrixPairing.lean` SHA-256 `57f14b5d6de08f432ccf3d3a0ab19a819bba9b69fa635413c12693af338164ea`.

The locked Lean 4.30.0 build passed (130 jobs), and both declarations are included in the exact axiom audit. Lean proves binary dot parity is symmetric and applies it to the earlier reindexed native Fourier replay: for any successful Gaussian program, each modeled output amplitude is the exact sum over original input vectors with sign parity `x^T J y`, represented as the Boolean dot product of output `x` with `matrixApply J y`. This particular identity does not require symmetry of J.

The result uses the modeled gate records and exact cyclotomic quotient. A standard complex embedding and normalization, refinement of actual Python execution, the quadratic Walsh-support result, sector identities and resource bounds remain unproved. This does not certify any labeled paper theorem.
