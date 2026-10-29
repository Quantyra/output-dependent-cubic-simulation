# One-wire basis Walsh kernel

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardBasisKernel.lean` SHA-256 `36c5993b0d4b0c8c335183552eed3cf44452fc6a3ce8872dcc1780cc600b3cb8`.

The locked Lean 4.30.0 build passed (123 jobs); both declarations use `[propext, Classical.choice, Quot.sound]`. For an arbitrary point-supported exact-amplitude basis term, Lean proves that a single Hadamard has support only at the basis vector or its selected-wire flip, with the exact Hadamard scale and a negative sign precisely when both input and output bits are one. The arbitrary-state one-wire result is the finite sum of these contributions over the explicit binary basis.

The multi-wire product/closed Walsh sum, complex embedding, Python correspondence, sector identities, costs and all paper theorem labels remain open.
