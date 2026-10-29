# Exact recursive Hadamard kernel linearity

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardKernelLinearity.lean` SHA-256 `c3be4b70feb67dc3c16e531986792b113cf608a7e14b3b1259c726246f393615`.

The locked Lean 4.30.0 build passed (120 jobs); all eight declarations have exact transitive axioms in the project audit baseline. Lean proves additivity and scalar homogeneity for both a single exact Hadamard kernel step and the iterated kernel over any wire list, together with the necessary exact-amplitude sign and commutation identities.

This is linearity of the existing recursive kernel, not its closed normalized Walsh-sum identification or physical complex semantics. Python correspondence, sector identities, costs and all paper theorem labels remain open.
