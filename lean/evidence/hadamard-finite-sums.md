# Hadamard kernel over finite sums

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardFiniteSums.lean` SHA-256 `985a4fd3441295d9f5c75af22d6aa17354fdd457397b28c30b8d8822a3888f0e`.

The locked Lean 4.30.0 build passed (121 jobs); five declarations have exact transitive axioms in the project audit baseline. The exact quotient has a proved additive zero, zero negation and multiplication by zero. The recursive Hadamard kernel maps zero to zero and distributes over any finite list of amplitude functions, including the empty list.

This does not yet construct the computational-basis decomposition or identify the kernel with the closed normalized Walsh sum or physical complex amplitudes. Python correspondence, sector identities, costs and all paper theorem labels remain open.
