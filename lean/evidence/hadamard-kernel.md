# Recursive exact Hadamard kernel

Target: source-to-Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardKernel.lean` SHA-256 `3054232d373221d4eb4f60e943c940a7fb445eea3b9a0ab3fd3313118c82b719`.

The locked Lean 4.30.0 build passed (117 jobs). Four declarations have exact transitive axioms in the project audit baseline. Lean defines a normalized two-branch exact-amplitude update and its iteration over wires, proves it equals the replayed Hadamard sequence for every state, tracks the shared denominator exponent, and connects it to the Python-ordered native Fourier record replay through the computed CNOT input action.

This recursive representation is not yet identified with the closed normalized Walsh sum or physical complex amplitudes. Python correspondence, circuit-to-sector identities, costs and all paper theorem labels remain open.
