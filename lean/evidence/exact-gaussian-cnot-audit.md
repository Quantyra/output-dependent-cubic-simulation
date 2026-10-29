# Exact native Gaussian CNOT replay

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactGaussianCNOTReplay.lean` SHA-256 `be7a937c3e6eae29dfaafa17cc2b31dcd4d0775e4443168d6ae98518b01d83ed`.

The locked Lean 4.30.0 build passed (99 jobs). The shared CNOT numerator and exponent identities use no axioms; native program replay uses `[propext]`; Gaussian CNOT amplitude transport uses `[propext, Classical.choice, Quot.sound]`. Exact native replay of valid encoded CNOT records agrees with the shared-state action. When Gaussian row reduction succeeds, the reversed encoded CNOT program replays and transports exact amplitudes according to the input binary matrix.

This does not establish the whole Fourier transform or two-layer circuit. Hadamard composition, Python and complex-number correspondence, full runtime, costs and all labeled manuscript theorems remain open.
