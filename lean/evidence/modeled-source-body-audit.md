# Native replay of the modeled source body

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ModeledFourier.lean` SHA-256 `a48a283be5dfef8aab3879ac2c8414ddf90e38ca3a288a4ab55566473e52415e`.

The locked Lean 4.30.0 build passed (101 jobs). CNOT amplitude, CNOT congruence, native transform replay and phase congruence use `[propext, Quot.sound]`; modeled transform congruence and source-body correctness use `[propext, Classical.choice, Quot.sound]`. For a degree-checked source descriptor and successful Gaussian row program, the executable modeled body compiler returns native records whose replay matches, at every exact amplitude, three modeled all-wire-Hadamard/linear transforms interleaved with the two source phase signs. This applies to arbitrary represented initial states.

The modeled transform is not yet identified with the manuscript normalized Fourier kernel or embedded into complex amplitudes. Python compiler and identity-header correspondence, basis-input preparation, runtime, full costs and all labeled manuscript theorems remain open.
