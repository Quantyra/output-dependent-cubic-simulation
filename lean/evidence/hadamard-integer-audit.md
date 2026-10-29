# Unnormalized Hadamard and controlled sign

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardInteger.lean` SHA-256 `dfe8c5170c554f178e14c9452f4b2f082a77dfb7afc1ebc493258305b27c710a`.

Lean 4.30.0 locked project build passed (57 jobs). Both declarations use `[propext, Quot.sound]`. For integer coefficient functions, the unnormalized Hadamard numerator squared equals twice the original amplitude, and the unnormalized target-Hadamard, CNOT, target-Hadamard sequence yields twice the controlled-sign amplitude for distinct wires. An initial incorrect sign in the candidate Hadamard definition was exposed by the proof and corrected before the successful build.

The scalar factor two is explicit: this does not prove normalized complex Hadamard semantics, native H record replay, cubic phases, Python compiler equivalence, full circuit behavior, cost, or any labeled manuscript theorem.
