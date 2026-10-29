# Native replay of the cubic-sign block

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/MappedNativeCubic.lean` SHA-256 `e0a7eeeef8f3ebc4ea69151ad95c5c64e5891dd0ec4853299b269b11c9b93803`.

The locked Lean 4.30.0 build passed (89 jobs). Program concatenation uses no axioms; validity uses `[propext, Quot.sound]`; the action identity uses `[propext]`; native cubic correctness uses `[propext, Classical.choice, Quot.sound]`. The mapped native record list for Hadamard, Toffoli decomposition and Hadamard succeeds on any represented state and any three distinct selected wires, with exact output amplitudes equal to the modeled cubic sign at every output vector.

Full Python compiler correspondence, complex embedding, complete circuit behavior, costs and all labeled manuscript theorems remain open.
