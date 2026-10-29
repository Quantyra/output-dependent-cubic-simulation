# Occurrence-count characterization

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/MaskCountParity.lean` SHA-256 `3740cd1c38458678d32946411e7b5809c6e3d772133e2e89ad67e4a8be436080`.

The locked Lean 4.30.0 build passed (111 jobs). The parity/count theorem uses `[propext, Quot.sound]`; the sorted membership theorem uses `[propext, Classical.choice, Quot.sound]`. For every natural mask and finite input list, the mask belongs to the sorted Lean normalizer output if and only if its input occurrence count is odd.

This characterizes the Lean normalizer, not actual Python execution or formal Python refinement. JSON text parsing, circuit-to-sector identities, costs and all paper theorem labels remain open.
