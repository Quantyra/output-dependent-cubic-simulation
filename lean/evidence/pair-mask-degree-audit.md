# Pair-mask degree bound

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/QuadraticMasks.lean` SHA-256 `fd00f66649390f3f8ff4ecb86a9a3637156a722ee0006428d3aa30c9b8f17ec3`.

Lean 4.30.0 with locked dependencies: `lake build` passed (21 jobs), and the 41-declaration axiom audit passed. `pairMask_degree` proves the actual source mask selecting either of two finite indices has degree at most two, including equal indices. It uses the finite range's no-duplicates property and a general two-choice list bound. Both declarations use `[propext, Classical.choice, Quot.sound]`, within the baseline.

This does not yet bound all output terms or compose the result with the cubic phase derivative construction. Cost, native circuit decoding, sector identities and all seven labeled paper theorems remain open.
