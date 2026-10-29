# Source matrix linearity

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/MatrixLinearity.lean` SHA-256 `a85d189d44a5e68b436584eecf8c6ba0690e5dc69d585f4389a4500a98a14db1`.

Lean 4.30.0 with locked dependencies: `lake build` passed (24 jobs), and the 50-declaration axiom audit passed. The fold lemma uses `propext`; matrix application preserves coordinatewise XOR and maps zero to zero using `[propext, Quot.sound]`. The proofs apply to the actual finite-list XOR/AND evaluator and arbitrary matrices, including zero dimensions.

These results do not establish invertibility, computation of the output shift, native decoder/gate semantics, or a labeled manuscript theorem.
