# Binary matrix row programs

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/MatrixRowProgram.lean` SHA-256 `7ad3e43f55368af1a844bf93be222e8d44cfc736fd74242b6938be71d4e62434`.

Lean 4.30.0 with locked dependencies: `lake build` passed (28 jobs), and the 63-declaration axiom audit passed. The executable row-program interpreter folds over swaps and XOR row additions; a same-row addition is a no-op. Every finite program preserves the exact matrix-equation solution set. Both declarations use `[propext, Quot.sound]`.

This establishes composition of row operations, not pivot selection, elimination completeness, invertibility validation, operational cost or any labeled manuscript theorem.
