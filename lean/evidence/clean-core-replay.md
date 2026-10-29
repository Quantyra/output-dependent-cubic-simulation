# Clean-checkout replay of the core Lean helpers

The local repository was cloned into a separate clean checkout from commit `6b5e070` after the paper's first publication. This snapshot contains the core-only Lake manifest; it does not yet contain a locked Mathlib dependency. Lean 4.30.0 and Lake 5.0.0 were invoked from the verified local toolchain.

`lake build` exited 0 and reported successful builds of `SectorSimulation.Derivative`, `SectorSimulation.BinaryShift`, and `SectorSimulation` (five jobs). `lake env lean Audit.lean` exited 0, printing the elaborated declarations and the same transitive axiom reports as the original checkout:

- `SectorSimulation.booleanDerivative_shift_invariant`: no axioms.
- `SectorSimulation.binaryShift_involutive`: `Quot.sound`.
- `SectorSimulation.binaryDerivative_shift_invariant`: `Quot.sound`.

This replay verifies those three declarations under the Lean kernel and the stated baseline. It does not certify the published sector proposition, the source compiler, the estimator or the runtime theorem. Mathlib locking, exact statement-to-declaration bridges, complete paper coverage and the successor audit remain open.
