# Pivot selection and candidate row program

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source at commit `129b808`, `lean/SectorSimulation/GaussianPivot.lean`, SHA-256 `fa0f80437281936708dbeb28fe09232a1fccfa790780c31ce6cf73f07ea47325`.

Lean 4.30.0 with locked dependencies: `lake build` passed (29 jobs), and the 65-declaration axiom audit passed. Pivot search returns only an eligible row with a set entry and failure excludes every eligible set entry. The first theorem uses `propext`; the second uses `[propext, Quot.sound]`. A recursive candidate program selects pivots, swaps rows and emits column-clearing operations, using the already verified row-program interpreter.

The candidate program's reduction invariants, invertible-input completeness, finite examples and operational cost have not yet been established. Function-valued matrices do not by themselves provide a polynomial-cost implementation. No labeled manuscript theorem is certified.
