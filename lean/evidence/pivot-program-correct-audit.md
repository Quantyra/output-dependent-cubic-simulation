# Successful pivot programs reduce to identity

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PivotProgramCorrect.lean` SHA-256 `dca4405e2aa17de32607a22709019281e803086dced73ee92ac4a198e836270d`.

Lean 4.30.0 with locked dependencies: `lake build` passed (36 jobs), and the 90-declaration axiom audit passed. The actual full pivot generator, whenever it returns an operation list, reduces the source matrix to the identity when executed. The proof composes the generated operations, shows each successful pivot produces a unit column, and inducts over ordered columns while preserving earlier unit columns. The main theorem uses `[propext, Classical.choice, Quot.sound]`; all six declarations are audited.

Success for every invertible input is not yet proved. The proof does not establish finite-encoding runtime, native circuit semantics, or any labeled manuscript theorem.
