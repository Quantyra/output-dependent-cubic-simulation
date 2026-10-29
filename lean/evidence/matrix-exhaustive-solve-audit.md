# Exhaustive finite matrix-equation reference

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExhaustiveMatrixSolve.lean` SHA-256 `bbefe84400f9950fbdd23d2ba645d8c58df51a40e490f6cefde3aa9daf9a5633`.

Lean 4.30.0 with locked dependencies: `lake build` passed (25 jobs), and the 54-declaration axiom audit passed. The explicit recursive list contains every Boolean vector; finite coordinate comparison is exact; searching the list yields a solution only if the actual source matrix equation holds and returns one whenever a solution exists. All four audited declarations use `[propext, Quot.sound]`. This applies to singular matrices and zero dimensions as well as invertible cases.

The list doubles at every dimension, so this is an exponential reference construction, not the paper's efficient elimination algorithm or an operational cost proof. Invertibility, output-index specialization, native decoder and gate semantics, and all labeled manuscript theorem certifications remain open.
