# Pivot existence for an injective matrix

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PivotExists.lean` SHA-256 `0654322d1b39a89d57aae1fee776e0427befc19ae9ef5295f7dc2bba15a41dd2`.

Lean 4.30.0 with locked dependencies: `lake build` passed (39 jobs), and the 100-declaration axiom audit passed. For an injective source matrix whose earlier columns are unit columns, the actual pivot search returns an eligible row. The proof constructs a nonzero kernel vector from the current column and earlier unit columns if search fails. All three declarations depend on `[propext, Classical.choice, Quot.sound]`.

The full consecutive-pivot induction, finite-encoding runtime, native circuit semantics and all labeled manuscript theorem certifications remain open.
