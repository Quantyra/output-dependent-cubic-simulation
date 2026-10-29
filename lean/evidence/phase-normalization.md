# Boolean phase normalization lemmas

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PhaseNormalization.lean` SHA-256 `01a47f15d5efb5f96d68a9e138d63be38a989ad74cce78013c400862a48ab770`.

The locked Lean 4.30.0 build passed (108 jobs). `evalPhase_perm` uses `[propext]`; `evalPhase_cancel_separated` uses `[propext, Quot.sound]`. The first proves that any permutation of a represented ANF phase leaves evaluation unchanged; the second proves that two equal masks can be removed at arbitrary positions, with all other masks retained.

These are mathematical ingredients for phase normalization, not a verification of the Python toggle-set algorithm, its sorting, serializer, native compiler, or any manuscript theorem. The circuit-to-sector bridge, costs and all paper labels remain open.
