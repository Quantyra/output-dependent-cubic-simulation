# Toggle-and-sort ANF normalization

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ToggleMaskNormalization.lean` SHA-256 `cc736892bedfebc889cd307a81c2767ab3ef378248ea0c815df04676739772a3`.

The locked Lean 4.30.0 build passed (109 jobs). Exact transitive axioms for all nine declarations are recorded in the project audit baseline. The executable Lean normalizer toggles natural masks in a list and sorts the result. For every width and input, Lean proves it preserves ANF evaluation; its output is duplicate-free and ascending. The fold proof covers any initial accumulator.

This is a formal Lean model of the toggle-and-sort behavior, not a verified refinement of Python or a proof that its output equals Python set normalization. Text serialization, circuit-to-sector identities, costs and all paper theorem labels remain open.
