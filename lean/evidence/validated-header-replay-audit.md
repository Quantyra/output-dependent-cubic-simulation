# Validated numeric-byte header and native replay

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ValidatedHeaderReplay.lean` SHA-256 `f5db5fec326318158f580e9482b69e8269cd7b489b34e0e44f39d62b953c32ca`.

The locked Lean 4.30.0 build passed (103 jobs); all three declarations use `[propext, Classical.choice, Quot.sound]`. A successfully decoded validated JSON descriptor has a numeric-byte header prefix. If its remaining body equals the Lean modeled compiler output for a successful Gaussian program, the complete native gate list replays to the modeled body amplitudes. Under the same hypotheses the existing output-derivative computation also succeeds with its stated degree and length bounds.

Matching the body to the Lean compiler is an explicit hypothesis, not a proof about arbitrary decoded bodies or Python. Python recognizer/compiler correspondence, normalized Fourier and complex semantics, basis preparation, runtime, full costs and all labeled manuscript theorems remain open.
