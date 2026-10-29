# Modeled recognizer conditional completeness

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ModeledRecognizerCompleteness.lean` SHA-256 `44e62a85a6d35a258d9e78c1a4437f8719cec6754e16293b0a4e9343f4df27e5`.

The locked Lean 4.30.0 build passed (105 jobs); all six declarations use `[propext, Classical.choice, Quot.sound]`. Modeled recognition is equivalent to successful validated decoding, Gaussian program generation and exact body equality. A numeric-byte header whose ASCII and JSON contents decode to a validated descriptor round-trips; for any such descriptor a Gaussian program and compiler-produced body exist, and that header plus body is recognized.

Byte/JSON decoding to the descriptor is an explicit hypothesis: this does not construct a serializer, prove Python correspondence, or recognize arbitrary equivalent gate lists. Normalized Fourier and complex semantics, basis preparation, runtime, full costs and all labeled manuscript theorems remain open.
