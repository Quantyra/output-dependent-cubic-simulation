# Full raw-validator preservation under normalization

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ValidatedRawNormalization.lean` SHA-256 `ddd4ae975e86f4706519171d40910ce0d456d71cf8be5939619bd39f382bcea2`.

The locked Lean 4.30.0 build passed (114 jobs). The wrapper accept/reject declarations use `[propext, Quot.sound]`; the preservation theorem uses `[propext, Classical.choice, Quot.sound]`. For every raw descriptor accepted by the complete Lean raw validator, the normalized raw descriptor also passes that validator. The validation-first wrapper still rejects invalid original descriptors, including those that might normalize to valid ones.

This does not prove correspondence with actual Python execution or connect the wrapper to the recognizer. JSON parsing, circuit-to-sector identities, costs and all paper theorem labels remain open.
