# Validation before normalization

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ValidatedRawNormalization.lean` SHA-256 `7613f351cedf4857233dce83c31574856631544ed3de0d9bbc7e8bc5e267585d`.

The locked Lean 4.30.0 build passed (114 jobs); both declarations use `[propext, Quot.sound]`. The Lean wrapper first runs the existing raw descriptor validator, returning none when it rejects, and otherwise returns the normalized raw descriptor. This ensures invalid raw masks are not silently removed before that validation.

The wrapper does not prove the normalized descriptor passes the complete validator, nor does it change the existing recognizer. Python refinement, JSON parsing, circuit-to-sector identities, costs and all paper theorem labels remain open.
