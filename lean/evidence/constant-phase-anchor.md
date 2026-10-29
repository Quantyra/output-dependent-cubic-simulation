# Constant-phase anchor alignment

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698.
SHA-256 `lean/SectorSimulation/ModeledFourier.lean`: `f86428ff1264e2b1cfe9bc172af43ec58c58685e50898c02869ced49a25a632c`.
SHA-256 `lean/ModeledRecognizerExamples.lean`: `3c75f9de750a81f5f0d9e57147e5b7a7ba6a3b42564ab959e27e02a2b712e54e`.

The modeled compiler now chooses wire zero for constant-phase records, as does the published Python compiler, even when the output wire differs. Its existing exact native replay theorem was rebuilt with the new anchor. A Lean finite regression example checks a validated two-wire descriptor with a constant first phase and output wire one.

The locked Lean 4.30.0 build passed (105 jobs); the modeled-recognizer examples and existing exact axiom audit passed. This addresses only the constant-phase wire choice. It does not prove full Python compiler or recognizer correspondence, phase normalization, JSON/ASCII serialization, Gaussian ordering, normalized Fourier semantics, or any labeled paper theorem.
