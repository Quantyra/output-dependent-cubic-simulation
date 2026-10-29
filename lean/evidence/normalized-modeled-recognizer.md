# Canonical phase modeled recognizer

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698.
SHA-256 `lean/SectorSimulation/NormalizedModeledRecognizer.lean`: `dd25f92b72c5bd4d9693492abb94993547b77b7029429713e3837fe3a6d30b22`.
SHA-256 `tools/check_python_lean_bridge.py`: `b2cfd6b5c8042f86bf8299e78a7140721d3ca9fba89d873666a9a18c5d7dfb29`.

The locked Lean 4.30.0 build passed (115 jobs); the three declarations have exact transitive axioms recorded in the project audit baseline. The new modeled recognizer validates the raw descriptor before requiring its phase lists to be normalized, then delegates to the existing exact-body recognizer. Acceptance implies its exact replay and derivative results. Conditional completeness holds for an already recognized source whose decoded raw descriptor passes the normalization wrapper unchanged. Five Python-compiled native examples pass both Lean recognizers; a noncanonical duplicate-mask header is rejected by Python and the new recognizer.

The new recognizer does not yet establish canonical JSON-byte equality, Python implementation equivalence, normalized Fourier/complex semantics, input preparation, full costs or any paper theorem. Five examples and one rejection are not a general correspondence proof.
