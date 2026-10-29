# Raw two-phase descriptor normalization

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/RawDescriptorNormalization.lean` SHA-256 `83bee578ca7b534340e66866afb92db5da4275c256bd1d5f8772ad79b872e0d5`.

The locked Lean 4.30.0 build passed (113 jobs). Seven declarations have exact transitive axioms recorded in the project audit baseline. Normalization retains both Boolean phase functions, width, pairing rows, basis and output, is idempotent, and preserves already satisfied mask-width and phase-degree checks. Every retained mask came from the input.

This does not establish that the full raw validator accepts the normalized descriptor, that the actual Python implementation is equivalent, or that JSON parsing, circuit-to-sector identities, costs or any paper theorem is certified. Original-input validation must still occur before normalization to match Python rejection behavior.
