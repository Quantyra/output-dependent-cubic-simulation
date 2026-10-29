# CNOT amplitude reindexing

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CNOTAmplitude.lean` SHA-256 `b0da436b298ad9bfd2a27e898581bd90804d0175685d444831a0e61afe28886a`.

Lean 4.30.0 locked project build passed (54 jobs). Exact audited axioms appear in `CLAIMS.json` and stay within the permitted baseline. A modeled CNOT sequence acts on arbitrary basis-indexed coefficient functions by reverse-order basis reindexing. For a successful modeled Gaussian program, literal encoded native-record replay maps every input coefficient to the basis index obtained by the original binary matrix.

This defines the CNOT amplitude action by reindexing; it does not prove equivalence to Python compiler output or establish Hadamard, phase, normalization, full circuit, probability, cost, or any labeled manuscript theorem.
