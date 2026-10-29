# Literal three-wire Toffoli non-H record trace

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ToffoliRecordTrace.lean` SHA-256 `37ca3382863b2d6db74f5307aa88218f1c80cda1c111df121c4c9d62878de1b8`. The copied 15-record list corresponds to `src/check_acceptance_estimator.py:254`, specialized to wires 0, 1 and 2.

Lean 4.30.0 locked project build passed (60 jobs). Both declarations use `[propext]`. An executable symbolic interpreter traces the CX, T and TDG records after filtering out both H records; on all three-bit inputs it restores the bits and produces the modeled cubic sign exponent modulo eight. Kernel reduction, not native evaluation, discharges the finite cases.

Filtering out H does not justify moving the second H past later control-only gates. This is not a proof of H commutation, complex amplitudes or normalization, general wire relabeling, Python equivalence, full circuit semantics, cost or any labeled manuscript theorem.
