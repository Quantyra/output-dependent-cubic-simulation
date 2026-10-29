# Exact three-wire Toffoli basis replay

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ToffoliBasisReplay.lean` SHA-256 `b9b7ec0ecbf6832685228d06bddc91aafb4747fa9649c29fce6c7a6a08964236`; copied gate list in `lean/SectorSimulation/ToffoliRecordTrace.lean` corresponds to `src/check_acceptance_estimator.py:254` specialized to wires 0, 1, 2.

Lean 4.30.0 locked project build passed (74 jobs). The exhaustive check uses `[propext]`; the explicit quotient-amplitude theorem uses `[propext, Quot.sound]`. Kernel reduction checks all 64 input/output basis entries of the complete 15-record list under the exact native interpreter, including both normalized Hadamards. Every represented basis input is mapped to the ideal Toffoli basis output without an extra phase. No native evaluation is used.

General-state linearity, arbitrary wire relabeling, complex embedding, proof that Python produces this list, full circuit behavior, cost and all labeled manuscript theorems remain open.
