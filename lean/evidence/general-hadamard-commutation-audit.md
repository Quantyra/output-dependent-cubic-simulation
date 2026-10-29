# Generalized Hadamard commutation

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardGeneral.lean` SHA-256 `5fefc93dc5d9d0a658827551e7575fe59f2b3ec9f742b6da7e6bc31ff5a78a42`.

Lean 4.30.0 locked project build passed (62 jobs); each declaration uses `[propext, Quot.sound]`. A generalized Hadamard numerator and its scaled version commute with a disjoint CNOT and with a flip-invariant diagonal multiplier under the stated distributivity and scalar commutation assumptions. The statements quantify over arbitrary coefficient types and an arbitrary scale.

The assumptions have not yet been instantiated for complex T/TDG phases or the physical normalization constant. Literal decomposition replay, Python correspondence, full circuit semantics, cost and all labeled manuscript theorems remain open.
