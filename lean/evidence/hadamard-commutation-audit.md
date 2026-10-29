# Unnormalized Hadamard commutation

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardCommutation.lean` SHA-256 `b15fc5c06a7f7f9e822acf52b252b524ae2836cb612ebcd74302d5e20d9f4d6c`.

Lean 4.30.0 locked project build passed (61 jobs); each declaration uses `[propext, Quot.sound]`. On integer coefficient functions, the unnormalized Hadamard commutes with flip-invariant Boolean signs and with a CNOT whose control and target differ from the Hadamard wire. The underlying CNOT/bit-flip commutation is also proved.

This does not cover complex T/TDG phases, normalization, literal decomposition replay, Python execution equivalence, full circuit behavior, cost, or any labeled manuscript theorem.
