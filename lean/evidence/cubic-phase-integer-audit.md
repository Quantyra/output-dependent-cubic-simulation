# Unnormalized cubic phase via ideal Toffoli

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CubicPhaseInteger.lean` SHA-256 `4a9757b0d0193a498a8fa4597f2f79bcdcf79dd72d83e7dbd1c57690743b6f2b`.

Lean 4.30.0 locked project build passed (58 jobs); the theorem uses `[propext, Quot.sound]`. For integer coefficient functions and each control distinct from the target, unnormalized target-Hadamard, ideal Toffoli, target-Hadamard produces twice the cubic controlled-sign coefficient on every basis vector.

This defines an ideal Toffoli basis action and leaves the factor of two explicit. It does not prove the compiler's actual Toffoli decomposition, normalized complex Hadamard semantics, native replay, Python equivalence, full circuit behavior, cost or any labeled manuscript theorem.
