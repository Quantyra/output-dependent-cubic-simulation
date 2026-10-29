# X and Z amplitude actions and constant phase

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PhaseGateAmplitude.lean` SHA-256 `0bca68b341552a4223a7d7c58567f7bb80c5fb7e0a0f719814b66b849cc8cfad`.

Lean 4.30.0 locked project build passed (55 jobs). The four declarations use `[propext, Quot.sound]`. X and Z are modeled on basis-indexed coefficient functions; X is involutive and Z is involutive when negation is. In execution order the modeled X Z X Z sequence gives global negation on every amplitude, matching the compiler's intended constant-phase effect.

This does not yet connect the X and Z functions to native record decoding or Python execution, prove Hadamard and multiwire phases, normalization, full circuit semantics, cost, or any labeled manuscript theorem.
