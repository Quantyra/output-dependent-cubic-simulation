# Mask parity in normalization

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/MaskParity.lean` SHA-256 `3c18374def2013f09411c23485e9a2504865e7bad8d6880c1404dce7aa98bb2f`.

The locked Lean 4.30.0 build passed (110 jobs); the three declarations use `[propext, Classical.choice, Quot.sound]`. For each natural mask, the Lean toggle normalizer returns that mask exactly when the XOR fold of equality tests over the input list is true. The proof handles an arbitrary duplicate-free initial accumulator and continues through the sorted output.

This characterizes the Lean normalizer, not actual Python execution or a proof that the two implementations agree. JSON text parsing, circuit-to-sector identities, costs and all paper theorem labels remain open.
