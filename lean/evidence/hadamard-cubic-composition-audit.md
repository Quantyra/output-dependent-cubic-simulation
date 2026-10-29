# Hadamard congruence and cubic sign composition

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardAmplitudeCongruence.lean` SHA-256 `6083c57c8aef22c3995c25ba7ea9edbbfac9529d487b1657d303b9454eada747`.

The locked Lean 4.30.0 build passed (88 jobs); all four declarations use `[propext, Classical.choice, Quot.sound]`. State subtraction corresponds to quotient subtraction, and the modeled Hadamard preserves pointwise exact-amplitude equality. Combining this congruence with selected-wire typed Toffoli correctness and the ideal H-Toffoli-H identity proves the composed typed sequence yields the modeled cubic-sign amplitude for any injectively selected three wires and represented state.

Native replay of the complete composition, Python compiler correspondence, complex embedding, full circuit behavior, costs and all labeled manuscript theorems remain open.
