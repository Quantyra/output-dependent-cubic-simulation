# Three-bit state decomposition

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ThreeBitDecomposition.lean` SHA-256 `d5cabf175a19b1392382556bae96c99d616a8189bf490bd0ef2d26636857e140`.

The locked Lean 4.30.0 build passed (81 jobs); the decomposition theorem uses `[propext, Quot.sound]`. Every exact shared-denominator three-wire state is equal to the explicitly defined sum of eight computational basis states, each weighted by the original numerator at that basis vector and shifted to the original denominator.

This decomposition is not yet combined with replay to establish arbitrary-state Toffoli action. Arbitrary wire relabeling, complex embedding, Python correspondence, full circuit behavior, costs and all labeled manuscript theorems remain open.
