# Three-wire Toffoli exact replay correctness

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ToffoliIdealSum.lean` SHA-256 `f6f5841aac31ad06185ee6c49a65f3af3a7939bf2a69e289edda24371038d1c8`.

The locked Lean 4.30.0 build passed (83 jobs). The ideal weighted basis exponent declaration uses `[propext, Quot.sound]`; the other four use `[propext, Classical.choice, Quot.sound]`. For any represented exact shared-denominator three-wire state and any of the eight indexed output vectors, literal Toffoli record replay succeeds and its quotient amplitude equals the modeled ideal Toffoli amplitude. The proof combines the eight-component replay sum, weighted basis correctness, quotient addition and the finite ideal permutation.

This result concerns the modeled three-wire record list and exact quotient. Arbitrary-wire generalization, complex embedding, Python record correspondence, full circuit behavior, costs and all labeled manuscript theorems remain open.
