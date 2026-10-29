# Exact native replay preserves addition

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactReplayLinearity.lean` SHA-256 `c45f6168385268b89861a5509b3b9a2d9f018d34319c138a3c1ba7a7808d606a`.

Lean 4.30.0 locked project build passed (76 jobs); all three declarations use `[propext, Classical.choice, Quot.sound]`. Accepted gates increment the shared denominator exponent exactly for H. For any finite native gate list, replay of the sum of equal-denominator states equals the sum of their replays, with rejection represented by `Option` on both sides.

This proves addition preservation, not coefficient homogeneity or arbitrary-state Toffoli action. Arbitrary wire relabeling, complex embedding, Python correspondence, full circuit behavior, cost and all labeled manuscript theorems remain open.
