# Native cubic layer replay

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CubicLayerReplay.lean` SHA-256 `65293a127342c01dc8db61af02ea59196aa197954df35b2be2bb1bbe13434f31`.

The locked Lean 4.30.0 build passed (90 jobs). Negation and cubic-sign congruence use `[propext, Quot.sound]`, replay concatenation uses `[propext]`, and both layer correctness declarations use `[propext, Classical.choice, Quot.sound]`. For any finite list of injectively selected three-wire blocks, native replay of the concatenated mapped cubic programs succeeds and matches the corresponding sequential modeled cubic signs at every exact output amplitude. The wire selections may differ between blocks.

The ideal layer has not yet been connected to the manuscript phase encoding or the full Python compiler. Complex embedding, complete circuit behavior, costs and all labeled manuscript theorems remain open.
