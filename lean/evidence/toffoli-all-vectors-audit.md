# Three-wire Toffoli correctness for all output vectors

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ToffoliAllVectors.lean` SHA-256 `fd482bc5eead85541b58f2c03f0526796d42f0eb895987f8cd1f87725b9cfb54`.

The locked Lean 4.30.0 build passed (84 jobs). Surjectivity of the three-bit basis enumeration uses `[propext, Quot.sound]`; the Toffoli theorem uses `[propext, Classical.choice, Quot.sound]`. Every represented three-wire input state has a single successful literal Toffoli replay result whose exact amplitude equals the modeled ideal action at every Boolean output vector.

Arbitrary-wire generalization, complex embedding, Python record correspondence, full circuit behavior, costs and all labeled manuscript theorems remain open.
