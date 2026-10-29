# Degree-three source phase coverage

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CubicMaskCoverage.lean` SHA-256 `a0d237eed59ea06733ebf4eae86688c0ab8024e7c3396ed52cfc219bb58cf6bb`.

The locked Lean 4.30.0 build passed (94 jobs). Triple values use `[propext]`, triple injectivity uses `[propext, Quot.sound]`, and the other four declarations use `[propext, Classical.choice, Quot.sound]`. For any degree-at-most-three Boolean phase list and an available wire, valid lower-degree and cubic block lists exist with identical Boolean evaluation; consequently native records exist whose exact replay implements that phase on every represented input state. Duplicate source masks are preserved semantically by XOR.

This is an existence proof, not a verified executable compiler or Python correspondence. It assumes an available wire and does not cover the zero-wire constant case. Complex embedding, complete circuit behavior, costs and all labeled manuscript theorems remain open.
