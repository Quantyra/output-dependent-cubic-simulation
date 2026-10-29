# Native cubic layer and Boolean ANF

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CubicLayerANF.lean` SHA-256 `a5ea92523d273781d888d278787ec92523c1c2c7d5c600d8a5cc0ee123902e0b`.

The locked Lean 4.30.0 build passed (91 jobs). The mask evaluation and ideal layer declarations use `[propext, Quot.sound]`; native replay correctness uses `[propext, Classical.choice, Quot.sound]`. The selected triples map to Boolean monomial masks in the existing ANF representation. For any finite list of distinct-wire blocks, native replay succeeds and each exact output amplitude equals the input numerator signed by the XOR of the corresponding cubic monomials, at the original denominator. Repeated monomials are retained and cancel through XOR.

This covers triple blocks only. Constant, linear and quadratic compilation, full Python compiler correspondence, complex embedding, complete circuit behavior, costs and all labeled manuscript theorems remain open.
