# Exact normalized Hadamard involution

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactHadamard.lean` SHA-256 `a196cfdcba2a370a5a82c7dac2dd270963e1821c224317aa44579c4029492fe4`.

Lean 4.30.0 locked project build passed (70 jobs). Both audited declarations use `[propext, Classical.choice, Quot.sound]`. For every represented finite state with a shared power-of-two denominator, the defined exact Hadamard updates the numerator by z-z^3 and increases the denominator exponent by one. Applying it twice multiplies the numerator by four and adds two denominator bits; every quotient-valued amplitude is therefore restored exactly.

This is an involution theorem for the defined shared-denominator model. Complex embedding, representation independence, coverage of general quotient-valued states, native gate replay, Python correspondence, norm preservation, full circuit semantics, cost and all labeled manuscript theorems remain open.
