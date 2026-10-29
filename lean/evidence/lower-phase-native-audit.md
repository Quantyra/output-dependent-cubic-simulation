# Native lower-degree phase blocks

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/LowerPhaseNative.lean` SHA-256 `aa7fed4c95fd7774ca85952f4e12ff4d092d7ac1a32dd990df0ac4a99aedda30`.

The locked Lean 4.30.0 build passed (92 jobs). The constant-sign and monomial-congruence declarations use `[propext, Quot.sound]`; the other three use `[propext, Classical.choice, Quot.sound]`. Native blocks for a constant sign, Z linear sign and H-CNOT-H quadratic sign match their Boolean monomial signs, and finite lists of valid blocks replay successfully and match the sequential modeled monomial-sign layer. Constant terms require an available wire; quadratic wires must differ.

The lower-degree layer is not yet connected to combined ANF evaluation and the cubic layer. Full Python compiler correspondence, complex embedding, complete circuit behavior, costs and all labeled manuscript theorems remain open.
