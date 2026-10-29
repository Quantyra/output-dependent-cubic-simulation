# Exact native replay preserves coefficient scaling

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CycloAssociativity.lean` SHA-256 `12918494e5e84d06d5ff7ad7457cc733abfbfd9e076fc1e31493496e73192f5f`.

Lean 4.30.0 locked project build passed (77 jobs). The CNOT and X scaling declarations use no axioms; the other eight audited declarations use `[propext, Classical.choice, Quot.sound]`. Cyclotomic coefficient multiplication is associative, and each modeled native gate and arbitrary finite replay preserve scaling by any four-integer cyclotomic coefficient, including interpreter rejection. The shared denominator exponent is unchanged by scaling.

This result is limited to integral cyclotomic coefficient scaling; it does not establish general dyadic-scalar homogeneity or arbitrary-state Toffoli action. Arbitrary wire relabeling, complex embedding, Python correspondence, full circuit behavior, costs and all labeled manuscript theorems remain open.
