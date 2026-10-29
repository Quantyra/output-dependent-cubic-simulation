# Injectivity across row programs

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PivotInjectivity.lean` SHA-256 `33e4235b4d59baaecec759a4c29a970bc77cd81dd052a0eb04ed269fac26ec8e`.

Lean 4.30.0 with locked dependencies: `lake build` passed (38 jobs), and the 97-declaration axiom audit passed. The actual row-program interpreter preserves injectivity of the source matrix evaluator. Separately, a successful full pivot program implies the original matrix evaluator is injective. These use `[propext, Quot.sound]` and `[propext, Classical.choice, Quot.sound]`, respectively.

The converse direction, that injectivity guarantees successful pivot generation, is not yet proved. Finite-encoding runtime, native circuit semantics and all labeled manuscript theorem certifications remain open.
