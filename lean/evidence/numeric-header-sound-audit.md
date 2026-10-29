# Numeric native header parser characterization

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NumericHeaderSound.lean` SHA-256 `b4492ba17e2b648f7c3dfc4166da7347b0f5679368a9b2cad46f87bc328d08f3`.

Lean 4.30.0 with locked dependencies: `lake build` passed (49 jobs), and the 126-declaration axiom audit passed. The numeric-byte gate-record parser returns a given byte list and body exactly when the full input equals the canonical encoded header followed by that body. The soundness direction uses `[propext, Quot.sound]`; the equivalence uses `[propext, Classical.choice, Quot.sound]`.

This characterizes the Lean numeric header parser, not its equivalence to Python byte/ASCII/JSON parsing, descriptor decoding, canonical gate-body replay, physical circuit semantics, or any labeled manuscript theorem.
