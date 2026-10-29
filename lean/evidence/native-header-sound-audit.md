# Native header bit parser soundness

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NativeHeaderSound.lean` SHA-256 `d3b3be8ae7ffd6bdcc4fabcbd0be2c84113c780434cb2ce4c9f5e376ea711933`.

Lean 4.30.0 with locked dependencies: `lake build` passed (44 jobs), and the 111-declaration axiom audit passed. Whenever the abstract bit-record parser accepts, the complete input is exactly the canonical doubled-X/Z bit encoding, doubled-H terminator and returned body. Combined with the previous round trip, this gives both directions for the abstract prefix grammar. The theorem uses `[propext]`.

This is not yet a proof for full native gate records, ASCII/JSON decoding, canonical body replay, physical circuit semantics, or any labeled manuscript theorem.
