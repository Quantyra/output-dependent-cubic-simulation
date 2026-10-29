# Native gate-record header parser

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NativeGateHeader.lean` SHA-256 `c339ac0c244aa13233fad75485643d8bb6359952c372c5715e9299cc5d9e49ae`.

Lean 4.30.0 with locked dependencies: `lake build` passed (45 jobs), the 114-declaration axiom audit passed, and source examples passed for body preservation, nonzero-wire rejection and mismatched pairs. Gate records carry tag strings and complete wire lists. The parser and encoder satisfy both round-trip and accepted-prefix reconstruction, with exact record count. The round trip uses `[propext, Classical.choice, Quot.sound]`; the length and soundness theorems use `[propext]`.

This does not yet prove equivalence to Python tuple parsing, byte alignment or ASCII/JSON serialization, descriptor decoding, canonical body replay, gate denotation or any labeled manuscript theorem.
