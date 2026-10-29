# Native header eight-bit framing

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NativeHeaderBytes.lean` SHA-256 `f4c9ec184eb9eeffde042e45c1e657c63c99ce00b23a262763df4f0b4804ec19`.

Lean 4.30.0 with locked dependencies: `lake build` passed (46 jobs), the 117-declaration axiom audit passed, and source examples passed an eight-bit header with body retention and a one-bit incomplete-header rejection. The model groups bit fields in b7-to-b0 order and composes their round trip with the full gate-record parser. The byte-field round trip and conditional incomplete rejection use `[propext]`; the composed header round trip uses `[propext, Classical.choice, Quot.sound]`.

This is an eight-Boolean-field representation, not yet a numeric-byte or Python ASCII/JSON equivalence proof. Accepted-input byte-parser soundness, native descriptor decoding, canonical body replay, physical gate semantics and all labeled manuscript theorem certifications remain open.
