# Numeric byte header round trip

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NumericHeaderBytes.lean` SHA-256 `b5dc5778f111de6a3d2b2c2d9831962e9083332742d16eff98a7da5a51389e86`.

Lean 4.30.0 with locked dependencies: `lake build` passed (48 jobs), the 124-declaration axiom audit passed, and source examples for byte values 65 and 255 passed. The eight Boolean fields and numbers below 256 are mutually inverse using most-significant-bit-first weights; the full numeric-byte header encoding decodes to the original byte list and body. The finite 256-value proof uses kernel `decide`, not native evaluation. The byte bound has no axioms, the byte round trips use `[propext]`, and the composed header theorem uses `[propext, Classical.choice, Quot.sound]`.

Numeric parser soundness for arbitrary accepted inputs, Python byte/ASCII/JSON equivalence, descriptor decoding, body replay, physical gate semantics and all labeled manuscript theorem certifications remain open.
