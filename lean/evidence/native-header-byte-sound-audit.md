# Native byte-field header parser soundness

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NativeHeaderBytesSound.lean` SHA-256 `bfc58f5bdaa468e12c97447f6e8f44c7f18079a8b57ce9bc7154ed5af86f6085`.

Lean 4.30.0 with locked dependencies: `lake build` passed (47 jobs), and the 120-declaration axiom audit passed. Every accepted byte-field parse reconstructs its exact input bits; every accepted gate-record byte header reconstructs its exact canonical header and returned body; and accepted bits have length exactly eight times the byte count. The first two declarations use `[propext]`, the length result `[propext, Quot.sound]`.

The fields are not yet related to numeric bytes, Python ASCII/JSON, descriptor decoding, canonical body replay or gate denotation. No labeled manuscript theorem is certified.
