# Native header bit-level round trip

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NativeHeaderBits.lean` SHA-256 `ba79af783785f0523433feda65ba4fa0d1a062527337e3e5028b7ee9a4358243`.

Lean 4.30.0 with locked dependencies: `lake build` passed (43 jobs), the 110-declaration axiom audit passed, and source examples passed valid, mismatched-pair and missing-terminator checks. For abstract wire-zero header tags, encoding a bit as doubled X or Z and terminating with doubled H decodes to the original bits and untouched following body; its length is `2 * bits.length + 2`. Both theorems use `[propext]`.

The tag abstraction is not yet the complete native gate grammar or a proof of Python equivalence. ASCII/JSON decoding, byte alignment, canonical body replay, gate denotation and all labeled manuscript theorem certifications remain open.
