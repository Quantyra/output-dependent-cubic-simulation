# ASCII descriptor header construction

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/AsciiDescriptorEncode.lean` SHA-256 `3542023d903d8526225292a704ca800fd5e9aa565a53ca96d3e9eeb633c4ada4`.

The locked Lean 4.30.0 build passed (107 jobs). The ASCII round-trip theorem uses `[propext, Quot.sound]`; the conditional recognizer theorem uses `[propext, Classical.choice, Quot.sound]`. For every list of bounded ASCII characters, constructed bytes decode to the corresponding text; if that text parses to the constructed descriptor JSON and the raw descriptor validates, an accepted modeled body exists.

This does not construct the descriptor JSON text or prove the parser accepts it, prove Python serialization or compiler correspondence, establish Fourier kernel or complex semantics, or certify a manuscript theorem.
