# JSON value construction and extraction

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/DescriptorJsonEncode.lean` SHA-256 `9273a944ad836bf0b921ed3b5c4bccb235207914a9ae618e5935ffe8fd7d078b`.

The locked Lean 4.30.0 build passed (106 jobs). All six declarations have transitive axioms `[propext, Classical.choice, Quot.sound]`. Lean constructs a JSON value for every raw two-phase descriptor and proves that the existing extractor recovers it. Given bytes decoding to text that parses to that value, and successful raw validation, it proves an accepted modeled body exists.

This does not construct or verify JSON text or ASCII bytes, prove Python serialization or compiler correspondence, establish Fourier kernel or complex semantics, or certify a manuscript theorem.
