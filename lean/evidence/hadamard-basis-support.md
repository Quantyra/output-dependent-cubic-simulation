# Multi-wire Hadamard basis support

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardBasisSupport.lean` SHA-256 `17895e04f03ff993bc05fe6e429e81de1ea2a8d843b05a024dfa70c45003519a`.

The locked Lean 4.30.0 build passed (124 jobs); all four declarations use `[propext, Classical.choice, Quot.sound]`. A Hadamard step vanishes if both inputs in its two-point fiber vanish. For any wire list, including repeated or empty lists, the exact kernel preserves a zero condition on every untouched bit. Therefore a point-supported basis input has zero output when any untouched output bit differs, and every nonzero output agrees on all untouched bits.

This establishes a necessary support condition, not nonzero amplitudes, sign products, closed Walsh sums, complex embedding, Python correspondence, sector identities, costs or any labeled paper theorem.
