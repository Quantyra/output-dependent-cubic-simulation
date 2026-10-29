# Source output derivative reference construction

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/SourceOutputDerivative.lean` SHA-256 `45255c3829cc35af24fe7f019272eee0f0e2d139c6821962f47ea51a73e31e67`.

Lean 4.30.0 with locked dependencies: `lake build` passed (26 jobs), and the 55-declaration axiom audit passed. For a descriptor with cubic phases and a surjective matrix evaluator, the explicit construction returns a shift solving `Jj=e` for the descriptor's output index and a bit-mask ANF of degree at most two and length at most seven times the second-phase input length, evaluating to its derivative. The theorem uses `[propext, Classical.choice, Quot.sound]`.

Surjectivity is an explicit hypothesis, not a proved validation procedure. The shift is found by exponential exhaustive search, not the paper's efficient elimination. Native decoding, physical output identity, Walsh/sector arguments and all labeled manuscript theorem certifications remain open.
