# Clearing-program pivot-row invariant

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ClearProgramInvariant.lean` SHA-256 `054af9c04f4d87042780e300aa41d020e82abf52dd42c2ee225abb720011ed0f`.

Lean 4.30.0 with locked dependencies: `lake build` passed (33 jobs), and the 77-declaration axiom audit passed. By induction over the actual row-program interpreter, any sequence of row additions that never targets a fixed row preserves that row. Applying this to the generated clearing operations shows the full clearing list preserves every pivot-row entry. The general lemma uses `[propext]`; the generated-list theorem uses `[propext, Quot.sound]`.

This does not yet show that every other entry in the pivot column is cleared, preserve prior columns through subsequent steps, prove invertible-input completeness, establish operational cost, or certify a labeled manuscript theorem.
