# Preservation of an earlier unit column

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PriorColumnInvariant.lean` SHA-256 `ea005543fdd2c1f2c74d98bed854294b12beb6d6527d2947ab07876dab1a333c`.

Lean 4.30.0 with locked dependencies: `lake build` passed (35 jobs), and the 84-declaration axiom audit passed. If an earlier column is a unit column, a later successful pivot search followed by the actual swap and generated clearing program preserves every entry of that earlier column. The theorem uses `[propext, Quot.sound]`; helper axioms are recorded in the audit.

This is a single-step invariant, not a full pivot-sequence induction, proof of pivot existence, elimination completeness, runtime, native circuit semantics or a labeled manuscript theorem.
