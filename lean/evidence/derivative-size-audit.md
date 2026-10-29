# Cubic derivative output size

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/DerivativeSize.lean` SHA-256 `c736a208ce660ead3dc6e3e80da0fa9cc23cb2adfabea41e68075ce44b11edbe`.

Lean 4.30.0 with locked dependencies: `lake build` passed (23 jobs), and the 47-declaration axiom audit passed. The actual one-mask constructor emits at most seven auxiliary terms; the phase constructor emits at most seven times the input mask count; and the mapped source ANF has the same bound. The statements apply to every successful return and use `[propext, Quot.sound]`. The separately proved correctness theorem supplies success for cubic phases.

This is an output-count bound, not a runtime, bit-cost, circuit-decoding, or full manuscript theorem proof.
