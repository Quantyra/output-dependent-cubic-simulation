# Source descriptor phase compilation

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/SourcePhaseCompiler.lean` SHA-256 `05763de8692aa90963159b467ae1bcfc95d6589093aee80f83daf978e9223ba7`.

The locked Lean 4.30.0 build passed (98 jobs). Descriptor nonzero and degree-check soundness use `[propext, Quot.sound]`; absence of zero-wire descriptors uses no axioms; phase compilation uses `[propext, Classical.choice, Quot.sound]`. Every modeled descriptor contains a measured output index and therefore has at least one wire. If both phases pass the cubic degree check, the executable Lean compiler produces correct native records for each phase separately on any represented state, each with at most 17 records per input monomial.

The two phases are checked separately on the same input state, not as a complete circuit. This result does not settle global-phase semantics for a hypothetical zero-wire circuit outside the descriptor type. Python correspondence, complex embedding, intervening circuit operations, runtime, full cost and all labeled manuscript theorems remain open.
