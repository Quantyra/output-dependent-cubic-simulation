# Evaluating cubic-mask support shapes

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Current `lean/SectorSimulation/SupportShapes.lean` SHA-256 `ed03fc89913d497557f7200740eecfc41034ae34402fb4e9fdebf3b9dff8326f`.

The locked Lean 4.30.0 project built successfully with ten jobs. `lake env lean Audit.lean` succeeded, and the 27-declaration axiom checker passed. The four elaborated declarations `evalMonomial_selected_nil`, `evalMonomial_selected_one`, `evalMonomial_selected_two`, and `evalMonomial_selected_three` establish the exact values for zero-, one-, two- and three-index selected supports, respectively. Each reports `[propext, Quot.sound]`, both in the declared trust baseline.

The proofs rewrite the actual bit-mask evaluator to the previously checked selected-index list and then evaluate the list conjunction. They apply to arbitrary finite dimensions and the explicitly stated support equalities. The earlier shape-extraction theorem provides such a case for each mask with degree at most three.

These results connect the represented mask evaluator to the coordinate-product identities, but do not yet assemble their derivative into a concrete output ANF or prove its degree bound. Source decoding, native circuit denotation, Walsh/sector identities and all seven manuscript theorem labels remain open.
