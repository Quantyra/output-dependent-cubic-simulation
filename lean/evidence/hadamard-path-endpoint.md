# Selected Hadamard path endpoint

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardPathEndpoint.lean` SHA-256 `57c2f2cb79299b44808f089dc8b52fc16f37975d42bdcfdbb949cddeecb5a634`.

The locked Lean 4.30.0 build passed (127 jobs); six declarations have exact transitive axioms in the project audit baseline. Lean separates the selected-path endpoint from its exact coefficient and proves each processed bit equals the requested output while each untouched bit retains the input. The all-wire selected path always reaches the output, including at width zero. The exact all-wire Hadamard kernel is therefore the binary-basis sum of the recursive selected-path coefficients, with no endpoint equality test.

The recursive coefficients are not yet simplified to the closed Walsh dot-product sign and normalization. Complex embedding, Python correspondence, sector identities, costs and all paper theorem labels remain open.
