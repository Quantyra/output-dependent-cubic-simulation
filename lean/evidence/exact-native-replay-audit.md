# Exact native gate replay and quadratic phase

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactNativeReplay.lean` SHA-256 `e72dac36c42093a921ed085d58c71259ce8b8d0b67a7faf7f29e6e088b38f11b`.

Lean 4.30.0 locked project build passed (73 jobs); `ExactNativeExamples.lean` checked rejection of invalid wires, duplicate CNOT wires and unknown tags, and acceptance of valid HH. Exact axiom sets are in `CLAIMS.json`, within the permitted baseline. The modeled interpreter executes H, X, Z, T, TDG and distinct-wire CX records on shared-denominator states; literal H-CX-H replay yields the exact controlled-sign quotient amplitude.

T/TDG correctness and full Toffoli decomposition replay, complex embedding, representation independence, norm preservation, Python equivalence, full circuit, cost and all labeled manuscript theorems remain open.
