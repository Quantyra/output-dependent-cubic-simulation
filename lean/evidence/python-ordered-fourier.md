# Python-order modeled Fourier and finite bridge checks

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698.
SHA-256 `lean/SectorSimulation/ModeledFourier.lean`: `60674b1ea7acc27e7d166f6e7e0fd77df1509c0ba0bcc06214a04c49484188b1`.
SHA-256 `lean/SectorSimulation/ExactNativeHeader.lean`: `349a011cd8cd39da63bb96fd5cd65ec0df3c7ab8c95e5cdd304ed3094aa70554`.
SHA-256 `lean/SectorSimulation/ValidatedHeaderReplay.lean`: `f5db5fec326318158f580e9482b69e8269cd7b489b34e0e44f39d62b953c32ca`.
SHA-256 `lean/SectorSimulation/ModeledSourceRecognizer.lean`: `f5e0edc06c68a9891dbe24683b4362bd5d807c470cc9caee5d7bd4285c7a41c6`.
SHA-256 `lean/SectorSimulation/ModeledRecognizerCompleteness.lean`: `44e62a85a6d35a258d9e78c1a4437f8719cec6754e16293b0a4e9343f4df27e5`.
SHA-256 `tools/check_python_lean_bridge.py`: `246a253c0cdc462a258f369afa5191534007a82fbdd45e9abf63a8694c210211`.

The modeled source compiler emits Gaussian CNOT records before all-wire Hadamards, matching the Python compiler ordering; its modeled state semantics and replay/congruence proofs were rebuilt accordingly. The earlier separately named Hadamard-first decomposition remains a distinct result. The locked Lean 4.30.0 build passed (105 jobs), the exact helper axiom audit passed, and the existing modeled-recognizer examples passed.

Five Python-compiled two-phase cases were accepted by the Lean recognizer, including identity and swap pairings, constant and cubic terms, nonzero output, and Python cancellation and sorting of duplicate input masks. The regression script checks exact generated gate lists; finite examples do not establish general Python normalization, serialization, Gaussian ordering or compiler/recognizer equivalence. Fourier kernel and complex semantics, basis preparation, full costs and all manuscript theorem labels remain open.
