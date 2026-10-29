# Modeled source recognizer

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ModeledSourceRecognizer.lean` SHA-256 `f5e0edc06c68a9891dbe24683b4362bd5d807c470cc9caee5d7bd4285c7a41c6`.

The locked Lean 4.30.0 build passed (104 jobs); both declarations use `[propext, Classical.choice, Quot.sound]`. The executable Lean recognizer validates the numeric-byte JSON header, obtains a Gaussian row program, compiles the modeled body, and accepts only an exact match. Acceptance implies exact native replay agrees with the modeled body amplitudes and the previously proved output derivative and its bounds. Concrete evaluation checks a matching example, a modified-body rejection and invalid-header rejection; CI runs these examples.

This is soundness for the Lean recognizer, not a proof of Python recognizer/compiler correspondence or recognition completeness. Normalized Fourier and complex semantics, basis preparation, runtime, full costs and all labeled manuscript theorems remain open.
