# Exact native header and source-body composition

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactNativeHeader.lean` SHA-256 `349a011cd8cd39da63bb96fd5cd65ec0df3c7ab8c95e5cdd304ed3094aa70554`.

The locked Lean 4.30.0 build passed (102 jobs). X squared, Z squared and the exact header identity use `[propext, Quot.sound]`; the other three declarations use `[propext, Classical.choice, Quot.sound]`. For any bit-list header and an existing wire zero, exact native replay preserves all amplitudes. With degree-checked phases and a successful Gaussian row program, appending the compiled modeled source body produces its modeled output amplitudes.

This uses Lean's bit-list header and does not yet establish correspondence with actual descriptor bytes or the Python implementation. Normalized Fourier and complex semantics, basis preparation, runtime, full costs and all labeled manuscript theorems remain open.
