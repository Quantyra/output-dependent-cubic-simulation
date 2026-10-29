# Coordinate monomial derivatives

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Current source `lean/SectorSimulation/MonomialDifference.lean` SHA-256 `a31d7ebf86d0f3806d9da3e33b97b20e91cf560806591ac7c8043a51eeef4bc9`.

Under Lean 4.30.0 and the locked Mathlib manifest, `lake build` exited 0 (nine jobs). `lake env lean Audit.lean` and the 17-declaration `tools/check_lean_audit.py` check passed. The elaborated declarations are `SectorSimulation.quadraticVariable_derivative` and `SectorSimulation.cubicVariable_derivative`; both quantify over an arbitrary index type, all selected indices, input vectors and binary shifts, and both report no axiom dependencies.

The quadratic identity has three terms; the cubic identity has the seven terms stated in `MonomialDifference.lean`. The proof instantiates the previously checked pointwise identities directly, using definitional unfolding of the actual Boolean derivative and binary shift. It requires neither distinct indices nor a supplied decomposition.

This is a proof for explicit coordinate products, not yet a theorem for arbitrary bit-mask monomial evaluators. The construction of the output quadratic ANF, its degree bound, source decoder, native circuit semantics and all seven published theorem labels remain open. The first paper is unchanged; no full certification or Python refinement is claimed.
