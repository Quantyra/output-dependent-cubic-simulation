# Constructed cubic phase derivative as quadratic bit-mask ANF

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CubicDerivativeANF.lean` SHA-256 `6c9d06256df3dfd7f69ea7d02b4b6eb42cc2c094d5e4468456264f9586ee7b73`.

Lean 4.30.0 with locked dependencies: `lake build` passed (22 jobs), and the 44-declaration axiom audit passed. For every represented phase with mask degree at most three and any binary shift, `cubicPhaseDerivativeANF_correct` proves the explicit source-derived constructor returns a bit-mask phase of degree at most two whose value at every input equals the Boolean derivative. It composes the actual term constructor, semantic translation, and degree proof; no derivative representation is assumed. It includes repeated coordinates, zero dimensions, and arbitrary lower-degree terms. Each new declaration depends on `[propext, Classical.choice, Quot.sound]`, within the baseline.

This source representation result does not establish the constructor's cost, the native decoder or output shift, physical circuit semantics, Walsh/sector identities, or any complete labeled manuscript theorem.
