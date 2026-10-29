# Auxiliary derivative lemma: core build and axiom audit

Paper target: https://doi.org/10.5281/zenodo.23754698, Proposition 2.2, derivative-invariance bridge only. Source: `lean/SectorSimulation/Derivative.lean` at commit `44323c77db4cb9a976bd18f06068ab5dd9863643`. The helper is quantified over any type, Boolean-valued function, involutive shift and input. It states that the Boolean derivative is invariant under the shift.

Environment: Lean 4.30.0 (`d024af099ca4bf2c86f649261ebf59565dc8c622`), Lake 5.0.0, Windows x86_64. The initial Lake manifest has no Mathlib dependency. The selected Mathlib revision is a separate outstanding target-freeze obligation.

From `lean/`, `lake build` returned exit 0. Its output reported `Built SectorSimulation.Derivative (341s)`, `Built SectorSimulation (14s)`, and `Build completed successfully (4 jobs)`. A further `lake env lean SectorSimulation/Derivative.lean` returned exit 0. Running `lake env lean Audit.lean` returned exit 0 and printed the elaborated declaration:

```text
SectorSimulation.booleanDerivative_shift_invariant {? : Type} (f : ? ? Bool) (shift : ? ? ?)
  (involutive : ? (x : ?), shift (shift x) = x) (x : ?) :
  SectorSimulation.booleanDerivative f shift (shift x) = SectorSimulation.booleanDerivative f shift x
'SectorSimulation.booleanDerivative_shift_invariant' does not depend on any axioms
```

The source defines the derivative as `Bool.xor (f x) (f (shift x))`; the proof unfolds it, rewrites using involutivity, and checks the four Boolean cases. This discharges only this explicitly scoped helper. It does not establish the source semantics, Walsh support, Clifford/sector identities, control discovery, estimator, operational costs or any published theorem. A clean-checkout replay and eventual Mathlib dependency audit remain open.
