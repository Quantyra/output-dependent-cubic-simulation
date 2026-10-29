# Bit-mask monomial semantics

Target bridge: the Boolean ANF representation in sections 1?2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/BooleanSource.lean` SHA-256 `bc7e9ab5b3b2d465e2846fb3ceaf5b2894508ac35dfdc23e0cb0d5ae2e382e06`.

The locked Lean 4.30.0 project built successfully (nine jobs). `lake env lean Audit.lean` and the 21-declaration `tools/check_lean_audit.py` check passed. The elaborated types establish, for every dimension `n`, mask `m` and binary input `x`:

- `evalMonomial_eq_true_iff`: the evaluator is true if and only if `m i = true` implies `x i = true` for every index `i`.
- `evalMonomial_emptyMask`: the all-false mask evaluates to true.
- `evalMonomial_selectedVariables`: the evaluator equals the conjunction over the selected index list.
- `monomialDegree_eq_selectedLength`: the defined mask degree is the selected list's length.

The first three declarations report transitive axioms `[propext, Quot.sound]`; the last has no axiom dependencies. These are all within the stated trust baseline. The first attempt to prove the selected-list equality left Lean with an implication-versus-disjunction equivalence; the accepted proof uses explicit filter membership in both directions. The empty-mask and selected-list results include `n=0` without an extra assumption.

This is a semantic bridge for the represented bit-mask monomial; it does not yet construct the shifted derivative ANF, prove the general degree bound, or connect descriptor decoding and gate replay to circuit semantics. No published manuscript theorem is marked certified.
