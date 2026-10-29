# Quadratic and cubic monomial difference expansions

Target bridge: the cubic-to-quadratic derivative argument in section 2 of https://doi.org/10.5281/zenodo.23754698. Audited historical source at commit `360d265`, `lean/SectorSimulation/MonomialDifference.lean`, SHA-256 `a4c29be4dc0ad133c75cb43af07dfa3e52c16aaa0d60a1411b22ee4203e3c5ae`.

Under Lean 4.30.0 and the locked Mathlib manifest, `lake build` completed successfully (nine jobs). `lake env lean Audit.lean` and the 15-declaration axiom checker passed. The elaborated statements are pointwise Boolean identities. `quadratic_difference_expansion` has the three terms `ja*b XOR a*jb XOR ja*jb`; `cubic_difference_expansion` has seven terms `ja*b*c`, `a*jb*c`, `a*b*jc`, `ja*jb*c`, `ja*b*jc`, `a*jb*jc`, `ja*jb*jc`, combined by XOR. Both declarations report no axiom dependencies.

The proofs perform kernel-checked Boolean case analysis, without `native_decide` or `sorry`. These identities show the explicit lower-degree form at the level of up to three named Boolean variable values. They do **not** yet construct an ANF from arbitrary finite monomial masks, prove a degree bound for that construction, or derive the general cubic phase theorem. Source decoding, circuit semantics and all seven published theorem labels remain open.
