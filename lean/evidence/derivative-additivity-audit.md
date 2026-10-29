# Boolean derivative additivity

Target bridge: the quadratic derivative construction in section 2 of https://doi.org/10.5281/zenodo.23754698. The source `lean/SectorSimulation/DerivativeLinear.lean` has SHA-256 `a9e9088bb11d2d18541a525e9bae99b13f4cc26a47f9c0564a6c8d180da63451`.

The declaration states, for every type, Boolean functions `f` and `g`, shift and input, that differentiating their pointwise XOR yields the XOR of their derivatives. The proof unfolds the derivative and checks all Boolean cases; it has no hypotheses asserting the conclusion.

Under Lean 4.30.0 and the locked Mathlib manifest, `lake build` exited 0 with seven jobs. `lake env lean Audit.lean` exited 0, and the elaborated type and `#print axioms` reported:

```text
SectorSimulation.booleanDerivative_xor {? : Type} (f g : ? ? Bool) (shift : ? ? ?) (x : ?) :
  SectorSimulation.booleanDerivative (fun y => f y ^^ g y) shift x =
    (SectorSimulation.booleanDerivative f shift x ^^ SectorSimulation.booleanDerivative g shift x)
'SectorSimulation.booleanDerivative_xor' depends on axioms: [propext]
```

The seven-declaration `tools/check_lean_audit.py` check passed. `propext` is in the allowed baseline. This general additivity lemma is not the ANF degree-drop theorem: the representation fold, differentiated monomial construction, cubic degree bound and source-to-circuit connection remain open. No manuscript theorem is marked certified.
