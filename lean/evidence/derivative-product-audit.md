# Boolean finite-difference product and variable rules

Target bridge: the derivative degree-drop argument in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/DerivativeProduct.lean` SHA-256 `1bf9ac3a0f9c08bafccd8550d3ca5c76842a3c85766c7de7edb5f1026e3bcff4`.

With Lean 4.30.0 and the locked Mathlib manifest, `lake build` exited 0 (eight jobs). `lake env lean Audit.lean` exited 0; the 13-declaration `tools/check_lean_audit.py` check passed. The relevant elaborated types and axiom reports are:

```text
SectorSimulation.booleanDerivative_const {? : Type} (b : Bool) (shift : ? ? ?) (x : ?) :
  SectorSimulation.booleanDerivative (fun x => b) shift x = false
'SectorSimulation.booleanDerivative_const' does not depend on any axioms
SectorSimulation.booleanDerivative_and {? : Type} (f g : ? ? Bool) (shift : ? ? ?) (x : ?) :
  D(f AND g) = (Df AND g) XOR (f AND Dg) XOR (Df AND Dg)
'SectorSimulation.booleanDerivative_and' depends on axioms: [propext]
SectorSimulation.binaryVariable_derivative {? : Type} (j x : ? ? Bool) (i : ?) :
  SectorSimulation.booleanDerivative (fun v => v i) (SectorSimulation.binaryShift j) x = j i
'SectorSimulation.binaryVariable_derivative' depends on axioms: [propext]
```

The middle line abbreviates the printed pointwise Lean expression for readability; the full exact source type is in `DerivativeProduct.lean` and `Audit.lean` prints it. The cross term is essential for finite differences. Proofs use Boolean cases and simplification; all reported axioms are within the declared baseline.

These rules are components of the monomial derivative construction. They do not yet prove that an arbitrary represented cubic derivative has a quadratic ANF, establish source decoding or circuit semantics, or certify a paper theorem. A clean CI replay is pending for this increment.
