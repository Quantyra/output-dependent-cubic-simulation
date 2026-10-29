# Constructed quadratic terms for a whole cubic phase derivative

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CubicPhaseDerivative.lean` SHA-256 `3c18d8cbe1f6418919deb82c50e015f7318cfade46df1366999202384cfaad7f`.

Under Lean 4.30.0 and the locked Mathlib manifest, `lake build` completed successfully (13 jobs). `lake env lean Audit.lean` and the 34-declaration axiom checker passed. The central elaborated declaration is:

```lean
SectorSimulation.cubicPhaseDerivativeTerms_correct {n : Nat} (p : PhaseANF n)
    (j : BinaryVector n) (hdegree : phaseWithinDegree 3 p = true) :
    ? terms, cubicPhaseDerivativeTerms p j = some terms ?
      ? x, evalQuadraticTerms terms x =
        booleanDerivative (evalPhase p) (binaryShift j) x
```

It depends on `[propext, Quot.sound]`, within the stated baseline. The algorithm traverses the actual ANF list; each mask is processed by the already proved source-derived support-case constructor and the resulting constant/linear/product lists are concatenated. The proof inducts over the phase list, extracts each degree bound, invokes the one-mask construction, and uses ANF and derivative additivity. It covers empty phases, zero dimensions, arbitrary lower terms and arbitrary binary shifts. No supplied quadratic decomposition or desired evaluation equality is assumed.

This proves a constructive whole-phase result in the **auxiliary quadratic term grammar**. It does not yet translate those terms into the paper's square-free bit-mask ANF or establish that output encoding's degree and resource bounds. The native decoder, computation of `j = J^-1 e`, circuit denotation, Walsh support and normalized-sector theorems remain open. It is a significant bridge for the derivative claim, not certification of any of the seven labeled manuscript theorems or the Python implementation.
