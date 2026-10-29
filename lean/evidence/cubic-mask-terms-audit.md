# Constructed quadratic terms for a cubic mask derivative

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source is `lean/SectorSimulation/QuadraticTerms.lean` and `lean/SectorSimulation/CubicMaskDerivative.lean`; the exact file hashes are recorded in the repository manifest.

With Lean 4.30.0 and the locked Mathlib manifest, `lake build` passed (12 jobs). `lake env lean Audit.lean` and the 33-declaration axiom checker passed. The central elaborated statement is:

```lean
SectorSimulation.cubicMaskDerivativeTerms_correct {n : Nat} (m : Monomial n)
    (j : BinaryVector n) (hdegree : monomialDegree m ? 3) :
    ? terms, cubicMaskDerivativeTerms m j = some terms ?
      ? x, evalQuadraticTerms terms x =
        booleanDerivative (evalMonomial m) (binaryShift j) x
```

The term datatype has only constant, one-coordinate and two-coordinate constructors. The algorithm computes the selected support and returns the zero-, one-, two- or three-coordinate construction, explicitly returning `none` for larger supports. Its correctness proof derives the small support case from the actual mask degree, uses the proved mask-evaluation identities and coordinate derivative formulas, and supplies the computed term list. It does not assume an output decomposition or desired derivative equality. All cases include zero dimensions and arbitrary shift vectors. The central theorem reports `[propext, Quot.sound]`; its five supporting term-list/coordinate constructions report `[propext]`, all within the declared baseline.

This is a constructive theorem for one represented mask in an auxiliary quadratic term grammar. It does not yet translate those terms to the source's square-free bit-mask ANF, prove the output-mask degree bound or total cost, lift the construction across a whole phase list, recover the output shift from a native circuit, or establish Walsh/sector semantics. No published theorem label, Python implementation refinement or full manuscript certification is claimed.
