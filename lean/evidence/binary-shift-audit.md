# Binary-vector derivative bridge: build and axiom audit

Target: the derivative-invariance step in section 2 of https://doi.org/10.5281/zenodo.23754698. The source `lean/SectorSimulation/BinaryShift.lean` SHA-256 is `9eb7cee9f4274575bf0addaabb4c0ba52f1f4c1cf56c83d9ef72124a27e3208b`.

Using Lean 4.30.0 and the core-only Lake project, `lake build` exited 0 and reported `Built SectorSimulation.BinaryShift (35s)`, `Built SectorSimulation (11s)`, and `Build completed successfully (5 jobs)`. `lake env lean Audit.lean` exited 0 and printed these elaborated types and transitive axioms:

```text
SectorSimulation.binaryShift_involutive {? : Type} (j x : ? ? Bool) :
  SectorSimulation.binaryShift j (SectorSimulation.binaryShift j x) = x
'SectorSimulation.binaryShift_involutive' depends on axioms: [Quot.sound]
SectorSimulation.binaryDerivative_shift_invariant {? : Type} (f : (? ? Bool) ? Bool) (j x : ? ? Bool) :
  SectorSimulation.booleanDerivative f (SectorSimulation.binaryShift j) (SectorSimulation.binaryShift j x) =
    SectorSimulation.booleanDerivative f (SectorSimulation.binaryShift j) x
'SectorSimulation.binaryDerivative_shift_invariant' depends on axioms: [Quot.sound]
```

The earlier general derivative helper still reports no axioms. `Quot.sound` is within the stated trusted baseline. The proofs use pointwise Boolean XOR and function extensionality; the statements do not assume the derivative-invariance conclusion. They do not yet instantiate the circuit, prove cubic degree reduction, establish Walsh support or certify Proposition 2.2. Python refinement and a clean-checkout replay remain open.
