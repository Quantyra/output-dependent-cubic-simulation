# Second-phase derivative shift invariance

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/BooleanSource.lean` SHA-256 `debf9cbf950439c1e26a7bacd59cace7f960157a5038757b314438b3ad00ef25`.

`secondPhaseDerivative d j v` evaluates the actual represented second-phase ANF at `v` and `v XOR j` and takes their Boolean XOR. The proved declaration is:

```lean
theorem secondPhaseDerivative_shift_invariant {n : Nat} (d : CircuitDescriptor n)
    (j v : BinaryVector n) :
    secondPhaseDerivative d j (binaryShift j v) = secondPhaseDerivative d j v
```

With Lean 4.30.0 and the locked Mathlib manifest, `lake build` completed successfully (six jobs), `lake env lean Audit.lean` succeeded, and `tools/check_lean_audit.py` accepted the six transitive reports. This declaration depends on `Quot.sound` only, within the stated baseline.

The statement is unconditional in the descriptor and shift; it does not assume the desired invariance. It establishes only shift invariance of the represented second-phase derivative. Formal recovery of `j = J^-1 e`, the cubic-to-quadratic degree bound, Walsh support, circuit denotation and sector normalization remain open. No published manuscript theorem or Python refinement is claimed.
