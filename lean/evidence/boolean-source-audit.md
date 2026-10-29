# Finite Boolean source algebra: initial audit

Published target: https://doi.org/10.5281/zenodo.23754698, sections 1?2. Audited historical source at commit `6083a6a`, `lean/SectorSimulation/BooleanSource.lean`, SHA-256: `32dd458e013a9e4d75bd5dd291851a9275f6bf5d16e5eb2cb671e4cee6b6671b`.

The module defines finite Boolean vectors, monomial masks, lists of monomials, binary matrices, monomial and phase evaluators, monomial degree, a degree-bound check, matrix-vector application and descriptor fields. It retains constant/lower terms and evaluates duplicate masks by XOR. Symmetry, invertibility, parser/encoder equivalence, gate replay and circuit denotation are not yet formalized.

Under Lean 4.30.0 and the locked Mathlib manifest, `lake build` completed successfully with six jobs. `lake env lean Audit.lean` reported:

```text
SectorSimulation.evalPhase_empty {n : Nat} (x : SectorSimulation.BinaryVector n) :
  SectorSimulation.evalPhase [] x = false
'SectorSimulation.evalPhase_empty' does not depend on any axioms
SectorSimulation.evalPhase_duplicate_cancel {n : Nat} (m : SectorSimulation.Monomial n)
  (x : SectorSimulation.BinaryVector n) : SectorSimulation.evalPhase [m, m] x = false
'SectorSimulation.evalPhase_duplicate_cancel' depends on axioms: [propext]
```

The empty case is definitional; duplicate cancellation is proved by Boolean case analysis and simplification. `propext` is within the declared axiom baseline. The first proof script for duplicate cancellation did not rewrite the expression during its case split and failed; the committed proof uses the named case equation and was rebuilt successfully. Finite examples in `SourceExamples.lean` check a constant monomial, a selected variable and duplicate cancellation; they are supplementary. No published source-to-circuit or sector theorem is certified.
