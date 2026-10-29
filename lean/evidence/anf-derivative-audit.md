# ANF fold and derivative distribution

Target bridge: Boolean phase representation and derivative in sections 1?2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/BooleanSource.lean` SHA-256 `8343bb46249fdeba26a7e853c2ff4afc335e5dd6936970599fe2b73162e44b11`.

The locked Lean 4.30.0 project built successfully (seven jobs). `lake env lean Audit.lean` and `tools/check_lean_audit.py` passed. The elaborated statements and transitive axiom reports are:

```text
SectorSimulation.phaseFold_from {n : Nat} (p : PhaseANF n) (x : BinaryVector n)
  (initial : Bool) : p.foldl (fun acc m => acc ^^ evalMonomial m x) initial =
    (initial ^^ evalPhase p x)
'SectorSimulation.phaseFold_from' depends on axioms: [propext]
SectorSimulation.evalPhase_append {n : Nat} (p q : PhaseANF n) (x : BinaryVector n) :
  evalPhase (p ++ q) x = (evalPhase p x ^^ evalPhase q x)
'SectorSimulation.evalPhase_append' depends on axioms: [propext, Quot.sound]
SectorSimulation.phaseDerivative_append {n : Nat} (p q : PhaseANF n)
  (shift : BinaryVector n ? BinaryVector n) (x : BinaryVector n) :
  booleanDerivative (evalPhase (p ++ q)) shift x =
    (booleanDerivative (evalPhase p) shift x ^^ booleanDerivative (evalPhase q) shift x)
'SectorSimulation.phaseDerivative_append' depends on axioms: [propext, Quot.sound]
```

The fold proof uses induction on the finite phase list and Boolean cases; its first induction rewrite attempt failed and was corrected to instantiate both induction hypotheses explicitly. The derivative result uses the proved ANF append identity and the independently checked function-level derivative additivity. All reported axioms lie in the declared trust baseline.

These declarations connect the actual represented ANF fold to derivative additivity. They do not yet construct the derivative of each monomial or establish the cubic-to-quadratic degree bound; native descriptor decoding, computed `J^-1 e`, circuit and Walsh/sector semantics remain open. No manuscript theorem or Python refinement is certified.
